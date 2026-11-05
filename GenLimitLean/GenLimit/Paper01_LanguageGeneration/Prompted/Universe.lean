import GenLimit.Paper01_LanguageGeneration.Prompted.Strings

/-!
# P01 prompted generation in an arbitrary enumerable string universe

The universe need not contain every word. `word` reads the string represented
by a universe element; for an ambient set `U : Set (List A)`, use subtype
inclusion. All membership queries stay inside the supplied universe and use
its explicit enumeration. No decidability of the ambient set is required.
The list-universe robustness definition is recovered by `robustPromptIn_id_iff`.
-/

namespace GenLimit.KM.Prompted

open GenLimit.KM.Transport

variable {A U : Type*}

/-- Source robustness inside the supplied string universe. `word` may in
particular be the inclusion of an arbitrary set of strings. -/
def RobustPromptIn (word : U → List A) (O : IndexedOracleFamily U) (p : List A) : Prop :=
  ∀ i n, ∃ x, x ∈ O.language i ∧
    ∃ c : List A, n ≤ c.length ∧ word x = p ++ c

/-- Compatibility with the full-word-universe interface. -/
theorem robustPromptIn_id_iff (O : IndexedOracleFamily (List A)) (p : List A) :
    RobustPromptIn id O p ↔ RobustPrompt O p := by
  constructor
  · intro h i n
    obtain ⟨x, hx, c, hc, he⟩ := h i n
    exact ⟨c, hc, he ▸ hx⟩
  · intro h i n
    obtain ⟨c, hc, hmem⟩ := h i n
    exact ⟨p ++ c, hmem, c, hc, rfl⟩

variable [DecidableEq A]

def encodedMatchesIn (word : U → List A) (e : U ≃ ℕ) (p : List A) (x : ℕ) : Bool :=
  decide (p <+: word (e.symm x))

theorem encoded_robust_in (word : U → List A) (e : U ≃ ℕ)
    (O : IndexedOracleFamily U) {p : List A} (hp : RobustPromptIn word O p) :
    Robust (encodeFamily e O) (encodedMatchesIn word e) p := by
  intro i hfinite
  obtain ⟨B, hB⟩ := (hfinite.image (fun x => (word (e.symm x)).length)).bddAbove
  obtain ⟨x, hx, c, hc, hword⟩ := hp i (B + 1)
  have hxenc : e x ∈ {n | n ∈ (encodeFamily e O).language i ∧
      encodedMatchesIn word e p n = true} := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    simp only [encodedMatchesIn, e.symm_apply_apply, hword, decide_eq_true_eq]
    exact ⟨c, rfl⟩
  have hlength := hB ⟨e x, hxenc, rfl⟩
  simp only [e.symm_apply_apply, hword, List.length_append] at hlength
  omega

/-- The Appendix A.5 machine transported to the supplied universe. -/
def generatorIn (word : U → List A) (e : U ≃ ℕ) (O : IndexedOracleFamily U)
    (stream : ℕ → U) (prompts : ℕ → List A)
    (hrob : ∀ t, RobustPromptIn word O (prompts t)) (t : ℕ) : U :=
  e.symm (generator (encodeFamily e O) (encodedMatchesIn word e)
    (Support.renameStream e stream) prompts (fun t => encoded_robust_in word e O (hrob t)) t)

/-- NeurIPS Theorem 7.1 for an arbitrary explicitly enumerable string
universe, with a threshold uniform over every robust prompt sequence. -/
theorem theorem_7_1_in_universe [DecidableEq U]
    (word : U → List A) (e : U ≃ ℕ) (O : IndexedOracleFamily U)
    {stream : ℕ → U} {z : ℕ}
    (hP : Generic.Presents stream (O.language z)) :
    ∃ T, ∀ (prompts : ℕ → List A) (hrob : ∀ t, RobustPromptIn word O (prompts t)),
      ∀ t, T ≤ t →
        prompts t <+: word (generatorIn word e O stream prompts hrob t) ∧
        generatorIn word e O stream prompts hrob t ∈ O.language z ∧
        generatorIn word e O stream prompts hrob t ∉ Generic.sample stream t := by
  have hPnat : Presents (Support.renameStream e stream) ((encodeFamily e O).language z) :=
    Support.presents_renameStream e hP
  obtain ⟨T, hT⟩ :=
    eventual_correctness_uniform (encodeFamily e O) (encodedMatchesIn word e) hPnat
  refine ⟨T, ?_⟩
  intro prompts hrob t ht
  have hmain := hT prompts (fun t => encoded_robust_in word e O (hrob t)) t ht
  refine ⟨?_, ?_, ?_⟩
  · simpa only [encodedMatchesIn, decide_eq_true_eq] using hmain.1
  · rcases hmain.2.1 with ⟨w, hw, he⟩
    change e.symm _ ∈ O.language z
    rw [← he, e.symm_apply_apply]
    exact hw
  · intro hseen
    apply hmain.2.2
    have hencoded := (mem_encoded_sample_iff e stream t _).2 hseen
    simpa only [generatorIn, e.apply_symm_apply] using hencoded

end GenLimit.KM.Prompted
