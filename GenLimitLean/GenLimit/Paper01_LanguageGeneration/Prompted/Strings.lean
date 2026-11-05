import GenLimit.Paper01_LanguageGeneration.Prompted.FiniteQuery
import GenLimit.Paper01_LanguageGeneration.Transport
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.List.Infix

/-!
# P01 Theorem 7.1: robust string prompts

Words are finite lists of alphabet symbols; concatenation is list append and
prompt extension is `List.IsPrefix`. The source definition of robustness uses
arbitrarily long continuations in every language, not merely a continuation
in the hidden target. It implies the infinitude required by the finite-query
machine over any alphabet. Over a finite alphabet the two conditions agree.

An explicit enumeration `List A ≃ ℕ` transports the concrete Appendix A.5
algorithm. Queries decode a word and invoke the supplied membership oracle;
prefix testing is decidable. The abstract countable-alphabet wrapper chooses
the enumeration classically. No runtime or numerical query bound is asserted.
-/

namespace GenLimit.KM.Prompted

open GenLimit.KM.Transport

variable {A : Type*}

/-- Section 7 robustness: every candidate admits arbitrarily long
continuations of this prompt. -/
def RobustPrompt (O : IndexedOracleFamily (List A)) (p : List A) : Prop :=
  ∀ i n, ∃ c : List A, n ≤ c.length ∧ p ++ c ∈ O.language i

/-- The matching portion of one candidate language. -/
def matchingLanguage (O : IndexedOracleFamily (List A)) (p : List A) (i : ℕ) :
    Set (List A) :=
  {w | w ∈ O.language i ∧ p <+: w}

theorem matchingLanguage_infinite
    (O : IndexedOracleFamily (List A)) {p : List A}
    (hp : RobustPrompt O p) (i : ℕ) :
    (matchingLanguage O p i).Infinite := by
  intro hfinite
  obtain ⟨B, hB⟩ := (hfinite.image List.length).bddAbove
  obtain ⟨c, hc, hmem⟩ := hp i (B + 1)
  have hlength : (p ++ c).length ≤ B :=
    hB ⟨p ++ c, ⟨hmem, ⟨c, rfl⟩⟩, rfl⟩
  simp only [List.length_append] at hlength
  omega

/-- Over a finite alphabet, infinitely many matching strings are precisely
the source's arbitrarily long continuations condition. -/
theorem robustPrompt_iff_infinite [Finite A]
    (O : IndexedOracleFamily (List A)) (p : List A) :
    RobustPrompt O p ↔ ∀ i, (matchingLanguage O p i).Infinite := by
  refine ⟨fun hp i => matchingLanguage_infinite O hp i, ?_⟩
  intro h i n
  obtain ⟨w, hw, hlong⟩ := (h i).exists_notMem_finite
    (List.finite_length_le A (p.length + n))
  obtain ⟨c, rfl⟩ := hw.2
  refine ⟨c, ?_, hw.1⟩
  change ¬ (p ++ c).length ≤ p.length + n at hlong
  simp only [List.length_append] at hlong
  omega

/-- Every infinite language over a finite alphabet admits arbitrarily long
words, so the empty prompt is robust. -/
theorem robustPrompt_nil [Finite A] (O : IndexedOracleFamily (List A)) :
    RobustPrompt O [] := by
  apply (robustPrompt_iff_infinite O []).2
  intro i
  simpa only [matchingLanguage, List.nil_prefix, and_true] using O.infinite' i

variable [DecidableEq A]

/-- Executable prefix test after decoding a universe index. -/
def encodedMatches (e : List A ≃ ℕ) (p : List A) (x : ℕ) : Bool :=
  decide (p <+: e.symm x)

theorem encoded_robust (e : List A ≃ ℕ)
    (O : IndexedOracleFamily (List A)) {p : List A} (hp : RobustPrompt O p) :
    Robust (encodeFamily e O) (encodedMatches e) p := by
  intro i
  apply ((matchingLanguage_infinite O hp i).image
    (Set.injOn_of_injective e.injective)).mono
  rintro _ ⟨w, hw, rfl⟩
  constructor
  · exact ⟨w, hw.1, rfl⟩
  · simpa [encodedMatches] using hw.2

/-- The actual Appendix A.5 generator on strings, relative to the supplied
universe coding and membership oracle. Robustness is only a termination
certificate; neither the target index nor the convergence time is an input. -/
def generatorOfEquiv (e : List A ≃ ℕ) (O : IndexedOracleFamily (List A))
    (stream : ℕ → List A) (prompts : ℕ → List A)
    (hrob : ∀ t, RobustPrompt O (prompts t)) (t : ℕ) : List A :=
  e.symm (generator (encodeFamily e O) (encodedMatches e)
    (Support.renameStream e stream) prompts (fun t => encoded_robust e O (hrob t)) t)

/-- The prompted generation-in-the-limit conclusion from Section 7. -/
def GeneratesInLimit (e : List A ≃ ℕ) (O : IndexedOracleFamily (List A))
    (stream : ℕ → List A) (prompts : ℕ → List A)
    (hrob : ∀ t, RobustPrompt O (prompts t)) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    prompts t <+: generatorOfEquiv e O stream prompts hrob t ∧
      generatorOfEquiv e O stream prompts hrob t ∈ O.language z ∧
      generatorOfEquiv e O stream prompts hrob t ∉ Generic.sample stream t

/-- Appendix (A.2) on strings. The same threshold works for every robust
prompt sequence, including adversarially changing prompts. -/
theorem theorem_7_1_uniform (e : List A ≃ ℕ) (O : IndexedOracleFamily (List A))
    {stream : ℕ → List A} {z : ℕ}
    (hP : Generic.Presents stream (O.language z)) :
    ∃ T, ∀ (prompts : ℕ → List A) (hrob : ∀ t, RobustPrompt O (prompts t)),
      ∀ t, T ≤ t →
        prompts t <+: generatorOfEquiv e O stream prompts hrob t ∧
        generatorOfEquiv e O stream prompts hrob t ∈ O.language z ∧
        generatorOfEquiv e O stream prompts hrob t ∉ Generic.sample stream t := by
  have hPnat : Presents (Support.renameStream e stream) ((encodeFamily e O).language z) :=
    Support.presents_renameStream e hP
  obtain ⟨T, hT⟩ := eventual_correctness_uniform (encodeFamily e O) (encodedMatches e) hPnat
  refine ⟨T, ?_⟩
  intro prompts hrob t ht
  have hmain := hT prompts (fun t => encoded_robust e O (hrob t)) t ht
  refine ⟨?_, ?_, ?_⟩
  · simpa only [encodedMatches, decide_eq_true_eq] using hmain.1
  · have hmem := hmain.2.1
    change _ ∈ Support.renameLanguage e (O.language z) at hmem
    rcases hmem with ⟨w, hw, he⟩
    change e.symm _ ∈ O.language z
    rw [← he, e.symm_apply_apply]
    exact hw
  · intro hseen
    apply hmain.2.2
    have hencoded := (mem_encoded_sample_iff e stream t _).2 hseen
    simpa only [generatorOfEquiv, e.apply_symm_apply] using hencoded

/-- NeurIPS Theorem 7.1, with the explicit universe enumeration used by the
membership-query algorithm. -/
theorem theorem_7_1 (e : List A ≃ ℕ) (O : IndexedOracleFamily (List A))
    {stream : ℕ → List A} {z : ℕ}
    (hP : Generic.Presents stream (O.language z))
    (prompts : ℕ → List A) (hrob : ∀ t, RobustPrompt O (prompts t)) :
    GeneratesInLimit e O stream prompts hrob z := by
  obtain ⟨T, hT⟩ := theorem_7_1_uniform e O hP
  exact ⟨T, hT prompts hrob⟩

/-- Abstract countable-alphabet convenience theorem. Its universe enumeration
is selected classically; use `theorem_7_1` for an explicitly supplied coding. -/
theorem theorem_7_1_countable [Countable A] (O : IndexedOracleFamily (List A))
    {stream : ℕ → List A} {z : ℕ}
    (hP : Generic.Presents stream (O.language z))
    (prompts : ℕ → List A) (hrob : ∀ t, RobustPrompt O (prompts t)) :
    GeneratesInLimit (countableEquivNat O) O stream prompts hrob z :=
  theorem_7_1 (countableEquivNat O) O hP prompts hrob

/-- The empty-prompt specialization recovers the unprompted input/output
guarantee. It does not identify the whole-prefix machine with Section 5's
different endpoint-only machine. -/
theorem empty_prompt_generates [Finite A]
    (e : List A ≃ ℕ) (O : IndexedOracleFamily (List A))
    {stream : ℕ → List A} {z : ℕ}
    (hP : Generic.Presents stream (O.language z)) :
    ∃ T, ∀ t, T ≤ t →
      generatorOfEquiv e O stream (fun _ => []) (fun _ => robustPrompt_nil O) t ∈
        O.language z ∧
      generatorOfEquiv e O stream (fun _ => []) (fun _ => robustPrompt_nil O) t ∉
        Generic.sample stream t := by
  obtain ⟨T, hT⟩ := theorem_7_1 e O hP (fun _ => []) (fun _ => robustPrompt_nil O)
  exact ⟨T, fun t ht => (hT t ht).2⟩

end GenLimit.KM.Prompted
