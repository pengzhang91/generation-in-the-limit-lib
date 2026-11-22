import GenLimit.Paper01_LanguageGeneration.Semantic
import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Main
import GenLimit.Paper01_LanguageGeneration.ObservedSetTransport

/-! # Distinct outputs in the two constructions for Theorem 2.1 -/

namespace GenLimit.KM.DistinctOutputs

/-- The observations alone determine criticality. Previously generated values
are excluded only when choosing the least fresh value from that language. -/
noncomputable def semanticStep (O : OracleFamily) (s : ℕ → ℕ) (t : ℕ)
    (history : Finset ℕ) : ℕ :=
  SetInterface.fresh O (sample s t ∪ history) (Semantic.focus O.language s t)

noncomputable def history (O : OracleFamily) (s : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | t + 1 => let old := history O s t
             insert (semanticStep O s t old) old

noncomputable def semanticOutput (O : OracleFamily) (s : ℕ → ℕ) (t : ℕ) : ℕ :=
  semanticStep O s t (history O s t)

private theorem history_mono (O : OracleFamily) (s : ℕ → ℕ) :
    Monotone (history O s) :=
  monotone_nat_of_le_succ fun _ => Finset.subset_insert _ _

private theorem semantic_spec (O : OracleFamily) (s : ℕ → ℕ) (t : ℕ) :
    semanticOutput O s t ∈ O.language (Semantic.focus O.language s t) ∧
    semanticOutput O s t ∉ sample s t ∪ history O s t :=
  SetInterface.fresh_spec _ _ _

def GeneratesDistinct (out : ℕ → ℕ) (K : Language) (s : ℕ → ℕ) : Prop :=
  Function.Injective out ∧ ∃ T, ∀ t ≥ T, out t ∈ K ∧ out t ∉ sample s t

/-- Section 4 with the lowest unseen output from the same critical language. -/
theorem semantic_generates (O : OracleFamily) {s : ℕ → ℕ} {z : ℕ}
    (hp : Presents s (O.language z)) :
    GeneratesDistinct (semanticOutput O s) (O.language z) s := by
  have different : ∀ {i j : ℕ}, i < j → semanticOutput O s i ≠ semanticOutput O s j := by
    intro i j hij heq
    have hi : semanticOutput O s i ∈ history O s (i+1) := Finset.mem_insert_self _ _
    exact (semantic_spec O s j).2 (Finset.mem_union_right _ (heq ▸ history_mono O s hij hi))
  constructor
  · intro i j heq
    exact le_antisymm (le_of_not_gt fun h => different h heq.symm)
      (le_of_not_gt fun h => different h heq)
  obtain ⟨T, hT⟩ := target_eventually_critical hp
  refine ⟨max T (z+1), fun t ht => ?_⟩
  have hz := hT t ((Nat.le_max_left ..).trans ht)
  have hf := Semantic.focus_spec (Nat.lt_of_succ_le ((Nat.le_max_right ..).trans ht)) hz
  obtain ⟨hm, hs⟩ := semantic_spec O s t
  exact ⟨critical_subset_of_le hf.2.2 hz hf.2.1 hm, fun h => hs (Finset.mem_union_left _ h)⟩

/-- Use the Section 5 endpoint search, also advancing past the previous
output in the rounds where no consistent candidate is available. -/
def queryStep (O : OracleFamily) (s : ℕ → ℕ) (t previous : ℕ) : ℕ :=
  let start := max (previous + 1) ((sample s t).sup id + 1)
  if h : O.HasConsistent s t then O.roundCounter s t h start - 1 else start

def queryOutput (O : OracleFamily) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => queryStep O s (t+1) (queryOutput O s t)

private theorem queryStep_bound (O : OracleFamily) (s : ℕ → ℕ) (t p : ℕ) :
    max (p+1) ((sample s t).sup id + 1) ≤ queryStep O s t p := by
  unfold queryStep
  split
  · exact Nat.le_sub_one_of_lt (O.roundCounter_gt _ _)
  · exact le_rfl

/-- Section 5 with pairwise distinct outputs, including all fallback rounds. -/
theorem finiteQuery_generates (O : OracleFamily) {s : ℕ → ℕ} {z : ℕ}
    (hp : Presents s (O.language z)) :
    GeneratesDistinct (queryOutput O s) (O.language z) s := by
  constructor
  · apply StrictMono.injective
    apply strictMono_nat_of_lt_succ
    intro t
    exact (Nat.le_max_left ..).trans (queryStep_bound O s (t+1) _)
  obtain ⟨T, hT⟩ := target_eventually_finitelyCritical hp
  refine ⟨max T (z+1), fun t ht => ?_⟩
  have hzt : z < t := (Nat.le_max_right ..).trans ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  let p := queryOutput O s k
  let b := max (p+1) ((sample s (k+1)).sup id + 1)
  have hc : O.HasConsistent s (k+1) :=
    ⟨z, O.mem_consistentCandidates.mpr ⟨hzt, O.consistentAt_iff.mpr (presents_consistent hp)⟩⟩
  let q := O.roundCounter s (k+1) hc b
  have hz := hT (k+1) ((Nat.le_max_left ..).trans ht) q
  have hn := O.selected_max hc hzt (O.finitelyCriticalAt_iff.mpr hz)
  have hm := O.mem_finitePrefix.mp (O.roundCounter_output_mem_selectedPrefix hc b)
  constructor
  · have he : queryOutput O s (k+1) = q - 1 := by simp [queryOutput, queryStep, hc, q, b, p]
    rw [he]
    exact finitelyCritical_prefix_subset hn hz (O.selected_finitelyCritical hc) _ hm.1 hm.2
  · intro hs
    have hle := Finset.le_sup (s := sample s (k+1)) (f := id) hs
    have hlt := (Nat.le_max_right (p+1) _).trans (queryStep_bound O s (k+1) p)
    exact Nat.not_lt_of_ge hle hlt

/-- Decode the output of either machine along the supplied enumeration. -/
def decoded (e : α ≃ ℕ) (out : ℕ → ℕ) : ℕ → α := e.symm ∘ out

def GeneratesDistinctOn (out : ℕ → α) (K : Set α) (s : ℕ → α) : Prop :=
  Function.Injective out ∧ ∃ T, ∀ t ≥ T, out t ∈ K ∧ out t ∉ Generic.sample s t

private theorem decode_generates (e : α ≃ ℕ) {out : ℕ → ℕ} {K : Set α} {s : ℕ → α}
    (h : GeneratesDistinct out (Support.renameLanguage e K) (Support.renameStream e s)) :
    GeneratesDistinctOn (decoded e out) K s := by
  obtain ⟨hinj, T, hT⟩ := h
  refine ⟨e.symm.injective.comp hinj, T, fun t ht => ?_⟩
  obtain ⟨hm, hf⟩ := hT t ht
  constructor
  · apply (Support.mem_renameLanguage_iff e K _).mp
    simpa [decoded] using hm
  · intro hs
    apply hf
    simpa [decoded] using (Transport.mem_encoded_sample_iff e s t _).mpr hs

/-- Both distinct-output constructions on any explicitly enumerated universe. -/
theorem generates_of_equiv (e : α ≃ ℕ) (O : Transport.IndexedOracleFamily α)
    {s : ℕ → α} {z : ℕ} (hp : Generic.Presents s (O.language z)) :
    GeneratesDistinctOn
      (decoded e (semanticOutput (Transport.encodeFamily e O) (Support.renameStream e s)))
      (O.language z) s ∧
    GeneratesDistinctOn
      (decoded e (queryOutput (Transport.encodeFamily e O) (Support.renameStream e s)))
      (O.language z) s := by
  have hp' : Presents (Support.renameStream e s) ((Transport.encodeFamily e O).language z) :=
    Support.presents_renameStream e hp
  exact ⟨decode_generates e (semantic_generates _ hp'), decode_generates e (finiteQuery_generates _ hp')⟩

end GenLimit.KM.DistinctOutputs
