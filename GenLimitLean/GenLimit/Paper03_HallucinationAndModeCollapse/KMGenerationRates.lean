import GenLimit.Paper03_HallucinationAndModeCollapse.GenerationWitnessRates
import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Main
import Mathlib.Data.List.GetD

/-!
# Finite witnesses for the membership-query KM generator

Lemma 5.13 strengthens the presentation-dependent P01 correctness theorem to
a distribution-independent finite set of positive witnesses. The first result
applies to P01's actual stateful machine on a finite list. The single-round
variant uses the same selector and terminating search, initialized above the
sample; resetting this cutoff removes persistent state without changing the
finite-witness argument. Both constructions use membership queries only.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit GenLimit.DiscreteIID

def listStream (xs : List ℕ) (k : ℕ) : ℕ := xs.getD k 0

theorem mem_sample_listStream (xs : List ℕ) (x : ℕ) :
    x ∈ sample (listStream xs) xs.length ↔ x ∈ xs := by
  simp only [mem_sample_iff, List.mem_iff_getElem]
  constructor <;> rintro ⟨k, hk, h⟩ <;> refine ⟨k, hk, ?_⟩
  · change xs.getD k 0 = x at h
    rwa [List.getD_eq_getElem _ _ hk] at h
  · change xs.getD k 0 = x
    rwa [List.getD_eq_getElem _ _ hk]

/-- The original P01 stateful machine run on exactly the observed prefix. -/
def statisticalKM (O : OracleFamily) (xs : List ℕ) : ℕ :=
  O.kmGenerator (listStream xs) xs.length

/-- Initialize one KM search round strictly above every observed point. -/
def freshStart (xs : List ℕ) : ℕ := xs.foldr max 0 + 1

def roundKM (O : OracleFamily) (xs : List ℕ) : ℕ :=
  (O.processRound (listStream xs) xs.length (freshStart xs)).output

theorem lt_freshStart (xs : List ℕ) {x : ℕ} (hx : x ∈ xs) : x < freshStart xs := by
  have h : x ≤ xs.foldr max 0 := by
    induction xs with
    | nil => simp at hx
    | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact (ih hx).trans (le_max_right _ _)
  exact Nat.lt_succ_of_le h

/-- A finite positive sample rules out every earlier non-superset. -/
theorem exists_KM_witness (C : LanguageFamily) (z : ℕ) :
    ∃ T : Finset ℕ, (∀ x ∈ T, x ∈ C z) ∧
      ∀ xs : List ℕ, (∀ x ∈ xs, x ∈ C z) → (∀ x ∈ T, x ∈ xs) →
        Critical C (listStream xs) xs.length z := by
  classical
  let bad := (Finset.range (z + 1)).filter (fun j => ¬C z ⊆ C j)
  have hex (j : {j // j ∈ bad}) : ∃ x, x ∈ C z ∧ x ∉ C j.1 :=
    Set.not_subset.mp (Finset.mem_filter.mp j.2).2
  let w := fun j : {j // j ∈ bad} => Classical.choose (hex j)
  refine ⟨bad.attach.image w, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Classical.choose_spec (hex j)).1
  · intro xs hxs hobs
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hxs x ((mem_sample_listStream xs x).mp hx)
    · intro j hj hcon
      by_contra hnot
      have hjbad : j ∈ bad := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj), hnot⟩
      let b : {j // j ∈ bad} := ⟨j, hjbad⟩
      have hw := Classical.choose_spec (hex b)
      apply hw.2
      apply hcon
      apply (mem_sample_listStream xs (w b)).mpr
      exact hobs (w b) (Finset.mem_image.mpr ⟨b, Finset.mem_attach _ _, rfl⟩)

/-- Source Lemma 5.13 for the existing stateful finite-query P01 algorithm. -/
theorem lemma_5_13 (O : OracleFamily) :
    FiniteWitnessGenerates O.language (statisticalKM O) := by
  intro z
  obtain ⟨T, hT, hcritical⟩ := exists_KM_witness O.language z
  refine ⟨T, hT, z + 1, ?_⟩
  intro xs hn hxs hobs
  have hz := hcritical xs hxs hobs
  have hzt : z < xs.length := Nat.lt_of_succ_le hn
  have hhas : O.HasConsistent (listStream xs) xs.length :=
    ⟨z, O.mem_consistentCandidates.mpr ⟨hzt, O.consistentAt_iff.mpr hz.1⟩⟩
  obtain ⟨j, _, hj, hmax, hout, hfresh⟩ :=
    O.run_round_spec (Nat.zero_lt_of_lt hzt) hhas
  have hzfc := critical_finitelyCritical hz (O.run (listStream xs) xs.length).counter
  have hsub := finitelyCritical_prefix_subset (hmax z hzt hzfc) hzfc hj
  have hy := O.mem_finitePrefix.mp hout
  exact ⟨hsub _ hy.1 hy.2, fun h => hfresh ((mem_sample_listStream xs _).mpr h)⟩

/-- The same finite witnesses work when a single round starts above the sample. -/
theorem roundKM_finiteWitness (O : OracleFamily) :
    FiniteWitnessGenerates O.language (roundKM O) := by
  intro z
  obtain ⟨T, hT, hcritical⟩ := exists_KM_witness O.language z
  refine ⟨T, hT, z + 1, ?_⟩
  intro xs hn hxs hobs
  have hz := hcritical xs hxs hobs
  have hzt : z < xs.length := Nat.lt_of_succ_le hn
  have hhas : O.HasConsistent (listStream xs) xs.length :=
    ⟨z, O.mem_consistentCandidates.mpr ⟨hzt, O.consistentAt_iff.mpr hz.1⟩⟩
  let q := O.roundCounter (listStream xs) xs.length hhas (freshStart xs)
  have heq : roundKM O xs = q - 1 := by
    unfold roundKM
    rw [O.processRound_of_hasConsistent hhas]
  rw [heq]
  have hzfc := critical_finitelyCritical hz q
  have hjfc := O.selected_finitelyCritical (m := q) hhas
  have hmax := O.selected_max hhas hzt (O.finitelyCriticalAt_iff.mpr hzfc)
  have hout := O.mem_finitePrefix.mp (O.roundCounter_output_mem_selectedPrefix hhas (freshStart xs))
  refine ⟨finitelyCritical_prefix_subset hmax hzfc hjfc _ hout.1 hout.2, ?_⟩
  intro hmem
  have hlo := lt_freshStart xs hmem
  have hhi : freshStart xs ≤ q - 1 := Nat.le_sub_one_of_lt (O.roundCounter_gt hhas _)
  omega

theorem statisticalKM_exponential (O : OracleFamily) :
    ExponentialGenerates O.language (deterministicIdentifier (statisticalKM O)) :=
  lemma_5_11 O.language _ (lemma_5_13 O)

theorem roundKM_exponential (O : OracleFamily) :
    ExponentialGenerates O.language (deterministicIdentifier (roundKM O)) :=
  lemma_5_11 O.language _ (roundKM_finiteWitness O)

end GenLimit.HallucinationModeCollapse
