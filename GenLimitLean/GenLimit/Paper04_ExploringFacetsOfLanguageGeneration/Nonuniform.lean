import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Definitions
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Card

/-!
# Charikar--Pabbaraju: non-uniform generation

This file formalizes the construction and upper bound in Section 3 of
Charikar--Pabbaraju, *Exploring Facets of Language Generation in the Limit*,
arXiv:2411.15364v2.

Paper indices start at one.  Here the target `C i` has paper index `i + 1`,
which explains the `i + 1` term in the threshold.  The family is represented
as an indexed sequence, so its enumeration order and repeated languages are
preserved.
-/

namespace GenLimit.CharikarPabbaraju

/-- Intersection of a finite indexed subcollection.  The empty intersection
is the whole universe. -/
def familyIntersection
    (C : GenLimit.Generic.LanguageFamily α) (J : Finset ℕ) : Set α :=
  {x | ∀ i, i ∈ J → x ∈ C i}

@[simp] theorem mem_familyIntersection
    {C : GenLimit.Generic.LanguageFamily α} {J : Finset ℕ} {x : α} :
    x ∈ familyIntersection C J ↔ ∀ i, i ∈ J → x ∈ C i :=
  Iff.rfl

@[simp] theorem familyIntersection_empty
    (C : GenLimit.Generic.LanguageFamily α) :
    familyIntersection C ∅ = Set.univ := by
  ext x
  simp [familyIntersection]

@[simp] theorem familyIntersection_insert
    (C : GenLimit.Generic.LanguageFamily α) (i : ℕ) (J : Finset ℕ) :
    familyIntersection C (insert i J) = C i ∩ familyIntersection C J := by
  ext x
  simp [familyIntersection]

/-- Definition 6 (`def:m(L)`), with one-based paper indices translated to
zero-based Lean indices.  The supremum is over all finite subcollections of
`C 0, ..., C i` that contain `C i` and have finite intersection. -/
noncomputable def nonuniformComplexity
    (C : GenLimit.Generic.LanguageFamily α) (i : ℕ) : ℕ := by
  classical
  exact (Finset.range (i + 1)).powerset.sup fun J =>
    if i ∈ J ∧ (familyIntersection C J).Finite
    then (familyIntersection C J).ncard
    else 0

theorem finite_intersection_ncard_le_complexity
    {C : GenLimit.Generic.LanguageFamily α} {i : ℕ} (J : Finset ℕ)
    (hJ : J ⊆ Finset.range (i + 1)) (hi : i ∈ J)
    (hfinite : (familyIntersection C J).Finite) :
    (familyIntersection C J).ncard ≤ nonuniformComplexity C i := by
  classical
  have hmem : J ∈ (Finset.range (i + 1)).powerset :=
    Finset.mem_powerset.mpr hJ
  have hle := Finset.le_sup
    (f := fun J : Finset ℕ =>
      if i ∈ J ∧ (familyIntersection C J).Finite
      then (familyIntersection C J).ncard
      else 0) hmem
  simpa [nonuniformComplexity, hi, hfinite] using hle

/-- Indices accepted by the paper's greedy intersection algorithm after it
has scanned `C 0, ..., C (n-1)`. -/
noncomputable def selectedIndices
    (C : GenLimit.Generic.LanguageFamily α) (S : Finset α) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => by
      classical
      let J := selectedIndices C S n
      exact if (↑S : Set α) ⊆ C n ∧
          (familyIntersection C (insert n J)).Infinite
      then insert n J
      else J

/-- The maintained set `I_t` in the paper's algorithm. -/
noncomputable def greedyCore
    (C : GenLimit.Generic.LanguageFamily α) (S : Finset α) (n : ℕ) : Set α :=
  familyIntersection C (selectedIndices C S n)

theorem selectedIndices_subset_range
    (C : GenLimit.Generic.LanguageFamily α) (S : Finset α) (n : ℕ) :
    selectedIndices C S n ⊆ Finset.range n := by
  classical
  induction n with
  | zero => simp [selectedIndices]
  | succ n ih =>
      simp only [selectedIndices]
      split
      · exact Finset.insert_subset_iff.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_self n),
            ih.trans (Finset.range_mono (Nat.le_succ n))⟩
      · exact ih.trans (Finset.range_mono (Nat.le_succ n))

theorem selectedIndices_step_subset
    (C : GenLimit.Generic.LanguageFamily α) (S : Finset α) (n : ℕ) :
    selectedIndices C S n ⊆ selectedIndices C S (n + 1) := by
  classical
  simp only [selectedIndices]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.rfl

theorem selectedIndices_mono
    (C : GenLimit.Generic.LanguageFamily α) (S : Finset α) :
    Monotone (selectedIndices C S) :=
  monotone_nat_of_le_succ (selectedIndices_step_subset C S)

theorem sample_subset_greedyCore
    (C : GenLimit.Generic.LanguageFamily α) (S : Finset α) (n : ℕ) :
    (↑S : Set α) ⊆ greedyCore C S n := by
  classical
  induction n with
  | zero => simp [greedyCore, selectedIndices]
  | succ n ih =>
      simp only [greedyCore, selectedIndices]
      split
      next h =>
        simpa [familyIntersection_insert] using Set.subset_inter h.1 ih
      next => simpa [greedyCore] using ih

theorem greedyCore_infinite [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) (S : Finset α) (n : ℕ) :
    (greedyCore C S n).Infinite := by
  classical
  induction n with
  | zero => simpa [greedyCore, selectedIndices] using (Set.infinite_univ : (Set.univ : Set α).Infinite)
  | succ n ih =>
      simp only [greedyCore, selectedIndices]
      split
      next h => simpa [familyIntersection_insert] using h.2
      next => simpa [greedyCore] using ih

theorem target_selected_at_threshold
    {C : GenLimit.Generic.LanguageFamily α} {S : Finset α} {i : ℕ}
    (hS : (↑S : Set α) ⊆ C i)
    (hcard : nonuniformComplexity C i < S.card) :
    i ∈ selectedIndices C S (i + 1) := by
  classical
  let J := insert i (selectedIndices C S i)
  have hJsub : J ⊆ Finset.range (i + 1) := by
    refine Finset.insert_subset_iff.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self i), ?_⟩
    exact (selectedIndices_subset_range C S i).trans
      (Finset.range_mono (Nat.le_succ i))
  have hiJ : i ∈ J := Finset.mem_insert_self i _
  have hSJ : (↑S : Set α) ⊆ familyIntersection C J := by
    rw [show J = insert i (selectedIndices C S i) from rfl,
      familyIntersection_insert]
    exact Set.subset_inter hS (sample_subset_greedyCore C S i)
  have hJinf : (familyIntersection C J).Infinite := by
    by_contra hnot
    have hfinite : (familyIntersection C J).Finite := not_not.mp hnot
    have hlow : S.card ≤ (familyIntersection C J).ncard := by
      simpa using Set.ncard_le_ncard hSJ hfinite
    have hupp : (familyIntersection C J).ncard ≤ nonuniformComplexity C i :=
      finite_intersection_ncard_le_complexity J hJsub hiJ hfinite
    exact (Nat.not_lt_of_ge (hlow.trans hupp)) hcard
  change i ∈ selectedIndices C S (Nat.succ i)
  simp [selectedIndices, hS, show familyIntersection C
    (insert i (selectedIndices C S i)) = familyIntersection C J from rfl, hJinf]

theorem greedyCore_subset_target
    {C : GenLimit.Generic.LanguageFamily α} {S : Finset α} {i n : ℕ}
    (hi : i ∈ selectedIndices C S n) :
    greedyCore C S n ⊆ C i := by
  intro x hx
  exact hx i hi

/-- Semantic form of the greedy algorithm.  The paper notes that its two
tests can be implemented using membership queries plus a finite-intersection
finiteness oracle; here they are resolved classically. -/
noncomputable def greedyGenerator [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) : GenLimit.Generic.Generator α := by
  classical
  exact fun t xs =>
    let S := GenLimit.Generic.sequenceSample xs
    Classical.choose
      ((greedyCore_infinite C S t).diff S.finite_toSet).nonempty

theorem greedyGenerator_spec [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) {t : ℕ} (xs : Fin t → α) :
    greedyGenerator C t xs ∈
      greedyCore C (GenLimit.Generic.sequenceSample xs) t \
        (↑(GenLimit.Generic.sequenceSample xs) : Set α) := by
  classical
  simpa only [greedyGenerator] using
    Classical.choose_spec
      ((greedyCore_infinite C (GenLimit.Generic.sequenceSample xs) t).diff
        (GenLimit.Generic.sequenceSample xs).finite_toSet).nonempty

/-- Theorem 6 (`thm:non-uniform-ub`): the algorithm is correct once the number of distinct inputs
is at least `max(i+1, m_C(C i)+1)` (paper index `i+1`). -/
theorem nonuniform_upper_bound [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) {i t : ℕ}
    (stream : GenLimit.Generic.Stream α)
    (hstream : GenLimit.Generic.StreamIn stream (C i))
    (hthreshold : max (i + 1) (nonuniformComplexity C i + 1) ≤
      (GenLimit.Generic.sample stream t).card) :
    GenLimit.Generic.CorrectAt (greedyGenerator C) (C i) stream t := by
  let S := GenLimit.Generic.sample stream t
  have hiCard : i + 1 ≤ S.card :=
    (Nat.le_max_left _ _).trans hthreshold
  have hmCard : nonuniformComplexity C i < S.card := by
    apply Nat.lt_of_succ_le
    exact (Nat.le_max_right _ _).trans hthreshold
  have hit : i + 1 ≤ t :=
    hiCard.trans (GenLimit.Generic.sample_card_le stream t)
  have hS : (↑S : Set α) ⊆ C i := by
    intro x hx
    obtain ⟨s, -, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hx
    exact hstream ⟨s, rfl⟩
  have hiFirst : i ∈ selectedIndices C S (i + 1) :=
    target_selected_at_threshold hS hmCard
  have hiFinal : i ∈ selectedIndices C S t :=
    selectedIndices_mono C S hit hiFirst
  have hspec := greedyGenerator_spec C (fun j : Fin t => stream j)
  rw [GenLimit.Generic.sequenceSample_prefix] at hspec
  change greedyGenerator C t (fun j : Fin t => stream j) ∈ C i ∧
    greedyGenerator C t (fun j : Fin t => stream j) ∉ S
  exact ⟨greedyCore_subset_target hiFinal hspec.1, hspec.2⟩

/-- Overview Theorem 1 / consequence of Theorem 6: every enumerated
countable collection of infinite languages is non-uniformly generatable. -/
theorem countable_collections_nonuniformly_generatable
    [Infinite α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (_hInfinite : ∀ i, (C i).Infinite) :
    ∃ gen : GenLimit.Generic.Generator α, IsNonuniformGenerator gen C := by
  refine ⟨greedyGenerator C, ?_⟩
  intro i
  refine ⟨max (i + 1) (nonuniformComplexity C i + 1), ?_⟩
  intro stream hP t ht
  exact nonuniform_upper_bound C stream
    (GenLimit.Generic.streamIn_of_presents hP) ht

end GenLimit.CharikarPabbaraju
