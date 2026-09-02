import GenLimit.Paper14_ListLanguageIdentification.Stabilization

/-!
# The list-identification algorithm

Algorithm 1 and the deterministic upper-bound path from Section 5 of
Charikar--Pabbaraju--Tewari.

The paper numbers its collection from `1`; this development uses Lean's
zero-based natural-number indices.  Consequently the arbitrary singleton
returned when no index is feasible is `[0]` rather than `{1}`.  This branch
is transient on every target presentation and has no effect on correctness.
-/

namespace GenLimit.ListIdentification

/-- The active index set in the recursive call of Algorithm 1. -/
def descendingIndexSet
    (F : GenLimit.Generic.LanguageFamily α)
    (k : ℕ) (I : Set ℕ) (i : ℕ) : Set ℕ :=
  {j |
    j ∈ I ∧
      i < j ∧
      F j ⊂ F i ∧
      (↑(psiTellTale F i k) : Set α) ⊆ F j}

/-- Algorithm 1 in list-valued form.

The input level is `k + 1`, so `psiTellTale F i k` denotes the source's
level-`k + 1` tell-tale `Tᵢ⁽ᵏ⁺¹⁾`. -/
noncomputable def listIdentify
    (F : GenLimit.Generic.LanguageFamily α) :
    ℕ → Set ℕ → Finset α → List ℕ
  | 0, _, _ => []
  | k + 1, I, S => by
      classical
      exact
        if hI : I.Nonempty then
          if hEligible :
              ∃ i, LevelEligible F (fun j => psiTellTale F j k) I S i then
            let i :=
              levelChoice F (fun j => psiTellTale F j k) I S
            i :: listIdentify F k (descendingIndexSet F k I i) S
          else
            [0]
        else
          []

/-- The output-size observation immediately following Algorithm 1. -/
theorem listIdentify_length_le
    (F : GenLimit.Generic.LanguageFamily α)
    (k : ℕ) (I : Set ℕ) (S : Finset α) :
    (listIdentify F k I S).length ≤ k := by
  induction k generalizing I with
  | zero =>
      simp [listIdentify]
  | succ k ih =>
      classical
      simp only [listIdentify]
      split
      next hI =>
        split
        next hEligible =>
          simp only [List.length_cons]
          exact Nat.succ_le_succ
            (ih (descendingIndexSet F k I
              (levelChoice F (fun j => psiTellTale F j k) I S)))
        next hNotEligible =>
          simp
      next hEmpty =>
        simp

/-- Pad a list of at most `k` indices to the fixed-width output type in
Definition 1. -/
def padIndexList (μ : List ℕ) (k : ℕ) : Fin k → ℕ :=
  fun r =>
    if h : r.val < μ.length then
      μ.get ⟨r.val, h⟩
    else
      0

theorem mem_padIndexList
    {μ : List ℕ} {k i : ℕ}
    (hi : i ∈ μ) (hlen : μ.length ≤ k) :
    ∃ r : Fin k, padIndexList μ k r = i := by
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp hi
  let s : Fin k := ⟨r.val, r.isLt.trans_le hlen⟩
  refine ⟨s, ?_⟩
  simp only [padIndexList]
  rw [dif_pos]
  · simpa [s] using hr
  · exact r.isLt

/-- Convert an at-most-`k` list-valued learner to Definition 1's fixed-width
interface. -/
def boundedToFixed
    (A : BoundedListIdentifier α) (k : ℕ) :
    ListIdentifier α k :=
  fun t xs => padIndexList (A t xs) k

theorem targetInIndexList_implies_targetInGuess_pad
    {F : GenLimit.Generic.LanguageFamily α}
    {z k : ℕ} {μ : List ℕ}
    (hlen : μ.length ≤ k)
    (h : TargetInIndexList F z μ) :
    TargetInGuess F z (padIndexList μ k) := by
  obtain ⟨i, hi, hFi⟩ := h
  obtain ⟨r, hr⟩ := mem_padIndexList hi hlen
  exact ⟨r, by simpa [hr] using hFi⟩

/-- Every index admitted to the recursive active set satisfies the next
lower `Psi` predicate. -/
theorem psi_of_mem_descendingIndexSet
    {F : GenLimit.Generic.LanguageFamily α}
    {k i j : ℕ} {I : Set ℕ}
    (hi : Psi F i (k + 1))
    (hj : j ∈ descendingIndexSet F k I i) :
    Psi F j k := by
  have hWitness := psiTellTale_spec hi
  exact hWitness.2 j hj.2.2.2 hj.2.2.1

/-- If the target is a strict sublanguage of the selected language and its
index is larger, Algorithm 1 retains the target in the recursive active set.
-/
theorem target_mem_descendingIndexSet
    {F : GenLimit.Generic.LanguageFamily α}
    {k i z : ℕ} {I : Set ℕ}
    (hzI : z ∈ I) (hiz : i < z)
    (hproper : F z ⊂ F i)
    (hTell : (↑(psiTellTale F i k) : Set α) ⊆ F z) :
    z ∈ descendingIndexSet F k I i := by
  exact ⟨hzI, hiz, hproper, hTell⟩

/-- On every presentation, the list emitted by Algorithm 1 eventually
contains an index denoting the target.  This is the deterministic constructive
upper bound of Theorem 6. -/
theorem listIdentify_eventually_contains_target
    {F : GenLimit.Generic.LanguageFamily α}
    {k z : ℕ} {I : Set ℕ}
    {stream : GenLimit.Generic.Stream α}
    (hPsi : ∀ i, i ∈ I → Psi F i k)
    (hzI : z ∈ I)
    (hP : GenLimit.Generic.Presents stream (F z)) :
    ∃ N, ∀ t, N ≤ t →
      TargetInIndexList F z
        (listIdentify F k I (GenLimit.Generic.sample stream t)) := by
  induction k generalizing I with
  | zero =>
      exact (psi_zero F z (hPsi z hzI)).elim
  | succ k ih =>
      classical
      let T : ℕ → Finset α := fun i => psiTellTale F i k
      have hT :
          ∀ i, i ∈ I → (↑(T i) : Set α) ⊆ F i := by
        intro i hi
        exact (psiTellTale_spec (hPsi i hi)).1
      obtain ⟨Nstable, hstable⟩ :=
        levelChoice_stabilizes
          (F := F) (T := T) (I := I) (z := z)
          hP hzI hT
      let q := limitChoice F T I z
      have hzCandidate : LimitCandidate F T I z z :=
        ⟨hzI, le_rfl, Set.Subset.rfl, hT z hzI⟩
      have hq : LimitCandidate F T I z q := by
        simpa [q] using
          limitChoice_spec (F := F) (T := T) (I := I)
            (z := z) ⟨z, hzCandidate⟩
      obtain ⟨Neligible, hTqSampleAt⟩ :=
        GenLimit.Generic.finset_eventually_subset_sample
          hP (T q) hq.2.2.2
      have hqEventuallyEligible :
          ∀ t, Neligible ≤ t →
            LevelEligible F T I
              (GenLimit.Generic.sample stream t) q := by
        intro t ht
        have hSampleTarget :
            (↑(GenLimit.Generic.sample stream t) : Set α) ⊆ F z := by
          intro x hx
          exact
            GenLimit.Generic.mem_language_of_mem_sample_of_presents hP hx
        exact
          ⟨hq.1, hSampleTarget.trans hq.2.2.1,
            hTqSampleAt.trans (GenLimit.Generic.sample_mono ht)⟩
      by_cases hqTarget : F q = F z
      · refine ⟨max Nstable Neligible, ?_⟩
        intro t ht
        have hst : Nstable ≤ t := (Nat.le_max_left _ _).trans ht
        have hel : Neligible ≤ t := (Nat.le_max_right _ _).trans ht
        have hqEligible := hqEventuallyEligible t hel
        have hExists :
            ∃ i, LevelEligible F T I
              (GenLimit.Generic.sample stream t) i :=
          ⟨q, hqEligible⟩
        have hChoice :
            levelChoice F T I (GenLimit.Generic.sample stream t) = q := by
          simpa [q] using hstable t hst
        refine ⟨q, ?_, hqTarget⟩
        simp only [listIdentify]
        rw [dif_pos ⟨z, hzI⟩, dif_pos hExists]
        simp only [List.mem_cons]
        exact Or.inl hChoice.symm
      · have hqProper : F z ⊂ F q :=
          ⟨hq.2.2.1, fun hback =>
            hqTarget (Set.Subset.antisymm hback hq.2.2.1)⟩
        have hqz : q < z := by
          have hqne : q ≠ z := by
            intro hqzEq
            apply hqTarget
            rw [hqzEq]
          exact Nat.lt_of_le_of_ne hq.2.1 hqne
        let I' := descendingIndexSet F k I q
        have hzI' : z ∈ I' := by
          exact target_mem_descendingIndexSet
            hzI hqz hqProper hq.2.2.2
        have hPsiQ : Psi F q (k + 1) :=
          hPsi q hq.1
        have hPsi' : ∀ i, i ∈ I' → Psi F i k := by
          intro i hi
          exact psi_of_mem_descendingIndexSet hPsiQ hi
        obtain ⟨Nrecursive, hrecursive⟩ :=
          ih hPsi' hzI'
        refine ⟨max Nstable (max Neligible Nrecursive), ?_⟩
        intro t ht
        have hst : Nstable ≤ t :=
          (Nat.le_max_left _ _).trans ht
        have hel : Neligible ≤ t :=
          (Nat.le_max_left _ _).trans
            ((Nat.le_max_right _ _).trans ht)
        have hrec : Nrecursive ≤ t :=
          (Nat.le_max_right _ _).trans
            ((Nat.le_max_right _ _).trans ht)
        have hqEligible := hqEventuallyEligible t hel
        have hExists :
            ∃ i, LevelEligible F T I
              (GenLimit.Generic.sample stream t) i :=
          ⟨q, hqEligible⟩
        have hChoice :
            levelChoice F T I (GenLimit.Generic.sample stream t) = q := by
          simpa [q] using hstable t hst
        have hChoice' :
            levelChoice F (fun j => psiTellTale F j k) I
                (GenLimit.Generic.sample stream t) = q := by
          simpa [T] using hChoice
        obtain ⟨i, hiList, hiTarget⟩ := hrecursive t hrec
        refine ⟨i, ?_, hiTarget⟩
        simp only [listIdentify]
        rw [dif_pos ⟨z, hzI⟩, dif_pos hExists]
        simp only [List.mem_cons]
        apply Or.inr
        rw [hChoice']
        simpa [I'] using hiList

/-- Theorem 6, as an existence theorem for the paper's list-valued
Algorithm 1. -/
theorem theorem6_kAngluin_sufficient
    {F : GenLimit.Generic.LanguageFamily α} {k : ℕ}
    (h : KAngluinCondition F k) :
    ∃ A : BoundedListIdentifier α,
      HasListBound A k ∧
      ∀ z, ∀ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream (F z) →
          ∃ N, ∀ t, N ≤ t →
            TargetInIndexList F z
              (A t (fun i => stream i)) := by
  let A : BoundedListIdentifier α :=
    fun _ xs =>
      listIdentify F k Set.univ
        (GenLimit.Generic.sequenceSample xs)
  refine ⟨A, ?_, ?_⟩
  · intro t xs
    exact listIdentify_length_le F k Set.univ
      (GenLimit.Generic.sequenceSample xs)
  · intro z stream hP
    simpa [A, GenLimit.Generic.sequenceSample_prefix] using
      (listIdentify_eventually_contains_target
        (F := F) (k := k) (z := z) (I := Set.univ)
        (fun i _ => h i) (Set.mem_univ z) hP)

/-- Fixed-width formulation of Theorem 6 using Definitions 1 and 2. -/
theorem theorem6_kAngluin_listIdentifiable
    {F : GenLimit.Generic.LanguageFamily α} {k : ℕ}
    (h : KAngluinCondition F k) :
    ListIdentifiable F k := by
  obtain ⟨B, hBound, hCorrect⟩ :=
    theorem6_kAngluin_sufficient (F := F) h
  refine ⟨boundedToFixed B k, ?_⟩
  intro z stream hP
  obtain ⟨N, hN⟩ := hCorrect z stream hP
  refine ⟨N, ?_⟩
  intro t ht
  have hList := hN t ht
  have hPadded :=
    targetInIndexList_implies_targetInGuess_pad
      (hBound t (fun i : Fin t => stream i)) hList
  simpa [boundedToFixed, listOutput] using hPadded

end GenLimit.ListIdentification
