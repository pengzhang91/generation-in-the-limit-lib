import GenLimit.Paper18_SafeLanguageGeneration.Definitions
import GenLimit.Support.Fresh
import GenLimit.Support.LeastCandidate
import Mathlib.Data.Finset.Max

/-!
# Safe generation when every target--harmful difference is infinite

This is the semantic construction behind Theorem 6.3 of
Anastasopoulos--Ateniese--Kornaropoulos, arXiv:2601.08648v2.  The target
candidate is the highest critical target language in finite scope; the
harmful candidate is the least consistent harmful language.  Once the former
is contained in the true target and the latter contains the true harmful
language, every fresh point in their difference is safe.
-/

namespace GenLimit.SafeGeneration

open GenLimit.Generic

/-- Finite target--harmful intersections imply the cross-difference
hypothesis of Theorem 6.3 whenever every target language is infinite. -/
theorem allCrossDifferencesInfinite_of_finite_cross_intersections
    (targets harmfuls : Generic.LanguageFamily α)
    (hTargets : ∀ i, (targets i).Infinite)
    (hIntersections : ∀ i j, (targets i ∩ harmfuls j).Finite) :
    AllCrossDifferencesInfinite targets harmfuls := by
  intro i j hDifference
  apply hTargets i
  apply (hDifference.union (hIntersections i j)).subset
  intro x hx
  by_cases hxHarmful : x ∈ harmfuls j
  · exact Or.inr ⟨hx, hxHarmful⟩
  · exact Or.inl ⟨hx, hxHarmful⟩

/-- Finite-history consistency for one label. -/
def ConsistentAt
    (C : Generic.LanguageFamily α) {t : ℕ} (xs : Fin t → Tagged α)
    (b : Bool) (i : ℕ) : Prop :=
  (↑(historyTaggedSample xs b) : Set α) ⊆ C i

theorem target_consistentAt
    {C : Generic.LanguageFamily α} {stream : Stream (Tagged α)}
    {b : Bool} {z t : ℕ}
    (hP : taggedRange stream b = C z) :
    ConsistentAt C (fun i : Fin t => stream i) b z := by
  intro x hx
  rw [historyTaggedSample_prefix] at hx
  obtain ⟨n, -, hn⟩ := mem_taggedSample_iff.mp hx
  rw [← hP]
  exact ⟨n, hn⟩

/-- A strict analogue of the KM critical relation for tagged histories. -/
def CriticalAt
    (C : Generic.LanguageFamily α) {t : ℕ} (xs : Fin t → Tagged α)
    (b : Bool) (n : ℕ) : Prop :=
  ConsistentAt C xs b n ∧
    ∀ i, i ≤ n → ConsistentAt C xs b i → C n ⊆ C i

theorem criticalAt_subset_of_le
    {C : Generic.LanguageFamily α} {t : ℕ} {xs : Fin t → Tagged α}
    {b : Bool} {i j : ℕ}
    (hij : i ≤ j) (hi : CriticalAt C xs b i)
    (hj : CriticalAt C xs b j) :
    C j ⊆ C i :=
  hj.2 i hij hi.1

/-- Every bounded candidate that fails to contain the presented language is
eventually inconsistent. -/
theorem bad_bounded_eventually_inconsistent
    {C : Generic.LanguageFamily α} {stream : Stream (Tagged α)}
    {b : Bool} {L : Generic.Language α}
    (hP : taggedRange stream b = L) (bound : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < bound →
      ¬L ⊆ C i →
      ¬ConsistentAt C (fun q : Fin t => stream q) b i := by
  classical
  induction bound with
  | zero =>
      exact ⟨0, by simp⟩
  | succ bound ih =>
      obtain ⟨Tprev, hprev⟩ := ih
      by_cases hsub : L ⊆ C bound
      · refine ⟨Tprev, ?_⟩
        intro t ht i hi hbad
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hprev t ht i hi hbad
        · exact False.elim (hbad hsub)
      · obtain ⟨x, hxL, hxnot⟩ := Set.not_subset.mp hsub
        obtain ⟨Tx, hTx⟩ := eventually_mem_taggedSample hP hxL
        refine ⟨max Tprev Tx, ?_⟩
        intro t ht i hi hbad hcon
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hprev t (le_trans (Nat.le_max_left _ _) ht) i hi hbad hcon
        · exact hxnot (hcon (by
            rw [historyTaggedSample_prefix]
            exact hTx t (le_trans (Nat.le_max_right _ _) ht)))

/-- The true target index is eventually critical for its labeled sample. -/
theorem target_eventually_criticalAt
    {C : Generic.LanguageFamily α} {stream : Stream (Tagged α)}
    {b : Bool} {z : ℕ}
    (hP : taggedRange stream b = C z) :
    ∃ T, ∀ t, T ≤ t →
      CriticalAt C (fun q : Fin t => stream q) b z := by
  obtain ⟨T, hT⟩ := bad_bounded_eventually_inconsistent hP z
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨target_consistentAt hP, ?_⟩
  intro i hiz hcon
  rcases eq_or_lt_of_le hiz with rfl | hiz
  · exact Set.Subset.rfl
  · by_contra hsub
    exact (hT t ht i hiz hsub) hcon

/-- Critical candidates currently in finite index scope. -/
noncomputable def criticalIndices
    (C : Generic.LanguageFamily α) {t : ℕ} (xs : Fin t → Tagged α)
    (b : Bool) : Finset ℕ := by
  classical
  exact (Finset.range t).filter fun i => CriticalAt C xs b i

@[simp] theorem mem_criticalIndices
    {C : Generic.LanguageFamily α} {t : ℕ} {xs : Fin t → Tagged α}
    {b : Bool} {i : ℕ} :
    i ∈ criticalIndices C xs b ↔ i < t ∧ CriticalAt C xs b i := by
  classical
  simp [criticalIndices]

/-- Highest critical target candidate in finite scope. -/
noncomputable def upperFocus
    (C : Generic.LanguageFamily α) {t : ℕ} (xs : Fin t → Tagged α)
    (b : Bool) : ℕ := by
  classical
  let candidates := criticalIndices C xs b
  exact if h : candidates.Nonempty then candidates.max' h else 0

theorem upperFocus_spec
    {C : Generic.LanguageFamily α} {t : ℕ} {xs : Fin t → Tagged α}
    {b : Bool} {z : ℕ}
    (hzt : z < t) (hz : CriticalAt C xs b z) :
    upperFocus C xs b < t ∧
      CriticalAt C xs b (upperFocus C xs b) ∧
      z ≤ upperFocus C xs b := by
  classical
  let candidates := criticalIndices C xs b
  have hzmem : z ∈ candidates := by
    simpa [candidates] using (mem_criticalIndices.mpr ⟨hzt, hz⟩)
  have hne : candidates.Nonempty := ⟨z, hzmem⟩
  have hfmem : candidates.max' hne ∈ candidates :=
    Finset.max'_mem candidates hne
  have hfocus : upperFocus C xs b = candidates.max' hne := by
    simp [upperFocus, candidates, hne]
  rw [hfocus]
  have hparts :
      candidates.max' hne < t ∧
        CriticalAt C xs b (candidates.max' hne) := by
    simpa [candidates] using (mem_criticalIndices.mp hfmem)
  exact ⟨hparts.1, hparts.2, Finset.le_max' candidates z hzmem⟩

/-- Consistent candidates currently in finite index scope. -/
noncomputable def consistentIndices
    (C : Generic.LanguageFamily α) {t : ℕ} (xs : Fin t → Tagged α)
    (b : Bool) : Finset ℕ := by
  classical
  exact (Finset.range t).filter fun i => ConsistentAt C xs b i

@[simp] theorem mem_consistentIndices
    {C : Generic.LanguageFamily α} {t : ℕ} {xs : Fin t → Tagged α}
    {b : Bool} {i : ℕ} :
    i ∈ consistentIndices C xs b ↔ i < t ∧ ConsistentAt C xs b i := by
  classical
  simp [consistentIndices]

/-- Least consistent harmful candidate in finite scope. -/
noncomputable def lowerFocus
    (C : Generic.LanguageFamily α) {t : ℕ} (xs : Fin t → Tagged α)
    (b : Bool) : ℕ := by
  classical
  let candidates := consistentIndices C xs b
  exact GenLimit.Support.leastCandidateWithFallback candidates 0

theorem lowerFocus_spec
    {C : Generic.LanguageFamily α} {t : ℕ} {xs : Fin t → Tagged α}
    {b : Bool} {z : ℕ}
    (hzt : z < t) (hz : ConsistentAt C xs b z) :
    lowerFocus C xs b < t ∧
      ConsistentAt C xs b (lowerFocus C xs b) ∧
      lowerFocus C xs b ≤ z := by
  classical
  let candidates := consistentIndices C xs b
  have hzmem : z ∈ candidates := by
    simpa [candidates] using (mem_consistentIndices.mpr ⟨hzt, hz⟩)
  have hne : candidates.Nonempty := ⟨z, hzmem⟩
  have hfmem :
      GenLimit.Support.leastCandidateWithFallback candidates 0 ∈ candidates :=
    GenLimit.Support.leastCandidateWithFallback_mem hne
  have hfocus :
      lowerFocus C xs b =
        GenLimit.Support.leastCandidateWithFallback candidates 0 := by
    simp [lowerFocus, candidates]
  rw [hfocus]
  have hparts :
      GenLimit.Support.leastCandidateWithFallback candidates 0 < t ∧
        ConsistentAt C xs b
          (GenLimit.Support.leastCandidateWithFallback candidates 0) := by
    simpa [candidates] using (mem_consistentIndices.mp hfmem)
  exact
    ⟨hparts.1, hparts.2,
      GenLimit.Support.leastCandidateWithFallback_le hzmem⟩

/-- The algorithm's current candidate difference. -/
def focusedDifference
    (targets harmfuls : Generic.LanguageFamily α)
    {t : ℕ} (xs : Fin t → Tagged α) : Set α :=
  targets (upperFocus targets xs true) \
    harmfuls (lowerFocus harmfuls xs false)

/-- Choose a fresh element of the current candidate difference. -/
noncomputable def safeValue
    (targets harmfuls : Generic.LanguageFamily α)
    (hCross : AllCrossDifferencesInfinite targets harmfuls)
    {t : ℕ} (xs : Fin t → Tagged α) : α := by
  exact GenLimit.Support.freshFromInfinite
    (focusedDifference targets harmfuls xs)
    (hCross (upperFocus targets xs true) (lowerFocus harmfuls xs false))
    (historyObservedSample xs)

theorem safeValue_spec
    (targets harmfuls : Generic.LanguageFamily α)
    (hCross : AllCrossDifferencesInfinite targets harmfuls)
    {t : ℕ} (xs : Fin t → Tagged α) :
    safeValue targets harmfuls hCross xs ∈ focusedDifference targets harmfuls xs ∧
      safeValue targets harmfuls hCross xs ∉ historyObservedSample xs := by
  constructor
  · exact GenLimit.Support.freshFromInfinite_mem _ _ _
  · exact GenLimit.Support.freshFromInfinite_not_mem _ _ _

/-- Algorithm for the all-infinite-differences model. -/
noncomputable def infiniteDifferenceGenerator
    (targets harmfuls : Generic.LanguageFamily α)
    (hCross : AllCrossDifferencesInfinite targets harmfuls) :
    SafeGenerator α :=
  fun _ xs => some (safeValue targets harmfuls hCross xs)

/-- Theorem 6.3: every pair of countable families whose cross differences
are infinite is safely generatable in the `SG∞` model. -/
theorem theorem_6_3
    (targets harmfuls : Generic.LanguageFamily α)
    (hCross : AllCrossDifferencesInfinite targets harmfuls) :
    SafelyGeneratesInfiniteDifferences
      (infiniteDifferenceGenerator targets harmfuls hCross)
      targets harmfuls := by
  intro z j stream hP
  obtain ⟨TK, hTK⟩ := target_eventually_criticalAt hP.1
  obtain ⟨TH, hTH⟩ :=
    bad_bounded_eventually_inconsistent hP.2 (j + 1)
  refine ⟨max (max TK TH) (max (z + 1) (j + 1)), ?_⟩
  intro t ht
  have hTKt : TK ≤ t :=
    le_trans (Nat.le_max_left TK TH)
      (le_trans (Nat.le_max_left (max TK TH) _) ht)
  have hTHt : TH ≤ t :=
    le_trans (Nat.le_max_right TK TH)
      (le_trans (Nat.le_max_left (max TK TH) _) ht)
  have hzt : z < t := Nat.lt_of_succ_le
    (le_trans (Nat.le_max_left (z + 1) (j + 1))
      (le_trans (Nat.le_max_right (max TK TH) _) ht))
  have hjt : j < t := Nat.lt_of_succ_le
    (le_trans (Nat.le_max_right (z + 1) (j + 1))
      (le_trans (Nat.le_max_right (max TK TH) _) ht))
  let xs : Fin t → Tagged α := fun q => stream q
  have hzcrit : CriticalAt targets xs true z := hTK t hTKt
  have hupper := upperFocus_spec hzt hzcrit
  have hjcon : ConsistentAt harmfuls xs false j :=
    target_consistentAt hP.2
  have hlower := lowerFocus_spec hjt hjcon
  have htargetSub :
      targets (upperFocus targets xs true) ⊆ targets z :=
    criticalAt_subset_of_le hupper.2.2 hzcrit hupper.2.1
  have hharmfulSub :
      harmfuls j ⊆ harmfuls (lowerFocus harmfuls xs false) := by
    by_contra hsub
    have hlt : lowerFocus harmfuls xs false < j + 1 :=
      Nat.lt_succ_of_le hlower.2.2
    exact (hTH t hTHt (lowerFocus harmfuls xs false) hlt hsub)
      hlower.2.1
  have hv := safeValue_spec targets harmfuls hCross xs
  refine ⟨safeValue targets harmfuls hCross xs, rfl, ?_, ?_⟩
  · exact ⟨htargetSub hv.1.1, fun hx => hv.1.2 (hharmfulSub hx)⟩
  · rw [← historyObservedSample_prefix stream t]
    exact hv.2

/-- Direct Theorem 6.3 corollary for infinite targets with finite
target--harmful intersections. -/
theorem theorem_6_3_of_finite_cross_intersections
    (targets harmfuls : Generic.LanguageFamily α)
    (hTargets : ∀ i, (targets i).Infinite)
    (hIntersections : ∀ i j, (targets i ∩ harmfuls j).Finite) :
    SafelyGeneratesInfiniteDifferences
      (infiniteDifferenceGenerator targets harmfuls
        (allCrossDifferencesInfinite_of_finite_cross_intersections
          targets harmfuls hTargets hIntersections))
      targets harmfuls :=
  theorem_6_3 targets harmfuls
    (allCrossDifferencesInfinite_of_finite_cross_intersections
      targets harmfuls hTargets hIntersections)

end GenLimit.SafeGeneration
