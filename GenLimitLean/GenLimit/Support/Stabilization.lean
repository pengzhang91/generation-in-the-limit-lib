import GenLimit.Core.GenericGeneration
import Mathlib.Order.Minimal

/-!
# Stabilization and eventual thresholds

Paper-independent facts for combining finitely many eventual thresholds and
for sequences whose natural-number values cannot move indefinitely.
-/

namespace GenLimit.Support

/-- Finitely many explicitly indexed eventual properties have one common
threshold. -/
theorem eventually_forall_lt
    {P : ℕ → ℕ → Prop} {n : ℕ}
    (hP : ∀ i, i < n → ∃ T, ∀ t, T ≤ t → P i t) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < n → P i t := by
  induction n with
  | zero =>
      exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨T₀, hT₀⟩ := ih (fun i hi => hP i (Nat.lt_succ_of_lt hi))
      obtain ⟨T₁, hT₁⟩ := hP n (Nat.lt_succ_self n)
      refine ⟨max T₀ T₁, ?_⟩
      intro t ht i hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi | rfl
      · exact hT₀ t (le_trans (Nat.le_max_left _ _) ht) i hi
      · exact hT₁ t (le_trans (Nat.le_max_right _ _) ht)

/-- Along an exact presentation, consistency of the finite sample with one
candidate eventually agrees with containment of the whole presented set in
that candidate. -/
theorem eventually_sample_subset_iff_presented_subset
    {stream : GenLimit.Generic.Stream α}
    {presented candidate : GenLimit.Generic.Language α}
    (hPresents : GenLimit.Generic.Presents stream presented) :
    ∃ T, ∀ t, T ≤ t →
      ((↑(GenLimit.Generic.sample stream t) : Set α) ⊆ candidate ↔
        presented ⊆ candidate) := by
  classical
  by_cases hSubset : presented ⊆ candidate
  · refine ⟨0, ?_⟩
    intro t _ht
    constructor
    · intro _hConsistent
      exact hSubset
    · intro _hSubset x hx
      obtain ⟨s, _hs, rfl⟩ :=
        GenLimit.Generic.mem_sample_iff.mp hx
      exact hSubset
        (GenLimit.Generic.streamIn_of_presents hPresents ⟨s, rfl⟩)
  · obtain ⟨x, hxPresented, hxNotCandidate⟩ :=
      Set.not_subset.mp hSubset
    have hxRange : x ∈ Set.range stream := by
      rw [hPresents]
      exact hxPresented
    obtain ⟨s, hsx⟩ := hxRange
    refine ⟨s + 1, ?_⟩
    intro t hst
    constructor
    · intro hConsistent
      exfalso
      apply hxNotCandidate
      apply hConsistent
      exact GenLimit.Generic.mem_sample_iff.mpr
        ⟨s, (Nat.lt_succ_self s).trans_le hst, hsx⟩
    · intro hSubset'
      exact False.elim (hSubset hSubset')

/-- The preceding presentation-stabilization theorem can be made uniform
over any explicitly finite prefix of a candidate family. -/
theorem finite_scope_eventually_sample_subset_iff_presented_subset
    (candidates : ℕ → GenLimit.Generic.Language α)
    {stream : GenLimit.Generic.Stream α}
    {presented : GenLimit.Generic.Language α}
    (hPresents : GenLimit.Generic.Presents stream presented)
    (scope : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < scope →
      ((↑(GenLimit.Generic.sample stream t) : Set α) ⊆ candidates i ↔
        presented ⊆ candidates i) := by
  apply eventually_forall_lt
  intro i _hi
  exact eventually_sample_subset_iff_presented_subset
    (candidate := candidates i) hPresents

/-- A non-increasing natural-number sequence eventually becomes constant. -/
theorem antitone_nat_eventually_constant
    (f : ℕ → ℕ) (hf : Antitone f) :
    ∃ M, ∀ m, M ≤ m → f m = f M := by
  obtain ⟨v, ⟨M, rfl⟩, hmin⟩ :=
    Nat.lt_wfRel.wf.has_min (Set.range f) ⟨f 0, ⟨0, rfl⟩⟩
  refine ⟨M, ?_⟩
  intro m hm
  apply Nat.le_antisymm (hf hm)
  apply Nat.le_of_not_gt
  intro hlt
  exact hmin (f m) ⟨m, rfl⟩ hlt

end GenLimit.Support
