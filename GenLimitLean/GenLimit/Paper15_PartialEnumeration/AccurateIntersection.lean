import GenLimit.Paper15_PartialEnumeration.SemiIndex

/-!
# Lemma 2.5: stable target prefix and comparable transitions

This module formalizes the deterministic finite-stabilization core of
Kleinberg--Wei, *Language Generation and Identification From Partial
Enumeration: Tight Density Bounds and Topological Characterizations*,
arXiv:2511.05295v1, Lemma 2.5.

The source first observes that the finitely many family indices through the
true target stabilize: each earlier language either contains the entire
enumerated set `E`, or is eventually made inconsistent by some presented
point.  Their stable intersection contains `E`, is infinite, and is
contained in the target.  The first part below checks this argument exactly.

For Item 2, Algorithm 1 has two eventual transition forms.  If its descending
chain is unchanged, the old and new identified intersections occupy adjacent
positions on one chain.  If the chain changes after a positive stable prefix,
the new intersection equals a member of the old chain.  In either case the
two identified intersections are comparable by inclusion.  The second part
encodes those source transition rules and proves their finite-step and
eventual comparability conclusions.

The remaining Item 3 assertion--that a full intersection occurs infinitely
often--requires the complete recursive Algorithm-1 trace and its
leftmost-nonfull elimination argument.  It is not assumed here.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration

/-! ## The stable target-prefix core of Item 1 -/

/-- Indices through the true target which contain the entire partially
enumerated set. -/
noncomputable def targetPrefixIndices
    (C : LanguageFamily) (E : Language) (z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (z + 1)).filter fun i => E ⊆ C i

@[simp] theorem mem_targetPrefixIndices
    {C : LanguageFamily} {E : Language} {z i : ℕ} :
    i ∈ targetPrefixIndices C E z ↔
      i ≤ z ∧ E ⊆ C i := by
  classical
  simp [targetPrefixIndices, Nat.lt_succ_iff]

/-- The stable intersection displayed in equations (5)--(6) of the source,
expressed over original family indices rather than the compressed list of
currently consistent languages. -/
noncomputable def targetPrefixCore
    (C : LanguageFamily) (E : Language) (z : ℕ) : Language :=
  intersectionOf C (targetPrefixIndices C E z)

theorem enumerated_subset_targetPrefixCore
    (C : LanguageFamily) (E : Language) (z : ℕ) :
    E ⊆ targetPrefixCore C E z := by
  intro u hu i hi
  exact (mem_targetPrefixIndices.mp hi).2 hu

theorem targetPrefixCore_subset_target
    {C : LanguageFamily} {E : Language} {z : ℕ}
    (hEz : E ⊆ C z) :
    targetPrefixCore C E z ⊆ C z := by
  intro u hu
  exact hu z (mem_targetPrefixIndices.mpr ⟨Nat.le_refl z, hEz⟩)

theorem targetPrefixCore_infinite
    {C : LanguageFamily} {E : Language} {z : ℕ}
    (hE : E.Infinite) :
    (targetPrefixCore C E z).Infinite :=
  hE.mono (enumerated_subset_targetPrefixCore C E z)

/-- The finite family prefix through `z` eventually consists exactly of the
indices which contain the presented set `E`.  Consequently its intersection
is the fixed target-prefix core. -/
theorem prefixIntersection_eventually_eq_targetPrefixCore
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E) :
    ∃ T, ∀ t, T ≤ t →
      prefixIntersection C stream t (z + 1) =
        targetPrefixCore C E z := by
  obtain ⟨T, hstable⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := C) (stream := stream) (E := E) hP (z + 1)
  refine ⟨T, ?_⟩
  intro t ht
  ext u
  constructor
  · intro hu i hi
    obtain ⟨hiz, hEi⟩ := mem_targetPrefixIndices.mp hi
    exact hu i (by omega)
      ((hstable t ht i (by omega)).mpr hEi)
  · intro hu i hi hconsistent
    exact hu i (mem_targetPrefixIndices.mpr
      ⟨by omega, (hstable t ht i hi).mp hconsistent⟩)

/-- Equations (4)--(6), the finite-stabilization heart of Lemma 2.5 Item 1:
eventually the prefix through the target is fixed, full, valid, and
infinite. -/
theorem lemma_2_5_stable_targetPrefix
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    ∃ T, ∀ t, T ≤ t →
      prefixIntersection C stream t (z + 1) =
          targetPrefixCore C E z ∧
        E ⊆ prefixIntersection C stream t (z + 1) ∧
        prefixIntersection C stream t (z + 1) ⊆ C z ∧
        (prefixIntersection C stream t (z + 1)).Infinite := by
  obtain ⟨T, hT⟩ :=
    prefixIntersection_eventually_eq_targetPrefixCore
      (C := C) (stream := stream) (E := E) (z := z) hP
  refine ⟨T, ?_⟩
  intro t ht
  have heq := hT t ht
  refine ⟨heq, ?_, ?_, ?_⟩
  · rw [heq]
    exact enumerated_subset_targetPrefixCore C E z
  · rw [heq]
    exact targetPrefixCore_subset_target hEz
  · rw [heq]
    exact targetPrefixCore_infinite hE

/-- The endgame used in Item 1: once Algorithm 1's identified intersection
is below the stable prefix through the true target, it is valid.  The
separate recursive-state proof must establish the displayed eventual bound. -/
theorem lemma_2_5_item_one_of_targetPrefix_bound
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hEz : E ⊆ C z)
    (identified : ℕ → Language)
    (hBound :
      ∃ T, ∀ t, T ≤ t →
        identified t ⊆
          prefixIntersection C stream t (z + 1)) :
    ∃ T, ∀ t, T ≤ t → identified t ⊆ C z := by
  obtain ⟨T, hT⟩ := hBound
  refine ⟨T, ?_⟩
  intro t ht u hu
  have htargetConsistent :
      Consistent C stream t z :=
    consistent_of_presented_subset hP hEz
  exact hT t ht hu z (by omega) htargetConsistent

/-! ## The transition-comparability core of Item 2 -/

/-- One Algorithm-1 state: a descending chain of candidate intersections
and the chain position currently identified. -/
structure IdentifiedIntersectionState where
  chain : ℕ → Language
  chosenIndex : ℕ
  descending : Antitone chain

/-- The intersection identified by one state. -/
def IdentifiedIntersectionState.identified
    (state : IdentifiedIntersectionState) : Language :=
  state.chain state.chosenIndex

/-- The two eventual transition forms in Algorithm 1.

In the unchanged-chain case, the cursor stays put or advances once.  In the
reset case, Rule 2 chooses a positive position at which the old and new
chains agree; the `k* = 0` branch has disappeared after the stable target
prefix is present. -/
inductive AlgorithmOneStep :
    IdentifiedIntersectionState →
      IdentifiedIntersectionState → Prop
  | stable
      (old new : IdentifiedIntersectionState)
      (hChain : new.chain = old.chain)
      (hIndex :
        new.chosenIndex = old.chosenIndex ∨
          new.chosenIndex = old.chosenIndex + 1) :
      AlgorithmOneStep old new
  | positiveReset
      (old new : IdentifiedIntersectionState)
      (resetIndex : ℕ)
      (hPositive : 0 < resetIndex)
      (hStable :
        old.chain resetIndex = new.chain resetIndex)
      (hChosen : new.chosenIndex = resetIndex) :
      AlgorithmOneStep old new

/-- Lemma 2.5 Item 2's one-step argument: either source transition puts both
identified intersections on the same descending chain, so they are
comparable by inclusion. -/
theorem AlgorithmOneStep.identified_comparable
    {old new : IdentifiedIntersectionState}
    (hStep : AlgorithmOneStep old new) :
    old.identified ⊆ new.identified ∨
      new.identified ⊆ old.identified := by
  cases hStep with
  | stable hChain hIndex =>
      change
        old.chain old.chosenIndex ⊆
            new.chain new.chosenIndex ∨
          new.chain new.chosenIndex ⊆
            old.chain old.chosenIndex
      rw [hChain]
      rcases hIndex with hSame | hNext
      · rw [hSame]
        exact Or.inl Set.Subset.rfl
      · rw [hNext]
        exact Or.inr (old.descending (Nat.le_succ _))
  | positiveReset resetIndex _ hStable hChosen =>
      change
        old.chain old.chosenIndex ⊆
            new.chain new.chosenIndex ∨
          new.chain new.chosenIndex ⊆
            old.chain old.chosenIndex
      rw [hChosen, ← hStable]
      rcases le_total old.chosenIndex resetIndex with hle | hle
      · exact Or.inr (old.descending hle)
      · exact Or.inl (old.descending hle)

/-- Eventual form of Lemma 2.5 Item 2.  Once every Algorithm-1 transition is
an unchanged-chain step or a positive reset, every consecutive pair of
identified intersections is inclusion-comparable. -/
theorem lemma_2_5_item_two_comparability
    (states : ℕ → IdentifiedIntersectionState)
    (hSteps :
      ∃ T, ∀ t, T ≤ t →
        AlgorithmOneStep (states t) (states (t + 1))) :
    ∃ T, ∀ t, T ≤ t →
      (states t).identified ⊆ (states (t + 1)).identified ∨
        (states (t + 1)).identified ⊆ (states t).identified := by
  obtain ⟨T, hT⟩ := hSteps
  exact ⟨T, fun t ht => (hT t ht).identified_comparable⟩

end PartialEnumeration
end KleinbergWei
end GenLimit
