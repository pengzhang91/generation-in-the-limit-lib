import GenLimit.Paper15_PartialEnumeration.AccurateIntersection

/-!
# Algorithm 1 Rule 2: observation-separated resets

Rule 2 of Algorithm 1 chooses the largest positive position at which the old
and new descending intersection chains agree and the common intersection is
infinite.  The existence of this largest position is not automatic for two
arbitrary descending chains: they could diverge and later agree forever.

For consecutive consistency chains, however, the newly observed element
supplies the missing invariant.  At the first eliminated candidate, the old
intersection omits the new observation.  Every new consistent candidate, and
therefore every positive new intersection, contains it.  Descendingness then
separates the entire old tail from the new chain.  Thus the last stable
infinite position really is the greatest Rule-2 candidate.

This module proves that one-step fact and packages the recurrence used in
Lemma 2.5 Item 3: every such elimination reset whose stable prefix contains
the partially enumerated set produces a full identified intersection.  The
remaining global task is to construct the source's ordered consistency
chains at every time and prove its dichotomy between eventual fullness and
cofinally many elimination resets.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration

/-- A positive infinite chain position eligible for Algorithm 1 Rule 2. -/
def RuleTwoCandidate
    (old new : IdentifiedIntersectionState) (k : ℕ) : Prop :=
  0 < k ∧
    old.chain k = new.chain k ∧
    (old.chain k).Infinite

/-- The source's requested largest eligible Rule-2 position. -/
def IsGreatestRuleTwoCandidate
    (old new : IdentifiedIntersectionState) (k : ℕ) : Prop :=
  RuleTwoCandidate old new k ∧
    ∀ j, RuleTwoCandidate old new j → j ≤ k

theorem greatestRuleTwoCandidate_unique
    {old new : IdentifiedIntersectionState} {k l : ℕ}
    (hk : IsGreatestRuleTwoCandidate old new k)
    (hl : IsGreatestRuleTwoCandidate old new l) :
    k = l :=
  Nat.le_antisymm (hl.2 k hk.1) (hk.2 l hl.1)

/-- A totalized semantic implementation of Rule 2's reset index.  It returns
zero only on malformed pairs of chains for which no greatest positive
infinite common position exists. -/
noncomputable def ruleTwoResetIndex
    (old new : IdentifiedIntersectionState) : ℕ := by
  classical
  exact
    if h :
        ∃ k, IsGreatestRuleTwoCandidate old new k
      then Classical.choose h
      else 0

theorem ruleTwoResetIndex_spec
    {old new : IdentifiedIntersectionState}
    (h : ∃ k, IsGreatestRuleTwoCandidate old new k) :
    IsGreatestRuleTwoCandidate old new
      (ruleTwoResetIndex old new) := by
  rw [ruleTwoResetIndex, dif_pos h]
  exact Classical.choose_spec h

/-- The local invariant of a genuine consistency-chain change.

`boundary` is the last unchanged positive position.  The next old
intersection omits the newly observed point, whereas every positive
intersection in the new chain contains it. -/
structure ObservationSeparatedResetData
    (old new : IdentifiedIntersectionState)
    (observed : ℕ) (boundary : ℕ) : Prop where
  positive : 0 < boundary
  stable : old.chain boundary = new.chain boundary
  infinite : (old.chain boundary).Infinite
  oldNext_misses : observed ∉ old.chain (boundary + 1)
  new_contains : ∀ j, 0 < j → observed ∈ new.chain j

theorem ObservationSeparatedResetData.tail_ne
    {old new : IdentifiedIntersectionState}
    {observed boundary j : ℕ}
    (h : ObservationSeparatedResetData old new observed boundary)
    (hboundary : boundary < j) :
    old.chain j ≠ new.chain j := by
  intro heq
  have hnextLe : boundary + 1 ≤ j := by omega
  have holdMiss : observed ∉ old.chain j := by
    intro hmem
    exact h.oldNext_misses (old.descending hnextLe hmem)
  have hnewMem : observed ∈ new.chain j :=
    h.new_contains j (h.positive.trans hboundary)
  rw [← heq] at hnewMem
  exact holdMiss hnewMem

/-- Observation separation proves that the stable boundary is exactly the
largest position requested by the source's Rule 2. -/
theorem ObservationSeparatedResetData.boundary_isGreatest
    {old new : IdentifiedIntersectionState}
    {observed boundary : ℕ}
    (h : ObservationSeparatedResetData old new observed boundary) :
    IsGreatestRuleTwoCandidate old new boundary := by
  refine ⟨⟨h.positive, h.stable, h.infinite⟩, ?_⟩
  intro j hj
  by_contra hnotLe
  have hboundary : boundary < j := by omega
  exact h.tail_ne hboundary hj.2.1

theorem ObservationSeparatedResetData.exists_greatest
    {old new : IdentifiedIntersectionState}
    {observed boundary : ℕ}
    (h : ObservationSeparatedResetData old new observed boundary) :
    ∃ k, IsGreatestRuleTwoCandidate old new k :=
  ⟨boundary, h.boundary_isGreatest⟩

theorem ObservationSeparatedResetData.ruleTwoResetIndex_eq
    {old new : IdentifiedIntersectionState}
    {observed boundary : ℕ}
    (h : ObservationSeparatedResetData old new observed boundary) :
    ruleTwoResetIndex old new = boundary := by
  exact greatestRuleTwoCandidate_unique
    (ruleTwoResetIndex_spec h.exists_greatest)
    h.boundary_isGreatest

/-! ## Realization by the paper's consistency intersections -/

/-- The descending chain obtained by intersecting the consistent candidates
among the first `k` original family indices.

This is an order-preserving version of the paper's compressed list of
currently consistent languages: inconsistent original indices simply create
repeated adjacent intersections.  Those repetitions do not change any
identified language or Rule-2 boundary. -/
def consistencyIntersectionState
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (t chosenIndex : ℕ) : IdentifiedIntersectionState where
  chain := prefixIntersection C stream t
  chosenIndex := chosenIndex
  descending := by
    intro a b hab u hu i hia hconsistent
    exact hu i (lt_of_lt_of_le hia hab) hconsistent

/-- Exact local data at the first original-index candidate eliminated by the
new observation `stream t`.

The positivity premise is the eventual `k* ≥ 1` condition in Lemma 2.5.
Infinitude of the stable prefix follows in the source from its containing the
infinite partially enumerated set; it is retained explicitly here so this
local transition theorem does not assume a global recursive trace. -/
structure LeftmostEliminationData
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (t boundary : ℕ) : Prop where
  positive : 0 < boundary
  wasConsistent : Consistent C stream t boundary
  missesObservation : stream t ∉ C boundary
  earlier_survive :
    ∀ i, i < boundary →
      Consistent C stream t i → stream t ∈ C i
  stableInfinite :
    (prefixIntersection C stream t boundary).Infinite

theorem LeftmostEliminationData.earlier_consistent_iff
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {t boundary i : ℕ}
    (h : LeftmostEliminationData C stream t boundary)
    (hi : i < boundary) :
    Consistent C stream (t + 1) i ↔
      Consistent C stream t i := by
  constructor
  · intro hnew u hu
    exact hnew (sample_mono (Nat.le_succ t) hu)
  · intro hold u hu
    obtain ⟨s, hs, rfl⟩ := mem_sample_iff.mp hu
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with hst | rfl
    · exact hold (value_mem_sample hst)
    · exact h.earlier_survive i hi hold

/-- Before the first eliminated candidate, the actual consistency
intersection chain is unchanged by the new observation. -/
theorem LeftmostEliminationData.prefixIntersection_stable
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {t boundary : ℕ}
    (h : LeftmostEliminationData C stream t boundary) :
    prefixIntersection C stream t boundary =
      prefixIntersection C stream (t + 1) boundary := by
  ext u
  constructor
  · intro hu i hi hnew
    exact hu i hi ((h.earlier_consistent_iff hi).mp hnew)
  · intro hu i hi hold
    exact hu i hi ((h.earlier_consistent_iff hi).mpr hold)

/-- A leftmost genuine elimination supplies exactly the observation
separation invariant used to justify Algorithm 1's largest Rule-2 reset. -/
theorem LeftmostEliminationData.toObservationSeparatedResetData
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {t boundary oldChosen newChosen : ℕ}
    (h : LeftmostEliminationData C stream t boundary) :
    ObservationSeparatedResetData
      (consistencyIntersectionState C stream t oldChosen)
      (consistencyIntersectionState C stream (t + 1) newChosen)
      (stream t) boundary := by
  refine
    { positive := h.positive
      stable := h.prefixIntersection_stable
      infinite := h.stableInfinite
      oldNext_misses := ?_
      new_contains := ?_ }
  · intro hmem
    exact h.missesObservation
      (hmem boundary (Nat.lt_succ_self boundary) h.wasConsistent)
  · intro j _ i _ hconsistent
    exact hconsistent (value_mem_sample (Nat.lt_succ_self t))

/-- Concrete Rule-2 index theorem for the paper's actual consistency
intersections: the first newly eliminated original index is exactly the last
stable infinite prefix. -/
theorem LeftmostEliminationData.ruleTwoResetIndex_eq
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {t boundary oldChosen newChosen : ℕ}
    (h : LeftmostEliminationData C stream t boundary) :
    ruleTwoResetIndex
        (consistencyIntersectionState C stream t oldChosen)
        (consistencyIntersectionState C stream (t + 1) newChosen) =
      boundary :=
  (h.toObservationSeparatedResetData).ruleTwoResetIndex_eq

/-- A Rule-2 transition that uses the semantic largest-index selector. -/
structure ObservationSeparatedRuleTwoStep
    (old new : IdentifiedIntersectionState)
    (observed : ℕ) (boundary : ℕ) : Prop
    extends ObservationSeparatedResetData old new observed boundary where
  chosen : new.chosenIndex = ruleTwoResetIndex old new

theorem ObservationSeparatedRuleTwoStep.chosenIndex_eq
    {old new : IdentifiedIntersectionState}
    {observed boundary : ℕ}
    (h : ObservationSeparatedRuleTwoStep
      old new observed boundary) :
    new.chosenIndex = boundary :=
  h.chosen.trans h.toObservationSeparatedResetData.ruleTwoResetIndex_eq

/-- The concrete reset state chosen at a leftmost elimination is an
Algorithm-1 observation-separated Rule-2 step. -/
theorem LeftmostEliminationData.toObservationSeparatedRuleTwoStep
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {t boundary oldChosen : ℕ}
    (h : LeftmostEliminationData C stream t boundary) :
    ObservationSeparatedRuleTwoStep
      (consistencyIntersectionState C stream t oldChosen)
      (consistencyIntersectionState C stream (t + 1) boundary)
      (stream t) boundary := by
  refine
    { toObservationSeparatedResetData :=
        h.toObservationSeparatedResetData
      chosen := ?_ }
  change boundary =
    ruleTwoResetIndex
      (consistencyIntersectionState C stream t oldChosen)
      (consistencyIntersectionState C stream (t + 1) boundary)
  exact h.ruleTwoResetIndex_eq.symm

/-- The concrete observation-separated reset is one of the positive reset
steps already used for Lemma 2.5 Item 2. -/
theorem ObservationSeparatedRuleTwoStep.toAlgorithmOneStep
    {old new : IdentifiedIntersectionState}
    {observed boundary : ℕ}
    (h : ObservationSeparatedRuleTwoStep
      old new observed boundary) :
    AlgorithmOneStep old new := by
  exact AlgorithmOneStep.positiveReset
    old new boundary h.positive h.stable h.chosenIndex_eq

/-- The local heart of Lemma 2.5 Item 3: when the last stable prefix contains
the enumerated set, Rule 2 resets to a full identified intersection. -/
theorem ObservationSeparatedRuleTwoStep.identified_full
    {old new : IdentifiedIntersectionState}
    {observed boundary : ℕ} {E : Language}
    (h : ObservationSeparatedRuleTwoStep
      old new observed boundary)
    (hfull : E ⊆ old.chain boundary) :
    E ⊆ new.identified := by
  intro u hu
  change u ∈ new.chain new.chosenIndex
  rw [h.chosenIndex_eq, ← h.stable]
  exact hfull hu

/-- A concrete leftmost elimination resets the realized consistency chain to
a full intersection whenever its stable prefix contains the partially
enumerated set.  This is the exact local conclusion used in Lemma 2.5
Item 3. -/
theorem LeftmostEliminationData.reset_identified_full
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {t boundary oldChosen : ℕ} {E : Language}
    (h : LeftmostEliminationData C stream t boundary)
    (hfull : E ⊆ prefixIntersection C stream t boundary) :
    E ⊆
      (consistencyIntersectionState
        C stream (t + 1) boundary).identified := by
  exact
    (h.toObservationSeparatedRuleTwoStep
      (oldChosen := oldChosen)).identified_full hfull

/-- An identified-intersection trace is full cofinally often.  This explicit
prefix formulation is the `infinitely many t` conclusion in Item 3. -/
def FullInfinitelyOften
    (E : Language) (states : ℕ → IdentifiedIntersectionState) : Prop :=
  ∀ T, ∃ t, T ≤ t ∧ E ⊆ (states t).identified

/-- The reset branch of Item 3's recurrence.  If observation-separated
elimination resets occur beyond every time and their stable prefixes contain
`E`, then the following states are full beyond every time. -/
theorem fullInfinitelyOften_of_cofinal_elimination_resets
    (E : Language) (states : ℕ → IdentifiedIntersectionState)
    (hresets :
      ∀ T, ∃ t, T ≤ t ∧
        ∃ observed boundary,
          ObservationSeparatedRuleTwoStep
              (states t) (states (t + 1)) observed boundary ∧
            E ⊆ (states t).chain boundary) :
    FullInfinitelyOften E states := by
  intro T
  obtain ⟨t, ht, observed, boundary, hstep, hfull⟩ :=
    hresets T
  refine ⟨t + 1, by omega, ?_⟩
  exact hstep.identified_full hfull

/-- The complete logical recurrence of Item 3.  The source proof splits into
eventual fullness or cofinally many leftmost-nonfull eliminations; the latter
branch is discharged by the preceding transition theorem. -/
theorem lemma_2_5_item_three_recurrence
    (E : Language) (states : ℕ → IdentifiedIntersectionState)
    (hdichotomy :
      (∃ T, ∀ t, T ≤ t → E ⊆ (states t).identified) ∨
        (∀ T, ∃ t, T ≤ t ∧
          ∃ observed boundary,
            ObservationSeparatedRuleTwoStep
                (states t) (states (t + 1)) observed boundary ∧
              E ⊆ (states t).chain boundary)) :
    FullInfinitelyOften E states := by
  rcases hdichotomy with heventual | hresets
  · obtain ⟨T₀, hT₀⟩ := heventual
    intro T
    refine ⟨max T T₀, Nat.le_max_left _ _, ?_⟩
    exact hT₀ _ (Nat.le_max_right _ _)
  · exact fullInfinitelyOften_of_cofinal_elimination_resets
      E states hresets

end PartialEnumeration
end KleinbergWei
end GenLimit
