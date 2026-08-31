import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.TargetAncestor

/-!
# Frozen-origin parent-forest frames

This module isolates the smallest typed interface needed to keep a
rank-climb argument in one parent forest while the observation round advances.
It deliberately does not assert that dynamic parent edges persist.
-/

namespace GenLimit
namespace KleinbergWei
namespace DensityMeasures
namespace FiniteRankParent

open TowerTopology

/-- Regard a vertex remaining at the later round `t` as a vertex of the
earlier forest at round `s`. -/
def pullbackRemaining
    {C : LanguageFamily} {stream : ℕ → ℕ} {s t : ℕ}
    (hst : s ≤ t) (vertex : RemainingPoint C stream t) :
    RemainingPoint C stream s :=
  ⟨vertex.1, remainingAt_of_later hst vertex.2⟩

@[simp] theorem pullbackRemaining_val
    {C : LanguageFamily} {stream : ℕ → ℕ} {s t : ℕ}
    (hst : s ≤ t) (vertex : RemainingPoint C stream t) :
    (pullbackRemaining hst vertex).1 = vertex.1 :=
  rfl

@[simp] theorem pullbackRemaining_self
    {C : LanguageFamily} {stream : ℕ → ℕ} {round : ℕ}
    (vertex : RemainingPoint C stream round) :
    pullbackRemaining (Nat.le_refl round) vertex = vertex := by
  apply Subtype.ext
  rfl

/-- A frame whose rank evolution is certified entirely in its origin forest.

`originToCurrent` says that the later `current` language, pulled back to the
origin round, is an ancestor (possibly equal) of `origin`.  Thus repeated
updates can accumulate a genuine same-forest parent path without assuming
that parent edges survive forest rebuilding. -/
structure FrozenFrame
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (originRound currentRound : ℕ) where
  round_le : originRound ≤ currentRound
  origin : RemainingPoint C stream originRound
  current : RemainingPoint C stream currentRound
  originToCurrent :
    AncestorAt C stream r hr originRound origin
      (pullbackRemaining round_le current)

/-- The reflexive frame at a chosen origin vertex. -/
def FrozenFrame.initial
    {C : LanguageFamily} {stream : ℕ → ℕ} {r round : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    (vertex : RemainingPoint C stream round) :
    FrozenFrame C stream r hr round round where
  round_le := Nat.le_refl round
  origin := vertex
  current := vertex
  originToCurrent := by
    simpa using ancestorAt_refl vertex

theorem FrozenFrame.level_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound currentRound : ℕ}
    (frame :
      FrozenFrame C stream r hr originRound currentRound) :
    levelOf hr frame.origin.1 ≤ levelOf hr frame.current.1 := by
  simpa using ancestorAt_level_le frame.originToCurrent

/-- A common ancestor in the frozen origin forest still remains at the later
round whenever it contains a vertex which remains at that later round. -/
theorem commonAncestor_remainingAt_later
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound laterRound : ℕ}
    (horiginLater : originRound ≤ laterRound)
    (later : RemainingPoint C stream laterRound)
    (common : RemainingPoint C stream originRound)
    (hlaterCommon :
      AncestorAt C stream r hr originRound
        (pullbackRemaining horiginLater later) common) :
    RemainingAt C stream laterRound common.1 := by
  intro x hx
  exact (ancestorAt_subset hlaterCommon) (later.2 hx)

/-- Retype an origin-forest common ancestor as a vertex at a later round. -/
def commonAtLater
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound laterRound : ℕ}
    (horiginLater : originRound ≤ laterRound)
    (later : RemainingPoint C stream laterRound)
    (common : RemainingPoint C stream originRound)
    (hlaterCommon :
      AncestorAt C stream r hr originRound
        (pullbackRemaining horiginLater later) common) :
    RemainingPoint C stream laterRound :=
  ⟨common.1,
    commonAncestor_remainingAt_later
      horiginLater later common hlaterCommon⟩

@[simp] theorem commonAtLater_val
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound laterRound : ℕ}
    (horiginLater : originRound ≤ laterRound)
    (later : RemainingPoint C stream laterRound)
    (common : RemainingPoint C stream originRound)
    (hlaterCommon :
      AncestorAt C stream r hr originRound
        (pullbackRemaining horiginLater later) common) :
    (commonAtLater horiginLater later common hlaterCommon).1 =
      common.1 :=
  rfl

@[simp] theorem pullbackRemaining_commonAtLater
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound laterRound : ℕ}
    (horiginLater : originRound ≤ laterRound)
    (later : RemainingPoint C stream laterRound)
    (common : RemainingPoint C stream originRound)
    (hlaterCommon :
      AncestorAt C stream r hr originRound
        (pullbackRemaining horiginLater later) common) :
    pullbackRemaining horiginLater
        (commonAtLater horiginLater later common hlaterCommon) =
      common := by
  apply Subtype.ext
  rfl

/-- At a fixed stabilized origin round, every later remaining language which
is target-valid still reaches the target in the frozen origin forest. -/
theorem target_ancestor_of_pullback_at_stable_origin
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound laterRound : ℕ}
    (hP : Presents stream (C z))
    (horiginLater : originRound ≤ laterRound)
    (hcritical : StrictCritical C stream (originRound + 1) z)
    (hzorigin : z < originRound)
    (hpurge :
      ∀ L : FamilyPoint C,
        L.1 ⊂ C z →
          levelOf hr (familyPoint C z) ≤ levelOf hr L →
            ¬ RemainingAt C stream originRound L)
    (later : RemainingPoint C stream laterRound)
    (hlaterTarget : later.1.1 ⊆ C z) :
    AncestorAt C stream r hr originRound
      (pullbackRemaining horiginLater later)
      (targetRemainingPoint hP originRound) := by
  let child := pullbackRemaining horiginLater later
  change
    AncestorAt C stream r hr originRound child
      (targetRemainingPoint hP originRound)
  by_cases heq : child.1.1 = C z
  · have hchildTarget :
        child = targetRemainingPoint hP originRound := by
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    rw [hchildTarget]
  · have hchildSubset : child.1.1 ⊆ C z := by
      simpa [child] using hlaterTarget
    have hchildProper : child.1.1 ⊂ C z :=
      Set.ssubset_iff_subset_ne.mpr
        ⟨hchildSubset, heq⟩
    have hchildLevel :
        levelOf hr child.1 < levelOf hr (familyPoint C z) := by
      apply Nat.lt_of_not_ge
      intro hge
      exact hpurge child.1 hchildProper hge child.2
    exact
      (reaches_target_at_stable_round
        hP hcritical hzorigin hpurge
        child hchildProper hchildLevel).to_reflTransGen

/-- Advance a frame to a later round through a common ancestor chosen in the
same frozen origin forest.  The returned anchor is proved remaining at the
later round rather than assumed to be. -/
def FrozenFrame.advanceWith
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound currentRound laterRound : ℕ}
    (frame :
      FrozenFrame C stream r hr originRound currentRound)
    (hcurrentLater : currentRound ≤ laterRound)
    (later : RemainingPoint C stream laterRound)
    (common : RemainingPoint C stream originRound)
    (hcurrentCommon :
      AncestorAt C stream r hr originRound
        (pullbackRemaining frame.round_le frame.current) common)
    (hlaterCommon :
      AncestorAt C stream r hr originRound
        (pullbackRemaining
          (frame.round_le.trans hcurrentLater) later) common) :
    FrozenFrame C stream r hr originRound laterRound where
  round_le := frame.round_le.trans hcurrentLater
  origin := frame.origin
  current :=
    commonAtLater
      (frame.round_le.trans hcurrentLater)
      later common hlaterCommon
  originToCurrent := by
    rw [pullbackRemaining_commonAtLater]
    exact ancestorAt_trans frame.originToCurrent hcurrentCommon

/-- The minimum common ancestor of two vertices in one finite-rank forest. -/
noncomputable def minimumCommonAncestorAt
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ}
    (a b : RemainingPoint C stream round)
    (hne :
      (commonAncestorSet C stream r hr round a b).Nonempty) :
    RemainingPoint C stream round :=
  Classical.choose
    (exists_inclusion_minimum_commonAncestor hne)

theorem minimumCommonAncestorAt_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ}
    (a b : RemainingPoint C stream round)
    (hne :
      (commonAncestorSet C stream r hr round a b).Nonempty) :
    minimumCommonAncestorAt a b hne ∈
        commonAncestorSet C stream r hr round a b ∧
      ∀ w,
        w ∈ commonAncestorSet C stream r hr round a b →
          (minimumCommonAncestorAt a b hne).1.1 ⊆ w.1.1 :=
  Classical.choose_spec
    (exists_inclusion_minimum_commonAncestor hne)

/-- Canonically advance a frozen frame by choosing the inclusion-minimum
common ancestor of its current anchor and the later vertex in the origin
forest. -/
noncomputable def FrozenFrame.advance
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound currentRound laterRound : ℕ}
    (frame :
      FrozenFrame C stream r hr originRound currentRound)
    (hcurrentLater : currentRound ≤ laterRound)
    (later : RemainingPoint C stream laterRound)
    (hne :
      (commonAncestorSet C stream r hr originRound
        (pullbackRemaining frame.round_le frame.current)
        (pullbackRemaining
          (frame.round_le.trans hcurrentLater) later)).Nonempty) :
    FrozenFrame C stream r hr originRound laterRound := by
  let laterAtOrigin :=
    pullbackRemaining
      (frame.round_le.trans hcurrentLater) later
  let common :=
    minimumCommonAncestorAt
      (pullbackRemaining frame.round_le frame.current)
      laterAtOrigin hne
  have hspec :=
    (minimumCommonAncestorAt_spec
      (pullbackRemaining frame.round_le frame.current)
      laterAtOrigin hne).1
  exact
    frame.advanceWith hcurrentLater later common hspec.1 hspec.2

/-- In one fixed parent forest, a common ancestor of `fallback` and an
escaping `newGuess` must be a proper ancestor of `fallback`, hence has
strictly larger level. -/
theorem sameForest_strictLevelClimb
    {C : LanguageFamily} {stream : ℕ → ℕ} {r round : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {fallback newGuess common : RemainingPoint C stream round}
    (hfallback :
      AncestorAt C stream r hr round fallback common)
    (hnewGuess :
      AncestorAt C stream r hr round newGuess common)
    (hescape :
      ¬ AncestorAt C stream r hr round newGuess fallback) :
    ProperAncestorAt C stream r hr round fallback common ∧
      levelOf hr fallback.1 < levelOf hr common.1 := by
  have hne : fallback ≠ common := by
    intro heq
    subst common
    exact hescape hnewGuess
  have hproper :
      ProperAncestorAt C stream r hr round fallback common := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hfallback with
      heq | hpath
    · exact (hne heq.symm).elim
    · exact hpath
  exact ⟨hproper, (properAncestorAt_strict hproper).1⟩

/-- If the later vertex escapes the current anchor, the canonical
inclusion-minimum common-ancestor update advances to a strictly higher level
while preserving one frozen origin forest. -/
theorem FrozenFrame.exists_strictAdvance
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound currentRound laterRound : ℕ}
    (frame :
      FrozenFrame C stream r hr originRound currentRound)
    (hcurrentLater : currentRound ≤ laterRound)
    (later : RemainingPoint C stream laterRound)
    (hne :
      (commonAncestorSet C stream r hr originRound
        (pullbackRemaining frame.round_le frame.current)
        (pullbackRemaining
          (frame.round_le.trans hcurrentLater) later)).Nonempty)
    (hescape :
      ¬ AncestorAt C stream r hr originRound
        (pullbackRemaining
          (frame.round_le.trans hcurrentLater) later)
        (pullbackRemaining frame.round_le frame.current)) :
    ∃ nextFrame :
        FrozenFrame C stream r hr originRound laterRound,
      levelOf hr frame.current.1 <
        levelOf hr nextFrame.current.1 := by
  let currentAtOrigin :=
    pullbackRemaining frame.round_le frame.current
  let laterAtOrigin :=
    pullbackRemaining
      (frame.round_le.trans hcurrentLater) later
  let common :=
    minimumCommonAncestorAt currentAtOrigin laterAtOrigin hne
  have hspec :=
    (minimumCommonAncestorAt_spec
      currentAtOrigin laterAtOrigin hne).1
  let nextFrame :=
    frame.advanceWith hcurrentLater later common hspec.1 hspec.2
  refine ⟨nextFrame, ?_⟩
  have hclimb :=
    (sameForest_strictLevelClimb
      hspec.1 hspec.2 hescape).2
  simpa [currentAtOrigin, common, nextFrame,
    FrozenFrame.advanceWith, commonAtLater] using hclimb

/-- At a stabilized origin, target-valid current and later vertices have the
target itself as a common ancestor in the frozen origin forest.  Hence an
escape from the current anchor produces an actual strictly advancing frame,
without any cross-round persistence premise. -/
theorem FrozenFrame.exists_strictAdvance_of_target
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {originRound currentRound laterRound : ℕ}
    (hP : Presents stream (C z))
    (hcritical : StrictCritical C stream (originRound + 1) z)
    (hzorigin : z < originRound)
    (hpurge :
      ∀ L : FamilyPoint C,
        L.1 ⊂ C z →
          levelOf hr (familyPoint C z) ≤ levelOf hr L →
            ¬ RemainingAt C stream originRound L)
    (frame :
      FrozenFrame C stream r hr originRound currentRound)
    (hcurrentLater : currentRound ≤ laterRound)
    (later : RemainingPoint C stream laterRound)
    (hcurrentTarget : frame.current.1.1 ⊆ C z)
    (hlaterTarget : later.1.1 ⊆ C z)
    (hescape :
      ¬ AncestorAt C stream r hr originRound
        (pullbackRemaining
          (frame.round_le.trans hcurrentLater) later)
        (pullbackRemaining frame.round_le frame.current)) :
    ∃ nextFrame :
        FrozenFrame C stream r hr originRound laterRound,
      levelOf hr frame.current.1 <
          levelOf hr nextFrame.current.1 ∧
        nextFrame.current.1.1 ⊆ C z := by
  have hcurrentAncestor :
      AncestorAt C stream r hr originRound
        (pullbackRemaining frame.round_le frame.current)
        (targetRemainingPoint hP originRound) :=
    target_ancestor_of_pullback_at_stable_origin
      hP frame.round_le hcritical hzorigin hpurge
      frame.current hcurrentTarget
  have hlaterAncestor :
      AncestorAt C stream r hr originRound
        (pullbackRemaining
          (frame.round_le.trans hcurrentLater) later)
        (targetRemainingPoint hP originRound) :=
    target_ancestor_of_pullback_at_stable_origin
      hP (frame.round_le.trans hcurrentLater)
      hcritical hzorigin hpurge later hlaterTarget
  have hcommon :
      (commonAncestorSet C stream r hr originRound
        (pullbackRemaining frame.round_le frame.current)
        (pullbackRemaining
          (frame.round_le.trans hcurrentLater) later)).Nonempty := by
    refine ⟨targetRemainingPoint hP originRound, ?_, ?_⟩
    · exact hcurrentAncestor
    · exact hlaterAncestor
  let currentAtOrigin :=
    pullbackRemaining frame.round_le frame.current
  let laterAtOrigin :=
    pullbackRemaining
      (frame.round_le.trans hcurrentLater) later
  let common :=
    minimumCommonAncestorAt currentAtOrigin laterAtOrigin hcommon
  have hspec :=
    (minimumCommonAncestorAt_spec
      currentAtOrigin laterAtOrigin hcommon)
  have hcommonTarget :
      common.1.1 ⊆ C z := by
    have hminimum :=
      hspec.2
        (targetRemainingPoint hP originRound)
        ⟨hcurrentAncestor, hlaterAncestor⟩
    exact hminimum
  let nextFrame :=
    frame.advanceWith hcurrentLater later common
      hspec.1.1 hspec.1.2
  refine ⟨nextFrame, ?_, ?_⟩
  · have hclimb :=
      (sameForest_strictLevelClimb
        hspec.1.1 hspec.1.2 hescape).2
    simpa [currentAtOrigin, common, nextFrame,
      FrozenFrame.advanceWith, commonAtLater] using hclimb
  · simpa [nextFrame, FrozenFrame.advanceWith,
      commonAtLater] using hcommonTarget

/-- A language-level escape is sufficient for the same strict-climb
conclusion, since every ancestor path grows by inclusion. -/
theorem sameForest_strictLevelClimb_of_not_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {r round : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {fallback newGuess common : RemainingPoint C stream round}
    (hfallback :
      AncestorAt C stream r hr round fallback common)
    (hnewGuess :
      AncestorAt C stream r hr round newGuess common)
    (hescape : ¬ newGuess.1.1 ⊆ fallback.1.1) :
    ProperAncestorAt C stream r hr round fallback common ∧
      levelOf hr fallback.1 < levelOf hr common.1 := by
  apply sameForest_strictLevelClimb hfallback hnewGuess
  intro hancestor
  exact hescape (ancestorAt_subset hancestor)

end FiniteRankParent
end DensityMeasures
end KleinbergWei
end GenLimit
