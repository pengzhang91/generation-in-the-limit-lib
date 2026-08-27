import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.TargetAncestor
import GenLimit.Core.OrderedDensity
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

/-!
# Finite-rank fallback and output state

This file formalizes Corollary 6.10 and the normalized state infrastructure
used by Claim 6.11 of Kleinberg and Wei.

Source-time normalization:

* Lean forest round `t` is source round `t+1`.
* A transition at Lean time `t+1` compares vertices at rounds `t` and
  `t+1`; its newly selected fallback is stored in step `t+1`.
* `badInputs` is the source's `W`; the later unexplained `M` is read as
  the same set.
* Claim 6.11's consistent bound is no `r+1` consecutive bad target
  positions.  The later phrase “no `r` consecutive” is an off-by-one typo.

The source leaves “unused” and queue initialization implicit and repeats its
output instruction.  The normalized state starts with an empty queue, records
all strings used by either player, purges used strings at each step, and emits
the least fresh member of the queue union the current identified language.
The construction assumes, as the paper does globally, that every family
language is infinite.

The dynamic implication from a bad run to a strict rank climb is not asserted
here: the printed proof assumes parent ancestry persists across changing
forests, an invariant not supplied by the time-ranked parent selector.
The final natural-number comparisons additionally require the target
enumeration to inherit the ambient natural order; `OrderedLanguage` itself
only records an arbitrary duplicate-free enumeration.
-/

namespace GenLimit
namespace KleinbergWei
namespace DensityMeasures
namespace FiniteRankFallback

open TowerTopology
open FiniteRankParent

/-- Reflexive ancestry in one remaining-language parent forest. -/
abbrev AncestorOrSelfAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (round : ℕ)
    (child ancestor :
      FiniteRankParent.RemainingPoint C stream round) : Prop :=
  FiniteRankParent.AncestorAt
    C stream r hr round child ancestor

/-- A family point is an ancestor of a vertex at a given round.  The
existential remaining proof lets one compare languages across two rounds
without identifying their proof-dependent subtype types. -/
def IsAncestorLanguageAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (round : ℕ)
    (child : FiniteRankParent.RemainingPoint C stream round)
    (ancestor : FiniteRankParent.FamilyPoint C) : Prop :=
  ∃ hremaining : FiniteRankParent.RemainingAt C stream round ancestor,
    AncestorOrSelfAt C stream r hr round child
      ⟨ancestor, hremaining⟩

/-- A language which is an ancestor in both forests adjacent to a
transition. -/
def IsCommonAncestorAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (round : ℕ)
    (current : FiniteRankParent.RemainingPoint C stream round)
    (next :
      FiniteRankParent.RemainingPoint C stream (round + 1))
    (ancestor : FiniteRankParent.FamilyPoint C) : Prop :=
  IsAncestorLanguageAt C stream r hr round current ancestor ∧
    IsAncestorLanguageAt C stream r hr (round + 1) next ancestor

/-- Inclusion grows along every reflexive parent path. -/
theorem reflTransGen_edge_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    {child ancestor :
      FiniteRankParent.RemainingPoint C stream round}
    (hpath : AncestorOrSelfAt C stream r hr round child ancestor) :
    child.1.1 ⊆ ancestor.1.1 :=
  FiniteRankParent.ancestorAt_subset hpath

/-- Level does not decrease along reflexive parent paths. -/
theorem reflTransGen_edge_level_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    {child ancestor :
      FiniteRankParent.RemainingPoint C stream round}
    (hpath : AncestorOrSelfAt C stream r hr round child ancestor) :
    FiniteRankParent.levelOf hr child.1 ≤
      FiniteRankParent.levelOf hr ancestor.1 :=
  FiniteRankParent.ancestorAt_level_le hpath

/-- Two ancestors of one vertex are comparable, since the parent relation
has functional outdegree. -/
theorem ancestors_comparable
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    {child :
      FiniteRankParent.RemainingPoint C stream round}
    {ancestor₁ ancestor₂ : FiniteRankParent.FamilyPoint C}
    (h₁ :
      IsAncestorLanguageAt C stream r hr round child ancestor₁)
    (h₂ :
      IsAncestorLanguageAt C stream r hr round child ancestor₂) :
    ancestor₁.1 ⊆ ancestor₂.1 ∨ ancestor₂.1 ⊆ ancestor₁.1 := by
  rcases h₁ with ⟨hrem₁, hpath₁⟩
  rcases h₂ with ⟨hrem₂, hpath₂⟩
  rcases
      FiniteRankParent.ancestors_comparable
        hpath₁ hpath₂ with
    h₁₂ | h₂₁
  · exact Or.inl (reflTransGen_edge_subset h₁₂)
  · exact Or.inr (reflTransGen_edge_subset h₂₁)

/-- The set of levels represented among common ancestors. -/
def CommonAncestorLevel
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (round : ℕ)
    (current : FiniteRankParent.RemainingPoint C stream round)
    (next :
      FiniteRankParent.RemainingPoint C stream (round + 1))
    (level : ℕ) : Prop :=
  ∃ ancestor : FiniteRankParent.FamilyPoint C,
    IsCommonAncestorAt C stream r hr round current next ancestor ∧
      FiniteRankParent.levelOf hr ancestor = level

/-- The least level at which the two vertices have a common ancestor. -/
noncomputable def leastCommonAncestorLevel
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (round : ℕ)
    (current : FiniteRankParent.RemainingPoint C stream round)
    (next :
      FiniteRankParent.RemainingPoint C stream (round + 1))
    (hexists :
      ∃ ancestor,
        IsCommonAncestorAt C stream r hr round current next ancestor) :
    ℕ := by
  classical
  exact Nat.find (show ∃ level,
    CommonAncestorLevel C stream r hr round current next level by
      obtain ⟨ancestor, hancestor⟩ := hexists
      exact
        ⟨FiniteRankParent.levelOf hr ancestor,
          ancestor, hancestor, rfl⟩)

/-- The normalized smallest common ancestor: first minimize its finite
Cantor--Bendixson level, then choose a witness at that level. -/
noncomputable def leastCommonAncestor
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (round : ℕ)
    (current : FiniteRankParent.RemainingPoint C stream round)
    (next :
      FiniteRankParent.RemainingPoint C stream (round + 1))
    (hexists :
      ∃ ancestor,
        IsCommonAncestorAt C stream r hr round current next ancestor) :
    FiniteRankParent.FamilyPoint C := by
  classical
  exact Classical.choose
    (Nat.find_spec
      (show ∃ level,
        CommonAncestorLevel C stream r hr round current next level by
          obtain ⟨ancestor, hancestor⟩ := hexists
          exact
            ⟨FiniteRankParent.levelOf hr ancestor,
              ancestor, hancestor, rfl⟩))

theorem leastCommonAncestor_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    {current : FiniteRankParent.RemainingPoint C stream round}
    {next :
      FiniteRankParent.RemainingPoint C stream (round + 1)}
    (hexists :
      ∃ ancestor,
        IsCommonAncestorAt C stream r hr round current next ancestor) :
    IsCommonAncestorAt C stream r hr round current next
      (leastCommonAncestor C stream r hr round current next hexists) ∧
    FiniteRankParent.levelOf hr
        (leastCommonAncestor C stream r hr round current next hexists) =
      leastCommonAncestorLevel
        C stream r hr round current next hexists := by
  classical
  exact Classical.choose_spec
    (Nat.find_spec
      (show ∃ level,
        CommonAncestorLevel C stream r hr round current next level by
          obtain ⟨ancestor, hancestor⟩ := hexists
          exact
            ⟨FiniteRankParent.levelOf hr ancestor,
              ancestor, hancestor, rfl⟩))

theorem leastCommonAncestor_level_min
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    {current : FiniteRankParent.RemainingPoint C stream round}
    {next :
      FiniteRankParent.RemainingPoint C stream (round + 1)}
    (hexists :
      ∃ ancestor,
        IsCommonAncestorAt C stream r hr round current next ancestor)
    {ancestor : FiniteRankParent.FamilyPoint C}
    (hancestor :
      IsCommonAncestorAt C stream r hr round current next ancestor) :
    leastCommonAncestorLevel
        C stream r hr round current next hexists ≤
      FiniteRankParent.levelOf hr ancestor := by
  classical
  unfold leastCommonAncestorLevel
  apply Nat.find_min'
  exact ⟨ancestor, hancestor, rfl⟩

/-- Minimizing level really gives the source's inclusion-minimum common
ancestor. -/
theorem leastCommonAncestor_inclusion_minimum
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    {current : FiniteRankParent.RemainingPoint C stream round}
    {next :
      FiniteRankParent.RemainingPoint C stream (round + 1)}
    (hexists :
      ∃ ancestor,
        IsCommonAncestorAt C stream r hr round current next ancestor)
    {ancestor : FiniteRankParent.FamilyPoint C}
    (hancestor :
      IsCommonAncestorAt C stream r hr round current next ancestor) :
    (leastCommonAncestor C stream r hr round current next hexists).1 ⊆
      ancestor.1 := by
  let chosen :=
    leastCommonAncestor C stream r hr round current next hexists
  have hchosen :
      IsCommonAncestorAt C stream r hr round current next chosen := by
    exact (leastCommonAncestor_spec hexists).1
  have hlevelMin :
      FiniteRankParent.levelOf hr chosen ≤
        FiniteRankParent.levelOf hr ancestor := by
    rw [(leastCommonAncestor_spec hexists).2]
    exact leastCommonAncestor_level_min hexists hancestor
  rcases hchosen.1 with ⟨hremChosen, hpathChosen⟩
  rcases hancestor.1 with ⟨hremAncestor, hpathAncestor⟩
  rcases
      FiniteRankParent.ancestors_comparable
        hpathChosen hpathAncestor with
    hChosenAncestor | hAncestorChosen
  · exact reflTransGen_edge_subset hChosenAncestor
  · rcases
        Relation.reflTransGen_iff_eq_or_transGen.mp
          hAncestorChosen with
      heq | htrans
    · have hpointEq : chosen = ancestor :=
        congrArg Subtype.val heq
      simp [chosen, hpointEq]
    · have hlevelStrict :
          FiniteRankParent.levelOf hr ancestor <
            FiniteRankParent.levelOf hr chosen :=
        FiniteRankParent.transGen_edge_level_lt htrans
      exact (not_lt_of_ge hlevelMin hlevelStrict).elim

/-- Source cases (1)--(3), normalized to a transition from `round` to
`round+1`. -/
noncomputable def fallbackChoice
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (round : ℕ)
    (current : FiniteRankParent.RemainingPoint C stream round)
    (next :
      FiniteRankParent.RemainingPoint C stream (round + 1)) :
    Option (FiniteRankParent.FamilyPoint C) := by
  classical
  if heq : current.1.1 = next.1.1 then
    exact none
  else if hdown :
      next.1.1 ⊆ current.1.1 ∧
        FiniteRankParent.levelOf hr next.1 ≠
          FiniteRankParent.levelOf hr current.1 then
    exact some next.1
  else if hcommon :
      ∃ ancestor,
        IsCommonAncestorAt C stream r hr round
          current next ancestor then
    exact some
      (leastCommonAncestor C stream r hr round
        current next hcommon)
  else
    exact none

/-- Corollary 6.10's semantic core: if the target is a common ancestor and
the next selector language is target-valid, every nontrivial transition
chooses a fallback language contained in the target. -/
theorem corollary_6_10_core
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    {current : FiniteRankParent.RemainingPoint C stream round}
    {next :
      FiniteRankParent.RemainingPoint C stream (round + 1)}
    {target : FiniteRankParent.FamilyPoint C}
    (hchanged : current.1.1 ≠ next.1.1)
    (hnextTarget : next.1.1 ⊆ target.1)
    (htargetCommon :
      IsCommonAncestorAt C stream r hr round
        current next target) :
    ∃ fallback,
      fallbackChoice C stream r hr round current next =
          some fallback ∧
        fallback.1 ⊆ target.1 := by
  classical
  rw [fallbackChoice]
  simp only [dif_neg hchanged]
  split
  next hdown =>
    exact ⟨next.1, rfl, hnextTarget⟩
  next hdown =>
    have hcommon :
        ∃ ancestor,
          IsCommonAncestorAt C stream r hr round
            current next ancestor :=
      ⟨target, htargetCommon⟩
    simp only [dif_pos hcommon]
    exact
      ⟨leastCommonAncestor C stream r hr round
          current next hcommon,
        rfl,
        leastCommonAncestor_inclusion_minimum
          hcommon htargetCommon⟩

/-- Corollary 6.10: after stabilization, every transition on which the
accurate selector changes language chooses a fallback contained in the true
target.  The returned vertices are the canonical selector values in their
respective post-observation forests. -/
theorem corollary_6_10
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ round, T ≤ round →
      ∃ current : FiniteRankParent.RemainingPoint C stream round,
        ∃ next :
            FiniteRankParent.RemainingPoint C stream (round + 1),
          current.1 =
              FiniteRankParent.identifiedPointAt C stream round ∧
            next.1 =
              FiniteRankParent.identifiedPointAt C stream (round + 1) ∧
            (current.1.1 ≠ next.1.1 →
              ∃ fallback,
                fallbackChoice C stream r hr round current next =
                    some fallback ∧
                  fallback.1 ⊆ C z) := by
  obtain ⟨Tancestor, hancestor⟩ :=
    FiniteRankParent.claim_6_8 hr hP hfirst
  obtain ⟨Tvalid, hvalid⟩ :=
    proposition_3_4 hP hfirst
  refine ⟨max Tancestor Tvalid, ?_⟩
  intro round hround
  have hTancestor : Tancestor ≤ round := by
    omega
  have hTvalid : Tvalid ≤ round + 2 := by
    omega
  obtain ⟨current, hcurrentValue, hcurrentPath⟩ :=
    hancestor round hTancestor
  obtain ⟨next, hnextValue, hnextPath⟩ :=
    hancestor (round + 1) (by omega)
  refine
    ⟨current, next, ?_, ?_, ?_⟩
  · simpa [FiniteRankParent.identifiedPointAt] using
      hcurrentValue
  · simpa [FiniteRankParent.identifiedPointAt] using
      hnextValue
  · intro hchanged
    have hnextTarget : next.1.1 ⊆ C z := by
      rw [hnextValue]
      simpa using hvalid (round + 2) hTvalid
    have htargetCommon :
        IsCommonAncestorAt C stream r hr round
          current next (FiniteRankParent.familyPoint C z) := by
      constructor
      · exact
          ⟨(FiniteRankParent.targetRemainingPoint hP round).2,
            hcurrentPath⟩
      · exact
          ⟨(FiniteRankParent.targetRemainingPoint
              hP (round + 1)).2,
            hnextPath⟩
    exact
      corollary_6_10_core
        hchanged hnextTarget htargetCommon

/-- The source fallback schedule, made total before stabilization.  Step zero
has no preceding transition.  At step `round + 1`, use the transition from
forest round `round` to `round + 1` when both selector values are vertices;
otherwise no fallback is scheduled. -/
noncomputable def canonicalFallbackAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r) :
    ℕ → Option (FiniteRankParent.FamilyPoint C)
  | 0 => none
  | round + 1 => by
      classical
      let current :=
        FiniteRankParent.identifiedPointAt C stream round
      let next :=
        FiniteRankParent.identifiedPointAt C stream (round + 1)
      exact
        if hcurrent :
            FiniteRankParent.RemainingAt C stream round current then
          if hnext :
              FiniteRankParent.RemainingAt
                C stream (round + 1) next then
            fallbackChoice C stream r hr round
              ⟨current, hcurrent⟩ ⟨next, hnext⟩
          else none
        else none

@[simp] theorem canonicalFallbackAt_zero
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r) :
    canonicalFallbackAt C stream r hr 0 = none :=
  rfl

theorem canonicalFallbackAt_succ_of_remaining
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    (hcurrent :
      FiniteRankParent.RemainingAt C stream round
        (FiniteRankParent.identifiedPointAt C stream round))
    (hnext :
      FiniteRankParent.RemainingAt C stream (round + 1)
        (FiniteRankParent.identifiedPointAt C stream (round + 1))) :
    canonicalFallbackAt C stream r hr (round + 1) =
      fallbackChoice C stream r hr round
        ⟨FiniteRankParent.identifiedPointAt C stream round,
          hcurrent⟩
        ⟨FiniteRankParent.identifiedPointAt C stream (round + 1),
          hnext⟩ := by
  classical
  simp [canonicalFallbackAt, hcurrent, hnext]

/-- The total canonical fallback schedule inherits Corollary 6.10: once the
selector stabilizes into the finite-rank forest, every changed transition
schedules a target-valid fallback at the following output step. -/
theorem canonicalFallbackAt_eventually_valid
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ round, T ≤ round →
      (FiniteRankParent.identifiedPointAt C stream round).1 ≠
          (FiniteRankParent.identifiedPointAt
            C stream (round + 1)).1 →
        ∃ fallback,
          canonicalFallbackAt C stream r hr (round + 1) =
              some fallback ∧
            fallback.1 ⊆ C z := by
  obtain ⟨T, hT⟩ :=
    corollary_6_10 hr hP hfirst
  refine ⟨T, ?_⟩
  intro round hround hchanged
  obtain
      ⟨current, next, hcurrentValue, hnextValue,
        htransition⟩ :=
    hT round hround
  have hcurrentRemaining :
      FiniteRankParent.RemainingAt C stream round
        (FiniteRankParent.identifiedPointAt C stream round) := by
    rw [← hcurrentValue]
    exact current.2
  have hnextRemaining :
      FiniteRankParent.RemainingAt C stream (round + 1)
        (FiniteRankParent.identifiedPointAt C stream (round + 1)) := by
    rw [← hnextValue]
    exact next.2
  have hcurrentEq :
      (⟨FiniteRankParent.identifiedPointAt C stream round,
          hcurrentRemaining⟩ :
        FiniteRankParent.RemainingPoint C stream round) =
          current := by
    apply Subtype.ext
    exact hcurrentValue.symm
  have hnextEq :
      (⟨FiniteRankParent.identifiedPointAt C stream (round + 1),
          hnextRemaining⟩ :
        FiniteRankParent.RemainingPoint C stream (round + 1)) =
          next := by
    apply Subtype.ext
    exact hnextValue.symm
  have hchanged' : current.1.1 ≠ next.1.1 := by
    intro heq
    apply hchanged
    rw [← hcurrentValue, ← hnextValue]
    exact heq
  obtain ⟨fallback, hfallback, hsubset⟩ :=
    htransition hchanged'
  refine ⟨fallback, ?_, hsubset⟩
  rw [canonicalFallbackAt_succ_of_remaining
    hcurrentRemaining hnextRemaining]
  simpa [hcurrentEq, hnextEq] using hfallback

/-! ## Normalized fallback/output queue -/

/-- Every family point denotes an infinite language under the paper's
standing assumption that every member of the family is infinite. -/
theorem familyPoint_infinite
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (L : FiniteRankParent.FamilyPoint C) :
    L.1.Infinite := by
  rcases L.2 with ⟨n, hn⟩
  simpa [← hn] using hInfinite n

/-- The first member of an infinite language strictly above `bound`. -/
noncomputable def nextAbove
    (L : Language) (hInfinite : L.Infinite) (bound : ℕ) : ℕ := by
  classical
  exact Nat.find (hInfinite.exists_gt bound)

theorem nextAbove_spec
    (L : Language) (hInfinite : L.Infinite) (bound : ℕ) :
    nextAbove L hInfinite bound ∈ L ∧
      bound < nextAbove L hInfinite bound := by
  classical
  exact Nat.find_spec (hInfinite.exists_gt bound)

theorem nextAbove_min
    (L : Language) (hInfinite : L.Infinite) (bound x : ℕ)
    (hxL : x ∈ L) (hbound : bound < x) :
    nextAbove L hInfinite bound ≤ x := by
  classical
  exact Nat.find_min' (hInfinite.exists_gt bound) ⟨hxL, hbound⟩

/-- The second fresh language member above the largest string used so far,
the source's `Succ_L(w')`. -/
noncomputable def secondAbove
    (L : Language) (hInfinite : L.Infinite) (bound : ℕ) : ℕ :=
  nextAbove L hInfinite (nextAbove L hInfinite bound)

theorem secondAbove_spec
    (L : Language) (hInfinite : L.Infinite) (bound : ℕ) :
    secondAbove L hInfinite bound ∈ L ∧
      nextAbove L hInfinite bound <
        secondAbove L hInfinite bound :=
  nextAbove_spec L hInfinite (nextAbove L hInfinite bound)

/-- The strings inserted on a fallback: every currently unused member of
the fallback language through the second member above the current maximum. -/
noncomputable def fallbackWindow
    (L : Language) (hInfinite : L.Infinite)
    (used : Finset ℕ) (hused : used.Nonempty) : Finset ℕ := by
  classical
  let bound := used.max' hused
  exact
    (Finset.range (secondAbove L hInfinite bound + 1)).filter
      fun x => x ∈ L ∧ x ∉ used

@[simp] theorem mem_fallbackWindow
    {L : Language} {hInfinite : L.Infinite}
    {used : Finset ℕ} {hused : used.Nonempty} {x : ℕ} :
    x ∈ fallbackWindow L hInfinite used hused ↔
      x ≤ secondAbove L hInfinite (used.max' hused) ∧
        x ∈ L ∧ x ∉ used := by
  classical
  simp [fallbackWindow, Nat.lt_succ_iff]

/-- Candidate condition for the next output. -/
def OutputCandidate
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (x : ℕ) : Prop :=
  x ∉ used ∧ (x ∈ preferred ∨ x ∈ current)

theorem outputCandidate_exists
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hInfinite : current.Infinite) :
    ∃ x, OutputCandidate preferred current used x := by
  obtain ⟨x, hxCurrent, hxFresh⟩ :=
    hInfinite.exists_notMem_finset used
  exact ⟨x, hxFresh, Or.inr hxCurrent⟩

/-- The smallest unused string in the priority queue union the currently
identified language. -/
noncomputable def leastOutput
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hInfinite : current.Infinite) : ℕ := by
  classical
  exact Nat.find
    (outputCandidate_exists preferred current used hInfinite)

theorem leastOutput_spec
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hInfinite : current.Infinite) :
    OutputCandidate preferred current used
      (leastOutput preferred current used hInfinite) := by
  classical
  exact Nat.find_spec
    (outputCandidate_exists preferred current used hInfinite)

theorem leastOutput_min
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hInfinite : current.Infinite)
    {x : ℕ} (hx : OutputCandidate preferred current used x) :
    leastOutput preferred current used hInfinite ≤ x := by
  classical
  exact Nat.find_min'
    (outputCandidate_exists preferred current used hInfinite) hx

/-- State immediately before an adversary/algorithm round. -/
structure OutputState where
  /-- All strings previously used by either player. -/
  used : Finset ℕ
  /-- Unused strings currently carrying fallback priority. -/
  queue : Finset ℕ
  /-- The preceding algorithm output, absent only initially. -/
  previousOutput : Option ℕ

/-- The empty pre-round state. -/
def OutputState.initial : OutputState :=
  ⟨∅, ∅, none⟩

/-- Purge used strings from the old queue and, on a fallback transition,
insert the source's finite two-successor window. -/
noncomputable def priorityAtStep
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (fallback : Option (FiniteRankParent.FamilyPoint C)) :
    Finset ℕ := by
  classical
  let usedNow := insert input state.used
  have husedNow : usedNow.Nonempty :=
    ⟨input, Finset.mem_insert_self input state.used⟩
  let oldQueue := state.queue \ usedNow
  let additions :=
    match fallback with
    | none => ∅
    | some L =>
        fallbackWindow L.1 (familyPoint_infinite hInfinite L)
          usedNow husedNow
  exact oldQueue ∪ additions

/-- One normalized interaction step. -/
noncomputable def outputStep
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current : FiniteRankParent.FamilyPoint C)
    (fallback : Option (FiniteRankParent.FamilyPoint C)) :
    OutputState := by
  classical
  let usedNow := insert input state.used
  let preferred :=
    priorityAtStep hInfinite state input fallback
  let output :=
    leastOutput preferred current.1 usedNow
      (familyPoint_infinite hInfinite current)
  exact
    ⟨insert output usedNow, preferred.erase output, some output⟩

/-- The output emitted by one normalized step. -/
noncomputable def emittedAtStep
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current : FiniteRankParent.FamilyPoint C)
    (fallback : Option (FiniteRankParent.FamilyPoint C)) : ℕ :=
  leastOutput
    (priorityAtStep hInfinite state input fallback)
    current.1 (insert input state.used)
    (familyPoint_infinite hInfinite current)

theorem outputStep_previousOutput
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current : FiniteRankParent.FamilyPoint C)
    (fallback : Option (FiniteRankParent.FamilyPoint C)) :
    (outputStep hInfinite state input current fallback).previousOutput =
      some (emittedAtStep hInfinite state input current fallback) := by
  rfl

theorem emittedAtStep_fresh
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current : FiniteRankParent.FamilyPoint C)
    (fallback : Option (FiniteRankParent.FamilyPoint C)) :
    emittedAtStep hInfinite state input current fallback ∉
      insert input state.used := by
  exact
    (leastOutput_spec
      (priorityAtStep hInfinite state input fallback)
      current.1 (insert input state.used)
      (familyPoint_infinite hInfinite current)).1

theorem emittedAtStep_mem_priority_or_current
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current : FiniteRankParent.FamilyPoint C)
    (fallback : Option (FiniteRankParent.FamilyPoint C)) :
    emittedAtStep hInfinite state input current fallback ∈
        priorityAtStep hInfinite state input fallback ∨
      emittedAtStep hInfinite state input current fallback ∈
        current.1 := by
  exact
    (leastOutput_spec
      (priorityAtStep hInfinite state input fallback)
      current.1 (insert input state.used)
      (familyPoint_infinite hInfinite current)).2

theorem emittedAtStep_le_candidate
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current : FiniteRankParent.FamilyPoint C)
    (fallback : Option (FiniteRankParent.FamilyPoint C))
    {x : ℕ}
    (hxFresh : x ∉ insert input state.used)
    (hxAvailable :
      x ∈ priorityAtStep hInfinite state input fallback ∨
        x ∈ current.1) :
    emittedAtStep hInfinite state input current fallback ≤ x := by
  exact
    leastOutput_min
      (priorityAtStep hInfinite state input fallback)
      current.1 (insert input state.used)
      (familyPoint_infinite hInfinite current)
      ⟨hxFresh, hxAvailable⟩

theorem priorityAtStep_contains_fallback_window
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (fallback : FiniteRankParent.FamilyPoint C)
    {x : ℕ}
    (hx :
      x ∈ fallbackWindow fallback.1
        (familyPoint_infinite hInfinite fallback)
        (insert input state.used)
        ⟨input, Finset.mem_insert_self input state.used⟩) :
    x ∈ priorityAtStep hInfinite state input (some fallback) := by
  classical
  simp only [priorityAtStep]
  exact Finset.mem_union_right _ hx

/-- An available fallback-window string upper-bounds the emitted output. -/
theorem emittedAtStep_le_fallback_window_member
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current fallback : FiniteRankParent.FamilyPoint C)
    {x : ℕ}
    (hx :
      x ∈ fallbackWindow fallback.1
        (familyPoint_infinite hInfinite fallback)
        (insert input state.used)
        ⟨input, Finset.mem_insert_self input state.used⟩) :
    emittedAtStep hInfinite state input current (some fallback) ≤ x := by
  have hxFresh :
      x ∉ insert input state.used :=
    (mem_fallbackWindow.mp hx).2.2
  exact
    emittedAtStep_le_candidate hInfinite state input current
      (some fallback) hxFresh
      (Or.inl
        (priorityAtStep_contains_fallback_window
          hInfinite state input fallback hx))

/-- A queued string persists through a step unless the adversary or the
algorithm uses it at that step. -/
theorem queue_member_persists
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current : FiniteRankParent.FamilyPoint C)
    (fallback : Option (FiniteRankParent.FamilyPoint C))
    {x : ℕ}
    (hxQueue : x ∈ state.queue)
    (hxUsed : x ∉ state.used)
    (hxInput : x ≠ input)
    (hxOutput :
      x ≠ emittedAtStep hInfinite state input current fallback) :
    x ∈ (outputStep hInfinite state input current fallback).queue := by
  classical
  simp only [outputStep, Finset.mem_erase]
  refine ⟨hxOutput, ?_⟩
  apply Finset.mem_union_left
  apply Finset.mem_sdiff.mpr
  refine ⟨hxQueue, ?_⟩
  simp [hxInput, hxUsed]

/-- The normalized queue contains no string already marked used. -/
theorem outputStep_queue_fresh
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : OutputState) (input : ℕ)
    (current : FiniteRankParent.FamilyPoint C)
    (fallback : Option (FiniteRankParent.FamilyPoint C)) :
    Disjoint
      (outputStep hInfinite state input current fallback).queue
      (outputStep hInfinite state input current fallback).used := by
  classical
  rw [Finset.disjoint_left]
  intro x hxQueue hxUsed
  simp only [outputStep, Finset.mem_erase] at hxQueue
  rcases hxQueue with ⟨hxNeOutput, hxPriority⟩
  change
    x ∈ insert
      (emittedAtStep hInfinite state input current fallback)
      (insert input state.used) at hxUsed
  rw [Finset.mem_insert] at hxUsed
  rcases hxUsed with hxOutput | hxUsedNow
  · exact hxNeOutput hxOutput
  · have hxOldOrNew :
        x ∈ state.queue \ insert input state.used ∨
          x ∈
            match fallback with
            | none => ∅
            | some L =>
                fallbackWindow L.1
                  (familyPoint_infinite hInfinite L)
                  (insert input state.used)
                  ⟨input,
                    Finset.mem_insert_self input state.used⟩ := by
      simpa [priorityAtStep] using hxPriority
    rcases hxOldOrNew with hxOld | hxNew
    · exact (Finset.mem_sdiff.mp hxOld).2 hxUsedNow
    · cases fallback with
      | none =>
          simp at hxNew
      | some L =>
          have hparts :=
            (mem_fallbackWindow.mp hxNew)
          exact hparts.2.2 hxUsedNow

/-- The state immediately before round `t`. -/
noncomputable def runState
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C)) :
    ℕ → OutputState
  | 0 => OutputState.initial
  | t + 1 =>
      outputStep hInfinite
        (runState hInfinite input identified fallback t)
        (input t) (identified t) (fallback t)

/-- The emitted output sequence of the normalized run. -/
noncomputable def runOutput
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C))
    (t : ℕ) : ℕ :=
  emittedAtStep hInfinite
    (runState hInfinite input identified fallback t)
    (input t) (identified t) (fallback t)

/-- The normalized output state driven by the source's semantic selector and
the total canonical fallback schedule. -/
noncomputable def canonicalRunState
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r) :
    ℕ → OutputState :=
  runState hInfinite stream
    (FiniteRankParent.identifiedPointAt C stream)
    (canonicalFallbackAt C stream r hr)

/-- The output sequence of the canonically wired normalized state machine. -/
noncomputable def canonicalRunOutput
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (t : ℕ) : ℕ :=
  runOutput hInfinite stream
    (FiniteRankParent.identifiedPointAt C stream)
    (canonicalFallbackAt C stream r hr) t

@[simp] theorem runState_zero
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C)) :
    runState hInfinite input identified fallback 0 =
      OutputState.initial :=
  rfl

@[simp] theorem runState_succ
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C))
    (t : ℕ) :
    runState hInfinite input identified fallback (t + 1) =
      outputStep hInfinite
        (runState hInfinite input identified fallback t)
        (input t) (identified t) (fallback t) :=
  rfl

theorem runState_previousOutput_succ
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C))
    (t : ℕ) :
    (runState hInfinite input identified fallback
      (t + 1)).previousOutput =
        some
          (runOutput hInfinite input identified fallback t) := by
  exact
    outputStep_previousOutput hInfinite
      (runState hInfinite input identified fallback t)
      (input t) (identified t) (fallback t)

theorem runOutput_fresh
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C))
    (t : ℕ) :
    runOutput hInfinite input identified fallback t ∉
      insert (input t)
        (runState hInfinite input identified fallback t).used := by
  exact
    emittedAtStep_fresh hInfinite
      (runState hInfinite input identified fallback t)
      (input t) (identified t) (fallback t)

/-- In a reachable run, the `used` field is exactly the set of earlier
adversary inputs and earlier generator outputs. -/
theorem mem_runState_used_iff
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C))
    (t x : ℕ) :
    x ∈ (runState hInfinite input identified fallback t).used ↔
      (∃ s, s < t ∧ input s = x) ∨
        ∃ s, s < t ∧
          runOutput hInfinite input identified fallback s = x := by
  induction t with
  | zero =>
      simp [runState, OutputState.initial]
  | succ t ih =>
      rw [runState_succ]
      change
        x ∈ insert
            (runOutput hInfinite input identified fallback t)
            (insert (input t)
              (runState hInfinite input identified fallback t).used) ↔
          (∃ s, s < t + 1 ∧ input s = x) ∨
            ∃ s, s < t + 1 ∧
              runOutput hInfinite input identified fallback s = x
      simp only [Finset.mem_insert]
      constructor
      · rintro (houtput | hinput | hold)
        · exact
            Or.inr
              ⟨t, Nat.lt_succ_self t, houtput.symm⟩
        · exact
            Or.inl
              ⟨t, Nat.lt_succ_self t, hinput.symm⟩
        · rcases ih.mp hold with
            ⟨s, hs, hvalue⟩ | ⟨s, hs, hvalue⟩
          · exact Or.inl ⟨s, hs.trans_le (Nat.le_succ t), hvalue⟩
          · exact Or.inr ⟨s, hs.trans_le (Nat.le_succ t), hvalue⟩
      · rintro (⟨s, hs, hvalue⟩ | ⟨s, hs, hvalue⟩)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
          · exact
              Or.inr (Or.inr
                (ih.mpr (Or.inl ⟨s, hs, hvalue⟩)))
          · exact Or.inr (Or.inl hvalue.symm)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
          · exact
              Or.inr (Or.inr
                (ih.mpr (Or.inr ⟨s, hs, hvalue⟩)))
          · exact Or.inl hvalue.symm

theorem runOutput_ne_current_input
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C))
    (t : ℕ) :
    runOutput hInfinite input identified fallback t ≠ input t := by
  intro heq
  have hfresh :=
    runOutput_fresh hInfinite input identified fallback t
  exact hfresh (by simp [heq])

/-- The normalized generator never emits the same string twice. -/
theorem runOutput_injective
    {C : LanguageFamily}
    (hInfinite : ∀ n, (C n).Infinite)
    (input : ℕ → ℕ)
    (identified : ℕ → FiniteRankParent.FamilyPoint C)
    (fallback :
      ℕ → Option (FiniteRankParent.FamilyPoint C)) :
    Function.Injective
      (runOutput hInfinite input identified fallback) := by
  intro s t heq
  rcases lt_trichotomy s t with hst | hst | hst
  · have hused :
        runOutput hInfinite input identified fallback s ∈
          (runState hInfinite input identified fallback t).used :=
      (mem_runState_used_iff
        hInfinite input identified fallback t _).mpr
          (Or.inr ⟨s, hst, rfl⟩)
    have hfresh :=
      runOutput_fresh hInfinite input identified fallback t
    exfalso
    apply hfresh
    apply Finset.mem_insert.mpr
    exact Or.inr (by simpa [heq] using hused)
  · exact hst
  · have hused :
        runOutput hInfinite input identified fallback t ∈
          (runState hInfinite input identified fallback s).used :=
      (mem_runState_used_iff
        hInfinite input identified fallback s _).mpr
          (Or.inr ⟨t, hst, rfl⟩)
    have hfresh :=
      runOutput_fresh hInfinite input identified fallback s
    exfalso
    apply hfresh
    apply Finset.mem_insert.mpr
    exact Or.inr (by simpa [heq] using hused)

/-! ## The normalized bad set and Claim 6.11's arithmetic endgame -/

/-- The set of strings ever emitted by an output sequence. -/
def outputSet (output : ℕ → ℕ) : Language :=
  Set.range output

/-- A bad adversary event.  The positivity clause makes `output (t-1)`
literal; source time starts at one. -/
def BadAt
    (K : OrderedLanguage)
    (input output : ℕ → ℕ) (t : ℕ) : Prop :=
  0 < t ∧
    ∃ hx : input t ∈ K.carrier,
      input t ∉ outputSet output ∧
        orderedSuccessor K (input t) hx < output t ∧
          orderedSuccessor K (input t) hx < output (t - 1)

/-- The source's `W`; the later symbol `M` is normalized to this same set. -/
def badInputs
    (K : OrderedLanguage)
    (input output : ℕ → ℕ) : Language :=
  {x | ∃ t, input t = x ∧ BadAt K input output t}

/-- `length` consecutive positions of `K`, starting at `start`, are bad. -/
def HasBadRunFrom
    (K : OrderedLanguage) (bad : Language)
    (start length : ℕ) : Prop :=
  ∀ offset, offset < length →
    K.enumeration (start + offset) ∈ bad

/-- Corrected statement form of Claim 6.11. -/
def EventuallyNoBadRun
    (r : ℕ) (K : OrderedLanguage) (bad : Language) : Prop :=
  ∃ m, ∀ start, m ≤ start →
    ¬ HasBadRunFrom K bad start (r + 1)

/-- The rank chain which the source intends to extract from `r+1`
consecutive bad target strings. -/
def RankClimbWitness (r : ℕ) : Prop :=
  ∃ levels : ℕ → ℕ,
    (∀ i, i ≤ r → levels i < r) ∧
      ∀ i, i < r → levels i < levels (i + 1)

/-- No strictly increasing chain of `r+1` levels fits below rank `r`. -/
theorem no_rankClimbWitness (r : ℕ) :
    ¬ RankClimbWitness r := by
  rintro ⟨levels, hbound, hstep⟩
  have hgrowth :
      ∀ i, i ≤ r → levels 0 + i ≤ levels i := by
    intro i hi
    induction i with
    | zero =>
        simp
    | succ i ih =>
        have hiLt : i < r := by omega
        have hprev := ih (by omega)
        have hnext := hstep i hiLt
        omega
  have hrGrowth := hgrowth r le_rfl
  have hrBound := hbound r le_rfl
  omega

end FiniteRankFallback
end DensityMeasures
end KleinbergWei
end GenLimit
