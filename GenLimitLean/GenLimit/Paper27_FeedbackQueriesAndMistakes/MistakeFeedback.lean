import GenLimit.Paper27_FeedbackQueriesAndMistakes.Definitions
import Mathlib.Data.List.Count
import Mathlib.Logic.Equiv.List

/-!
# Mistake-feedback generation: the countable-inner-cover core

This file formalizes an auxiliary, stronger-feedback set-output model.  A
strategy sees the complete finite history of truthful bits saying whether its
preceding whole set output was contained in the target.  It must eventually
output infinite subsets of the target.

The paper does not use this whole-set validity bit in Definition 3:
it tests only a canonical first output element, including freshness relative
to the observed sample.  The exact element and set models for Theorems 3.1--3.2
are in `ElementMistake.lean` and `SourceSetMistake.lean`.  The theorem below is
kept as a genuine auxiliary characterization, not promoted as a numbered
source result.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-- A set-valued strategy whose only observation is the finite history of
truthful mistake bits. -/
abbrev SetMistakeStrategy (α : Type*) :=
  List Bool → Set α

/-- The truthful bit returned after a set output: `true` means that the
entire output is contained in the target. -/
noncomputable def mistakeReply
    (strategy : SetMistakeStrategy α)
    (target : Set α) (history : List Bool) : Bool := by
  classical
  exact if strategy history ⊆ target then true else false

/-- The finite feedback history before round `t`. -/
noncomputable def mistakeHistory
    (strategy : SetMistakeStrategy α)
    (target : Set α) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
      let history := mistakeHistory strategy target t
      history ++ [mistakeReply strategy target history]

@[simp] theorem mistakeHistory_zero
    (strategy : SetMistakeStrategy α) (target : Set α) :
    mistakeHistory strategy target 0 = [] :=
  rfl

@[simp] theorem mistakeHistory_succ
    (strategy : SetMistakeStrategy α) (target : Set α) (t : ℕ) :
    mistakeHistory strategy target (t + 1) =
      mistakeHistory strategy target t ++
        [mistakeReply strategy target
          (mistakeHistory strategy target t)] :=
  rfl

/-- The set emitted in round `t` of the truthful interaction. -/
noncomputable def mistakeOutput
    (strategy : SetMistakeStrategy α)
    (target : Set α) (t : ℕ) : Set α :=
  strategy (mistakeHistory strategy target t)

/-- Eventual set-generation on one target. -/
def SetMistakeSucceedsOn
    (strategy : SetMistakeStrategy α)
    (target : Set α) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    (mistakeOutput strategy target t).Infinite ∧
      mistakeOutput strategy target t ⊆ target

/-- One strategy succeeds on every target in the class. -/
def SetMistakeGenerates
    (strategy : SetMistakeStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → SetMistakeSucceedsOn strategy L

/-- Existential set-valued mistake-feedback generation. -/
def SetMistakeGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : SetMistakeStrategy α,
    SetMistakeGenerates strategy targets

/-! ## Necessity: finite Boolean histories give a countable cover -/

/-- Necessity in the mistake-feedback characterization: the countably many
finite feedback transcripts enumerate an inner cover. -/
noncomputable def countableInnerCoverOfSetMistake
    [Infinite α]
    {targets : LanguageClass α}
    (strategy : SetMistakeStrategy α)
    (hstrategy : SetMistakeGenerates strategy targets) :
    CountableInnerCover targets := by
  apply CountableInnerCover.ofCountableOutputs strategy
  intro L hL
  obtain ⟨T, hT⟩ := hstrategy L hL
  have hgood := hT T (Nat.le_refl T)
  exact ⟨mistakeHistory strategy L T, hgood⟩

theorem setMistake_implies_countableInnerCover
    [Infinite α]
    {targets : LanguageClass α}
    (h : SetMistakeGeneratable targets) :
    HasCountableInnerCover targets := by
  obtain ⟨strategy, hstrategy⟩ := h
  exact ⟨countableInnerCoverOfSetMistake strategy hstrategy⟩

/-! ## Sufficiency: reject covers in order and lock on the first accepted one -/

/-- The canonical strategy tests cover number `i`, where `i` is the number
of preceding rejections.  A positive reply leaves `i` unchanged, so the
strategy locks on the first accepted cover. -/
def innerCoverMistakeStrategy
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    SetMistakeStrategy α :=
  fun history => inner.cover (history.count false)

private theorem innerCoverMistake_falseCount
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α)
    (k : ℕ)
    (hgood : inner.cover k ⊆ L)
    (hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ L) :
    ∀ t,
      (mistakeHistory (innerCoverMistakeStrategy inner) L t).count false =
        min t k := by
  classical
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      by_cases htk : t < k
      · have hmin : min t k = t :=
          Nat.min_eq_left (Nat.le_of_lt htk)
        have hbad : ¬ inner.cover t ⊆ L :=
          hminimal t htk
        have hsucc : t + 1 ≤ k := htk
        have hreply :
            mistakeReply (innerCoverMistakeStrategy inner) L
                (mistakeHistory (innerCoverMistakeStrategy inner) L t) =
              false := by
          simp [mistakeReply, innerCoverMistakeStrategy, ih, hmin, hbad]
        rw [mistakeHistory_succ, List.count_append, ih,
          Nat.min_eq_left (Nat.le_of_lt htk), hreply]
        simp
        exact hsucc
      · have hkt : k ≤ t := Nat.le_of_not_gt htk
        have hmin : min t k = k := Nat.min_eq_right hkt
        have hsucc : k ≤ t + 1 := Nat.le_trans hkt (Nat.le_succ t)
        have hreply :
            mistakeReply (innerCoverMistakeStrategy inner) L
                (mistakeHistory (innerCoverMistakeStrategy inner) L t) =
              true := by
          simp [mistakeReply, innerCoverMistakeStrategy, ih, hmin, hgood]
        rw [mistakeHistory_succ, List.count_append, ih,
          Nat.min_eq_right hkt, hreply]
        simp
        exact hsucc

/-- Sufficiency in the core characterization. -/
theorem countableInnerCover_implies_setMistake
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    SetMistakeGeneratable targets := by
  classical
  let inner := Nonempty.some hinner
  refine ⟨innerCoverMistakeStrategy inner, ?_⟩
  intro L hL
  let hexists : ∃ i, inner.cover i ⊆ L :=
    inner.contained L hL
  let k := Nat.find hexists
  have hgood : inner.cover k ⊆ L := by
    simpa [k] using Nat.find_spec hexists
  have hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ L := by
    intro i hi
    exact Nat.find_min hexists (by simpa [k] using hi)
  refine ⟨k, ?_⟩
  intro t hkt
  have hcount :
      (mistakeHistory (innerCoverMistakeStrategy inner) L t).count false =
        k := by
    rw [innerCoverMistake_falseCount inner L k hgood hminimal]
    exact Nat.min_eq_right hkt
  have houtput :
      mistakeOutput (innerCoverMistakeStrategy inner) L t =
        inner.cover k := by
    simp only [mistakeOutput, innerCoverMistakeStrategy, hcount]
  rw [houtput]
  exact ⟨inner.infinite_cover k, hgood⟩

/-- The countable-inner-cover characterization for the auxiliary sample-free
whole-set-validity feedback model. -/
theorem setMistake_core_characterization
    [Infinite α]
    (targets : LanguageClass α) :
    SetMistakeGeneratable targets ↔
      HasCountableInnerCover targets :=
  ⟨setMistake_implies_countableInnerCover,
    countableInnerCover_implies_setMistake⟩

end GenLimit.FeedbackQueries
