import GenLimit.Core.GenericGeneration
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.AccurateCausality
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TotalizedGCGMachine

/-!
# Finite-history realization of the repaired GCG

`TotalizedGCGMachine` is conveniently stated against a completed infinite
stream.  This module exposes the same round operation using only the finite
history visible after the adversary's current announcement.  The visible
history is extended by repeating its last value, and prefix causality of the
P07 selector proves that this arbitrary completion cannot affect the round.

The resulting state can be placed inside a joint adversary/generator
recursion without a circular infinite-stream definition.
-/

namespace GenLimit.TimeSensitive

/-- State of the finite-history repaired GCG immediately before a round. -/
structure OnlineTotalizedGCGState where
  stage : ℕ
  observations : List ℕ
  outputs : List ℕ

def OnlineTotalizedGCGState.initial : OnlineTotalizedGCGState :=
  ⟨0, [], []⟩

def OnlineTotalizedGCGState.base
    (state : OnlineTotalizedGCGState) : TotalizedGCGState :=
  ⟨state.stage, state.outputs⟩

/-- Any total completion of the observations through the current round.
Only its visible prefix is semantically used. -/
def onlineVisibleStream
    (state : OnlineTotalizedGCGState) (current : ℕ) : ℕ → ℕ :=
  GenLimit.Generic.historyThenFallback
    (state.observations ++ [current]) current

noncomputable def onlineTotalizedRoundOutput
    (F : CanonicallyOrderedFamily) (t : ℕ)
    (state : OnlineTotalizedGCGState) (current : ℕ) : ℕ :=
  totalizedRoundOutput F (onlineVisibleStream state current) t state.base

noncomputable def onlineTotalizedGCGStep
    (F : CanonicallyOrderedFamily) (t : ℕ)
    (state : OnlineTotalizedGCGState) (current : ℕ) :
    OnlineTotalizedGCGState :=
  let next := totalizedGCGStep F (onlineVisibleStream state current) t state.base
  { stage := next.stage
    observations := state.observations ++ [current]
    outputs := next.outputs }

noncomputable def onlineTotalizedGCGRun
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    ℕ → OnlineTotalizedGCGState
  | 0 => OnlineTotalizedGCGState.initial
  | t + 1 => onlineTotalizedGCGStep F t
      (onlineTotalizedGCGRun F stream t) (stream t)

noncomputable def onlineTotalizedGCGOutput
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  onlineTotalizedRoundOutput F t
    (onlineTotalizedGCGRun F stream t) (stream t)

@[simp] theorem onlineTotalizedGCGRun_zero
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    onlineTotalizedGCGRun F stream 0 = OnlineTotalizedGCGState.initial := rfl

@[simp] theorem onlineTotalizedGCGRun_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    onlineTotalizedGCGRun F stream (t + 1) =
      onlineTotalizedGCGStep F t
        (onlineTotalizedGCGRun F stream t) (stream t) := rfl

theorem onlineTotalizedGCGRun_observations_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (onlineTotalizedGCGRun F stream t).observations =
      (List.range t).map stream := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [onlineTotalizedGCGRun_succ]
      simp only [onlineTotalizedGCGStep, ih]
      simp [List.range_succ]

theorem onlineTotalizedGCGRun_outputs_length
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (onlineTotalizedGCGRun F stream t).outputs.length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [onlineTotalizedGCGRun_succ]
      simp only [onlineTotalizedGCGStep, totalizedGCGStep,
        OnlineTotalizedGCGState.base]
      simp [ih]

theorem onlineVisibleStream_run_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t n : ℕ) (hn : n < t + 1) :
    onlineVisibleStream (onlineTotalizedGCGRun F stream t) (stream t) n =
      stream n := by
  rw [onlineVisibleStream,
    onlineTotalizedGCGRun_observations_eq]
  simp only [GenLimit.Generic.historyThenFallback]
  have hlength :
      ((List.range t).map stream ++ [stream t]).length = t + 1 := by simp
  rw [dif_pos (by simpa [hlength] using hn)]
  by_cases hnt : n < t
  · simp [List.get_eq_getElem, hnt]
  · have hntEq : n = t := by omega
    subst n
    simp [List.get_eq_getElem]

theorem totalizedRoundActive_eq_of_eqOn_prefix
    (F : CanonicallyOrderedFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ} {state : TotalizedGCGState}
    (hstage : state.stage ≤ t)
    (hstream : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    totalizedRoundActive F stream₁ t state =
      totalizedRoundActive F stream₂ t state := by
  unfold totalizedRoundActive CanonicallyOrderedFamily.guess
  apply guessIndex_eq_of_eqOn_prefix
  intro n hn
  apply hstream n
  omega

theorem totalizedRoundOutput_eq_of_eqOn_prefix
    (F : CanonicallyOrderedFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ} {state : TotalizedGCGState}
    (hstage : state.stage ≤ t)
    (hstream : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    totalizedRoundOutput F stream₁ t state =
      totalizedRoundOutput F stream₂ t state := by
  unfold totalizedRoundOutput greedyRoundOutput greedyUsed
  rw [totalizedRoundActive_eq_of_eqOn_prefix F hstage hstream]
  rw [sample_eq_of_eq_on_prefix hstream]

theorem totalizedGCGStep_eq_of_eqOn_prefix
    (F : CanonicallyOrderedFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ} {state : TotalizedGCGState}
    (hstage : state.stage ≤ t)
    (hstream : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    totalizedGCGStep F stream₁ t state =
      totalizedGCGStep F stream₂ t state := by
  classical
  unfold totalizedGCGStep
  rw [totalizedRoundActive_eq_of_eqOn_prefix F hstage hstream]
  rw [totalizedRoundOutput_eq_of_eqOn_prefix F hstage hstream]

/-- The finite-history machine is extensionally the original repaired GCG
on every completed stream. -/
theorem onlineTotalizedGCGRun_base_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (onlineTotalizedGCGRun F stream t).base =
      totalizedGCGRun F stream t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [onlineTotalizedGCGRun_succ, totalizedGCGRun_succ]
      simp only [onlineTotalizedGCGStep, OnlineTotalizedGCGState.base]
      change
        totalizedGCGStep F
            (onlineVisibleStream (onlineTotalizedGCGRun F stream t) (stream t))
            t (onlineTotalizedGCGRun F stream t).base =
          totalizedGCGStep F stream t (totalizedGCGRun F stream t)
      rw [show
        totalizedGCGStep F
            (onlineVisibleStream (onlineTotalizedGCGRun F stream t) (stream t))
            t (onlineTotalizedGCGRun F stream t).base =
          totalizedGCGStep F stream t
            (onlineTotalizedGCGRun F stream t).base by
        apply totalizedGCGStep_eq_of_eqOn_prefix F
        · rw [ih]
          exact totalizedGCGRun_stage_le_time F stream t
        · exact onlineVisibleStream_run_eq F stream t]
      rw [ih]

theorem onlineTotalizedGCGOutput_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    onlineTotalizedGCGOutput F stream t =
      totalizedGCGOutput F stream t := by
  unfold onlineTotalizedGCGOutput onlineTotalizedRoundOutput
  rw [totalizedRoundOutput_eq_of_eqOn_prefix F
    (by rw [onlineTotalizedGCGRun_base_eq]
        exact totalizedGCGRun_stage_le_time F stream t)
    (onlineVisibleStream_run_eq F stream t)]
  rw [onlineTotalizedGCGRun_base_eq]
  rfl

end GenLimit.TimeSensitive
