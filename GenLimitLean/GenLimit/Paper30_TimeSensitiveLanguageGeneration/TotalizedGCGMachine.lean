import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GCGCommon
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyUpperDensity
import GenLimit.Support.TurnTaking.Announcements

/-!
# A totalized GCG queue

The printed Algorithm 2 queues only strict-superset transitions.  Its proof
later treats every queued language as eventually target-valid, although the
`Accurate` contract provides validity only after an unknown finite time.  An
early non-target queue entry can therefore be the final entry and make the
printed machine inconsistent forever.

This module records the minimal semantic repair used for the existential
Theorem 4: queue every `Accurate` guess.  Stage `m` uses the guess from round
`m + 1`.  Every stage still employs the paper's literal `OnTimeUnused` rule
and advances only after crossing its prescribed density threshold.  Since
the queue is cofinal, finite early guesses are eventually left behind and
the P07 `Accurate` guarantees apply without any oracle for the unknown
validity time.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei

structure TotalizedGCGState where
  stage : ℕ
  outputs : List ℕ

def TotalizedGCGState.initial : TotalizedGCGState :=
  ⟨0, []⟩

/-- Candidate used in round `t`; the time argument is retained to make the
causal interface explicit. -/
noncomputable def totalizedRoundActive
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (_t : ℕ) (old : TotalizedGCGState) : ℕ :=
  F.guess stream (old.stage + 1)

noncomputable def totalizedRoundOutput
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (old : TotalizedGCGState) : ℕ :=
  greedyRoundOutput (F.order (totalizedRoundActive F stream t old))
    stream t old.outputs

/-- One round of the repaired queue.  At round `t`, stage `m` has a next
queued guess exactly when `m < t`. -/
noncomputable def totalizedGCGStep
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (old : TotalizedGCGState) : TotalizedGCGState := by
  classical
  let active := totalizedRoundActive F stream t old
  let output := totalizedRoundOutput F stream t old
  let outputs := old.outputs ++ [output]
  let crossed :=
    gcgThreshold (old.stage + 1) ≤
      timelyDensity (outputHistoryStream outputs)
        (F.order active).enumeration id (t + 1)
  exact
    { stage := if old.stage < t ∧ crossed then old.stage + 1 else old.stage
      outputs := outputs }

noncomputable def totalizedGCGRun
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    ℕ → TotalizedGCGState
  | 0 => TotalizedGCGState.initial
  | t + 1 => totalizedGCGStep F stream t (totalizedGCGRun F stream t)

noncomputable def totalizedGCGOutput
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  totalizedRoundOutput F stream t (totalizedGCGRun F stream t)

@[simp] theorem totalizedGCGRun_zero
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    totalizedGCGRun F stream 0 = TotalizedGCGState.initial := rfl

@[simp] theorem totalizedGCGRun_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    totalizedGCGRun F stream (t + 1) =
      totalizedGCGStep F stream t (totalizedGCGRun F stream t) := rfl

theorem totalizedGCGRun_outputs_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream (t + 1)).outputs =
      (totalizedGCGRun F stream t).outputs ++
        [totalizedGCGOutput F stream t] := by
  rfl

theorem totalizedGCGRun_outputs_length
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).outputs.length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [totalizedGCGRun_outputs_succ, List.length_append, ih]
      simp

theorem totalizedGCGRun_outputs_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).outputs =
      (List.range t).map (totalizedGCGOutput F stream) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [totalizedGCGRun_outputs_succ, ih]
      simp [List.range_succ]

theorem totalizedGCGRun_outputs_toFinset
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).outputs.toFinset =
      sequencePrefix (totalizedGCGOutput F stream) t := by
  classical
  ext x
  simp [totalizedGCGRun_outputs_eq, sequencePrefix]

theorem totalizedGCGOutput_not_mem_observed
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    totalizedGCGOutput F stream t ∉ sample stream (t + 1) := by
  intro h
  exact onTimeUnused_fresh _ _ _ (Finset.mem_union_left _ h)

theorem totalizedGCGOutput_not_mem_prior
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    totalizedGCGOutput F stream t ∉
      sequencePrefix (totalizedGCGOutput F stream) t := by
  rw [← totalizedGCGRun_outputs_toFinset]
  intro h
  exact onTimeUnused_fresh _ _ _ (Finset.mem_union_right _ h)

theorem totalizedGCG_freshPlay
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    FreshPlay stream (totalizedGCGOutput F stream) := by
  constructor
  · intro t s hst heq
    apply totalizedGCGOutput_not_mem_observed F stream t
    rw [mem_sample_iff]
    exact ⟨s, by omega, heq⟩
  · intro t s hst heq
    apply totalizedGCGOutput_not_mem_prior F stream t
    rw [mem_sequencePrefix_iff]
    exact ⟨s, hst, heq⟩

theorem totalizedGCGOutput_mem_active
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    totalizedGCGOutput F stream t ∈
      F.language
        (F.guess stream ((totalizedGCGRun F stream t).stage + 1)) := by
  rw [← F.carrier_eq]
  exact onTimeUnused_mem _ _ _

theorem totalizedGCGRun_stage_mono_step
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).stage ≤
      (totalizedGCGRun F stream (t + 1)).stage := by
  simp only [totalizedGCGRun_succ, totalizedGCGStep]
  split <;> omega

theorem totalizedGCGRun_stage_le_time
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).stage ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [totalizedGCGRun_succ, totalizedGCGStep]
      split <;> omega

theorem totalizedGCGRun_stage_mono
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    Monotone fun t => (totalizedGCGRun F stream t).stage := by
  exact monotone_nat_of_le_succ
    (totalizedGCGRun_stage_mono_step F stream)

end GenLimit.TimeSensitive
