import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GCGCommon
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyAsymptotics

/-!
# Diagnostic implementation of the printed strict-rise GCG

This file gives a causal, zero-based normalization of printed Algorithm 2
(`GCG`) in Ganju--McVoy--Dughmi--Teng.  It is retained for source comparison,
not used by the repaired Theorem 4 proof.

At Lean round `t`, the adversary value `stream t` is received first.  The P07
`Accurate` selector is evaluated at round `t + 1`.  A strict increase from the
preceding guess is appended to the candidate list.  The emitted point is the
first fresh member of the active language whose language rank is strictly
after `t`.

The printed strict-rise queue has an eventual-consistency gap: an early
non-target final candidate need not be removed by the stated `Accurate`
contract.  `TotalizedGCGMachine` gives the separately named queue-all-guesses
repair used by the proved Theorem 4.  Keeping this implementation in
`Diagnostics` makes the source defect inspectable without placing the printed
machine on the normal proof dependency path.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei

namespace CanonicallyOrderedFamily

/-- A strict language increase between two consecutive accurate guesses. -/
def StrictGuessRise (F : CanonicallyOrderedFamily)
    (stream : ℕ → ℕ) (t : ℕ) : Prop :=
  F.language (F.guess stream t) ⊂ F.language (F.guess stream (t + 1))

end CanonicallyOrderedFamily

/-- State immediately before one printed GCG round. -/
structure GCGState where
  candidates : List ℕ
  stage : ℕ
  outputs : List ℕ

def GCGState.initial : GCGState :=
  ⟨[], 0, []⟩

/-- Append the new guess exactly on a strict consecutive increase. -/
noncomputable def appendCurrentGuess
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (candidates : List ℕ) : List ℕ := by
  classical
  exact if F.StrictGuessRise stream t then
    candidates ++ [F.guess stream (t + 1)]
  else candidates

/-- Active family index after the current strict-rise update. -/
noncomputable def activeGuess
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t stage : ℕ) (candidates : List ℕ) : ℕ :=
  if candidates.isEmpty then F.guess stream (t + 1)
  else candidates.getD stage (F.guess stream (t + 1))

/-- Data computed before emitting the round-`t` output. -/
noncomputable def gcgRoundCandidates
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (old : GCGState) : List ℕ :=
  appendCurrentGuess F stream t old.candidates

noncomputable def gcgRoundActive
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (old : GCGState) : ℕ :=
  activeGuess F stream t old.stage (gcgRoundCandidates F stream t old)

noncomputable def gcgRoundOutput
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (old : GCGState) : ℕ :=
  greedyRoundOutput (F.order (gcgRoundActive F stream t old))
    stream t old.outputs

/-- One causal round of the zero-based printed Algorithm 2 normalization. -/
noncomputable def gcgStep
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (old : GCGState) : GCGState := by
  classical
  let candidates := gcgRoundCandidates F stream t old
  let active := gcgRoundActive F stream t old
  let output := gcgRoundOutput F stream t old
  let outputs := old.outputs ++ [output]
  let canAdvance := old.stage + 1 < candidates.length
  let crossed :=
    gcgThreshold (old.stage + 1) ≤
      timelyDensity (outputHistoryStream outputs)
        (F.order active).enumeration id (t + 1)
  exact
    { candidates := candidates
      stage := if canAdvance ∧ crossed then old.stage + 1 else old.stage
      outputs := outputs }

/-- State after the first `t` complete printed GCG rounds. -/
noncomputable def gcgRun
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) : ℕ → GCGState
  | 0 => GCGState.initial
  | t + 1 => gcgStep F stream t (gcgRun F stream t)

/-- The concrete output sequence of the printed Algorithm 2. -/
noncomputable def gcgOutput
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  gcgRoundOutput F stream t (gcgRun F stream t)

@[simp] theorem gcgRun_zero
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    gcgRun F stream 0 = GCGState.initial := rfl

@[simp] theorem gcgRun_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    gcgRun F stream (t + 1) = gcgStep F stream t (gcgRun F stream t) := rfl

theorem gcgRun_outputs_length
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (gcgRun F stream t).outputs.length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp [gcgRun, gcgStep, ih]

theorem gcgRun_outputs_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (gcgRun F stream (t + 1)).outputs =
      (gcgRun F stream t).outputs ++ [gcgOutput F stream t] := by
  rfl

theorem gcgOutput_mem_active
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    gcgOutput F stream t ∈
      F.language (gcgRoundActive F stream t (gcgRun F stream t)) := by
  rw [← F.carrier_eq]
  exact onTimeUnused_mem _ _ _

theorem gcgOutput_not_mem_observed
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    gcgOutput F stream t ∉ sample stream (t + 1) := by
  intro h
  exact onTimeUnused_fresh _ _ _ (Finset.mem_union_left _ h)

theorem gcgOutput_not_mem_prior_outputs
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    gcgOutput F stream t ∉ (gcgRun F stream t).outputs.toFinset := by
  intro h
  exact onTimeUnused_fresh _ _ _ (Finset.mem_union_right _ h)

theorem gcgOutput_rank_onTime
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    t < onTimeUnusedRank
      (F.order (gcgRoundActive F stream t (gcgRun F stream t)))
      (greedyUsed stream t (gcgRun F stream t).outputs) t :=
  onTimeUnused_onTime _ _ _

end GenLimit.TimeSensitive
