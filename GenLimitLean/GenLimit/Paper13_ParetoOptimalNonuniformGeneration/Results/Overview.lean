import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.ExactPareto
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.NoisyProcedure

/-!
# Paper 13: main-results overview

This module is the public results facade for Charikar--Pabbaraju,
*Pareto-optimal Non-uniform Language Generation* (arXiv:2510.02795v1).
The declarations below are thin wrappers around the canonical proof modules;
they do not duplicate proofs.

## Coverage boundary

Theorems 1, 4, and 5 are exposed at the paper's deterministic semantic
boundary.  Theorem 6 is exposed with the totalized initialization required
when Procedure 2 has no feasible first witness.  This repair preserves the
source theorem's displayed generation-time conclusion.  The resulting
concrete noisy certificate also yields Theorem 8.

The representative distributional construction of Theorem 7 is not yet
formalized.  Consequently Theorem 9 is represented only by its common
finite-sublevel scheduler endgame, conditional on a
`VariantSchedulerCertificate`; it is deliberately not presented as a
concrete source theorem.  All generators are classical semantic functions;
no computability or running-time bound is claimed.
-/

namespace GenLimit.ParetoGeneration.Results

open GenLimit.ParetoGeneration

/-- Overview Theorem 1: every requested finite prefix of the canonical
Procedure-1 vector is realized by one globally valid generator and is
Pareto-optimal on that prefix. -/
theorem theorem_1
    [Infinite α] (F : Nat -> Set α) (stage : Nat) :
    ∃ G : HistoryGenerator α, ∃ time : TimeVector,
      AchievesTimeVector G F time ∧
      PositiveTimeVector time ∧
      MatchesPrefix stage time
        (fun i =>
          (canonicalProcedureStage F stage).complexity i + 1) ∧
      PrefixParetoOptimal stage
        (RealizableTimeVectors F) time :=
  overview_theorem_1_semantic F stage

/-- Theorem 4: an arbitrary monotone unbounded scheduler realizes the exact
displayed vector `max (g i) (mStar i + 1)`. -/
theorem theorem_4
    [Infinite α] (F : Nat -> Set α)
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f) :
    AchievesTimeVector (schedulerGenerator F f) F
        (schedulerTimeVector F f hf) ∧
      PositiveTimeVector (schedulerTimeVector F f hf) :=
  theorem_4_arbitrary_scheduler F f hf

/-- Theorem 5: finite canonical sublevels yield a generator realizing the
complete canonical Pareto-optimal vector. -/
theorem theorem_5
    [Infinite α] (F : Nat -> Set α)
    (hfinite : FiniteSublevels (canonicalComplexity F)) :
    ∃ G : HistoryGenerator α,
      AchievesTimeVector G F
          (fun i => canonicalComplexity F i + 1) ∧
        PositiveTimeVector
          (fun i => canonicalComplexity F i + 1) ∧
        ParetoOptimal (RealizableTimeVectors F)
          (fun i => canonicalComplexity F i + 1) :=
  theorem_5_exact_pareto F hfinite

/-- Theorem 6 with the source's empty-candidate initialization totalized:
the concrete noisy scheduler realizes the displayed noisy time vector. -/
theorem theorem_6
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f) :
    AchievesNoisyTimeVector
          (noisySchedulerGenerator F noise f)
          F noise
          (noisySchedulerTimeVector F noise f hf) ∧
      PositiveTimeVector
        (noisySchedulerTimeVector F noise f hf) :=
  theorem_6_corrected_totalized F noise f hf

/-- Theorem 8: under finite noisy-complexity sublevels, the corrected
Procedure-2 construction realizes a Pareto-optimal canonical noisy vector. -/
theorem theorem_8
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (hFinite :
      FiniteSublevels (canonicalNoisyComplexity F noise)) :
    variantCanonicalTime
          (canonicalNoisyComplexity F noise) ∈
        NoisyRealizableTimeVectors F noise ∧
      ParetoOptimal (NoisyRealizableTimeVectors F noise)
        (variantCanonicalTime
          (canonicalNoisyComplexity F noise)) :=
  theorem_8_corrected_deterministic_endgame F noise hFinite

/-- The scheduler-only endgame used by Theorem 9.  A concrete representative
specialization remains open because Theorem 7's distributional construction
has not yet supplied this certificate. -/
theorem theorem_9_representative_endgame
    {Achievable : Set TimeVector}
    {representativeComplexity : TimeVector}
    (certificate :
      VariantSchedulerCertificate Achievable representativeComplexity)
    (hfinite : FiniteSublevels representativeComplexity) :
    variantCanonicalTime representativeComplexity ∈ Achievable ∧
      ParetoOptimal Achievable
        (variantCanonicalTime representativeComplexity) :=
  theorem_9_representative_exactPareto_endgame certificate hfinite

end GenLimit.ParetoGeneration.Results
