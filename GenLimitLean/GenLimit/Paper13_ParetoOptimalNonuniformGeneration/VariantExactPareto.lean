import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.ArbitraryScheduler
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Scheduling

/-!
# Exact-Pareto scheduler endgames for the noisy and representative variants

Theorems 8 and 9 of Charikar--Pabbaraju,
*Pareto-optimal Non-uniform Language Generation*, use the same final
scheduling argument as Theorem 5.  Their variant-specific work is earlier:
construct the noisy or representative complexity, prove its Pareto lower
bound, and prove that the corresponding scheduler-driven algorithm realizes
the displayed maximum time.

This file formalizes the common final step.  It does not postulate either
variant construction.  Instead, `VariantSchedulerCertificate` records the
two exact obligations supplied by Theorems 6--7 and Claims B.2/C.2.  Under
the finite-sublevel hypothesis printed in Theorems 8--9, the scheduler built
below enters every coordinate by its canonical time.  Consequently the
maximum-time guarantee collapses to the canonical vector, which is both
realizable and Pareto optimal.

Coordinates are natural numbers.  For noisy generation they are the
zero-based positions of the paper's diagonal traversal of `(noise, language)`
pairs; for representative generation they are the language indices.
No probability distribution, randomized generator, or runtime semantics is
introduced here.
-/

namespace GenLimit.ParetoGeneration

/-- The canonical positive time vector associated with a variant complexity. -/
def variantCanonicalTime (complexity : TimeVector) : TimeVector :=
  fun i => complexity i + 1

/-- The generic finite-sublevel scheduler used in the exact noisy and
representative endgames.  Its value is a number of coordinates, hence the
successor of the largest eligible zero-based index. -/
noncomputable def variantFiniteSublevelScheduler
    (complexity : TimeVector) (hfinite : FiniteSublevels complexity) :
    ℕ → ℕ :=
  fun t => scope complexity hfinite t + 1

theorem variantFiniteSublevelScheduler_isUnbounded
    (complexity : TimeVector) (hfinite : FiniteSublevels complexity) :
    IsUnboundedScheduler
      (variantFiniteSublevelScheduler complexity hfinite) := by
  constructor
  · intro s t hst
    exact Nat.add_le_add_right (scope_mono hst) 1
  · intro i
    refine ⟨complexity i + 1, ?_⟩
    have hi := index_in_scope_by_complexity complexity hfinite i
    simpa [variantFiniteSublevelScheduler] using Nat.lt_succ_of_le hi

/-- Every coordinate enters the finite-sublevel scheduler no later than its
canonical time. -/
theorem variant_schedulerEntryTime_le
    (complexity : TimeVector) (hfinite : FiniteSublevels complexity)
    (i : ℕ) :
    schedulerEntryTime
        (variantFiniteSublevelScheduler complexity hfinite)
        (variantFiniteSublevelScheduler_isUnbounded complexity hfinite) i ≤
      variantCanonicalTime complexity i := by
  apply schedulerEntryTime_le_of_in_scope
  have hi := index_in_scope_by_complexity complexity hfinite i
  simpa [variantFiniteSublevelScheduler] using Nat.lt_succ_of_le hi

/-- The source's two variant obligations, isolated from the common scheduler
endgame.

`scheduler_realizable` is the exact maximum-time conclusion of Theorem 6 or
Theorem 7.  `canonical_tradeoff` is the earlier-coordinate lower bound of
Claim B.2 or Claim C.2. -/
structure VariantSchedulerCertificate
    (Achievable : Set TimeVector) (complexity : TimeVector) : Prop where
  scheduler_realizable :
    ∀ (f : ℕ → ℕ) (hf : IsUnboundedScheduler f),
      (fun i =>
        max (schedulerEntryTime f hf i)
          (variantCanonicalTime complexity i)) ∈ Achievable
  canonical_tradeoff :
    EarlierTradeoff (variantCanonicalTime complexity) Achievable

/-- The finite-sublevel scheduler realizes the canonical vector exactly. -/
theorem variant_canonicalTime_realizable
    {Achievable : Set TimeVector} {complexity : TimeVector}
    (certificate : VariantSchedulerCertificate Achievable complexity)
    (hfinite : FiniteSublevels complexity) :
    variantCanonicalTime complexity ∈ Achievable := by
  let f := variantFiniteSublevelScheduler complexity hfinite
  let hf := variantFiniteSublevelScheduler_isUnbounded complexity hfinite
  have hrealizable := certificate.scheduler_realizable f hf
  have htime :
      (fun i =>
        max (schedulerEntryTime f hf i)
          (variantCanonicalTime complexity i)) =
        variantCanonicalTime complexity := by
    funext i
    exact max_eq_right
      (variant_schedulerEntryTime_le complexity hfinite i)
  simpa [htime] using hrealizable

/-- Common exact-Pareto conclusion of Theorems 8 and 9: finite sublevels turn
the scheduler guarantee into a realizable Pareto-optimal canonical vector. -/
theorem variant_exactPareto_of_finiteSublevels
    {Achievable : Set TimeVector} {complexity : TimeVector}
    (certificate : VariantSchedulerCertificate Achievable complexity)
    (hfinite : FiniteSublevels complexity) :
    variantCanonicalTime complexity ∈ Achievable ∧
      ParetoOptimal Achievable (variantCanonicalTime complexity) := by
  exact
    ⟨variant_canonicalTime_realizable certificate hfinite,
      earlierTradeoff_implies_paretoOptimal
        certificate.canonical_tradeoff⟩

/-- Theorem 8's deterministic scheduling endgame, with noisy diagonal
coordinates encoded by natural numbers.  The noisy construction and its
probability-free semantic correctness are exactly the supplied certificate. -/
theorem theorem_8_noisy_exactPareto_endgame
    {Achievable : Set TimeVector} {noisyComplexity : TimeVector}
    (certificate :
      VariantSchedulerCertificate Achievable noisyComplexity)
    (hfinite : FiniteSublevels noisyComplexity) :
    variantCanonicalTime noisyComplexity ∈ Achievable ∧
      ParetoOptimal Achievable
        (variantCanonicalTime noisyComplexity) :=
  variant_exactPareto_of_finiteSublevels certificate hfinite

/-- Theorem 9's deterministic scheduling endgame.  The representative
distribution construction remains outside this declaration and is captured
by the supplied certificate. -/
theorem theorem_9_representative_exactPareto_endgame
    {Achievable : Set TimeVector}
    {representativeComplexity : TimeVector}
    (certificate :
      VariantSchedulerCertificate Achievable representativeComplexity)
    (hfinite : FiniteSublevels representativeComplexity) :
    variantCanonicalTime representativeComplexity ∈ Achievable ∧
      ParetoOptimal Achievable
        (variantCanonicalTime representativeComplexity) :=
  variant_exactPareto_of_finiteSublevels certificate hfinite

end GenLimit.ParetoGeneration
