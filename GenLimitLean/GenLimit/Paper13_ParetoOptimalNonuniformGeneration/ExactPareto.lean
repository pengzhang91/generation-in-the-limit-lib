import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.VariantExactPareto

/-!
# Exact Pareto optimality under finite sublevels

This module combines the newly formalized arbitrary-scheduler Theorem 4
with the finite-sublevel scheduler from `Scheduling.lean` to prove the full
semantic content of Theorem 5 in Charikar--Pabbaraju,
*Pareto-optimal Non-uniform Language Generation*,
arXiv:2510.02795v1, p. 10.

The source scheduler stores the largest eligible zero-based index.  Since
Theorem 4 interprets `f(t)` as a number of languages, the literal
zero-based scheduler here is `scope(t) + 1`.  The finite-sublevel
hypothesis puts every index into scope by its canonical time.  Theorem 4
then realizes the entire canonical vector, while the finite-stage Claim
3.1 tradeoffs assemble into a global Pareto-optimality proof.
-/

namespace GenLimit.ParetoGeneration

/-- The zero-based number-of-languages scheduler induced by the finite
sublevel construction in Theorem 5. -/
noncomputable abbrev finiteSublevelScheduler
    (F : Nat -> Set α)
    (hfinite : FiniteSublevels (canonicalComplexity F))
    (t : Nat) : Nat :=
  variantFiniteSublevelScheduler
    (canonicalComplexity F) hfinite t

theorem finiteSublevelScheduler_isUnbounded
    (F : Nat -> Set α)
    (hfinite : FiniteSublevels (canonicalComplexity F)) :
    IsUnboundedScheduler
      (finiteSublevelScheduler F hfinite) :=
  variantFiniteSublevelScheduler_isUnbounded
    (canonicalComplexity F) hfinite

/-- Under finite sublevels, the generalized inverse scheduler time is no
larger than the canonical generation time. -/
theorem finiteSublevel_schedulerEntryTime_le
    (F : Nat -> Set α)
    (hfinite : FiniteSublevels (canonicalComplexity F))
    (i : Nat) :
    schedulerEntryTime
        (finiteSublevelScheduler F hfinite)
        (finiteSublevelScheduler_isUnbounded F hfinite) i ≤
      canonicalComplexity F i + 1 := by
  simpa [variantCanonicalTime] using
    variant_schedulerEntryTime_le
      (canonicalComplexity F) hfinite i

/-- Therefore Theorem 4's exact max formula collapses coordinatewise to the
canonical Procedure-1 vector. -/
theorem finiteSublevel_schedulerTimeVector_eq
    (F : Nat -> Set α)
    (hfinite : FiniteSublevels (canonicalComplexity F)) :
    schedulerTimeVector F
        (finiteSublevelScheduler F hfinite)
        (finiteSublevelScheduler_isUnbounded F hfinite) =
      (fun i => canonicalComplexity F i + 1) := by
  funext i
  exact max_eq_right
    (finiteSublevel_schedulerEntryTime_le F hfinite i)

/-- Claim 3.1's finite-stage tradeoffs assemble into a global tradeoff for
the permanent canonical complexity vector. -/
theorem canonicalComplexity_earlierTradeoff
    (F : Nat -> Set α) :
    EarlierTradeoff (fun i => canonicalComplexity F i + 1)
      (RealizableTimeVectors F) := by
  intro time htime i himprove
  let current := canonicalProcedureStage F (i + 1)
  have hiStage : i < i + 1 := by omega
  have hiStable :
      current.complexity i = canonicalComplexity F i :=
    canonicalProcedureStage_complexity_stable F hiStage
  have himproveStage :
      time i < current.complexity i + 1 := by
    simpa [hiStable] using himprove
  obtain ⟨j, hj, hjWorse⟩ :=
    current.earlierPrefixTradeoff time htime i hiStage
      himproveStage
  have hjStage : j < i + 1 := hj.trans hiStage
  have hjStable :
      current.complexity j = canonicalComplexity F j :=
    canonicalProcedureStage_complexity_stable F hjStage
  exact ⟨j, hj, by simpa [hjStable] using hjWorse⟩

theorem canonicalComplexity_paretoOptimal
    (F : Nat -> Set α) :
    ParetoOptimal (RealizableTimeVectors F)
      (fun i => canonicalComplexity F i + 1) :=
  earlierTradeoff_implies_paretoOptimal
    (canonicalComplexity_earlierTradeoff F)

/-- Theorem 5, at the same distinct-history semantic boundary as Theorem 4:
finite canonical sublevels yield one generator realizing the complete
canonical Pareto-optimal time vector. -/
theorem theorem_5_exact_pareto
    [Infinite α] (F : Nat -> Set α)
    (hfinite : FiniteSublevels (canonicalComplexity F)) :
    ∃ G : HistoryGenerator α,
      AchievesTimeVector G F
        (fun i => canonicalComplexity F i + 1) ∧
      PositiveTimeVector
        (fun i => canonicalComplexity F i + 1) ∧
      ParetoOptimal (RealizableTimeVectors F)
        (fun i => canonicalComplexity F i + 1) := by
  let f := finiteSublevelScheduler F hfinite
  let hf := finiteSublevelScheduler_isUnbounded F hfinite
  let G := schedulerGenerator F f
  have hTheorem4 := theorem_4_arbitrary_scheduler F f hf
  have htimeEq :
      schedulerTimeVector F f hf =
        (fun i => canonicalComplexity F i + 1) := by
    simpa [f, hf] using
      finiteSublevel_schedulerTimeVector_eq F hfinite
  refine ⟨G, ?_, ?_, canonicalComplexity_paretoOptimal F⟩
  · simpa [G, htimeEq] using hTheorem4.1
  · intro i
    exact Nat.succ_le_succ (Nat.zero_le _)

end GenLimit.ParetoGeneration
