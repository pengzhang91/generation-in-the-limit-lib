import GenLimit.Paper32_InfinitelyManyHallucinations.TailPrecision

/-!
# Diagnostics for Paper 32

The appendix lemma "tail precision 1 implies precision 1" uses, in its
proof, that the cumulative guess cardinality tends to infinity.  That
hypothesis is absent from the printed lemma statement.  This module records
the finite-output obstruction: one invalid output followed by empty batches
has lower tail precision one, but lower membership precision zero.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

/-- A guess that emits the invalid value `0` once and then stops. -/
def oneShotInvalidExhaustion : Exhaustion where
  stage n := if n = 0 then ∅ else {0}
  stage_zero := by simp
  monotone_stage := by
    intro m n hmn
    by_cases hm : m = 0
    · simp [hm]
    · have hn : n ≠ 0 := by omega
      simp [hm, hn]

@[simp] theorem oneShotInvalidExhaustion_stage_zero :
    oneShotInvalidExhaustion.stage 0 = ∅ :=
  rfl

@[simp] theorem oneShotInvalidExhaustion_stage_succ (n : ℕ) :
    oneShotInvalidExhaustion.stage (n + 1) = {0} := by
  simp [oneShotInvalidExhaustion]

@[simp] theorem oneShotInvalidExhaustion_increment_zero :
    oneShotInvalidExhaustion.increment 0 = ∅ :=
  rfl

@[simp] theorem oneShotInvalidExhaustion_increment_one :
    oneShotInvalidExhaustion.increment 1 = {0} := by
  simp [Exhaustion.increment]

@[simp] theorem oneShotInvalidExhaustion_increment_succ_succ (n : ℕ) :
    oneShotInvalidExhaustion.increment (n + 2) = ∅ := by
  simp [Exhaustion.increment, Nat.add_assoc]

/-- The literal appendix implication is false without an infinite-output
hypothesis.  The two conjuncts give the exact obstruction. -/
theorem tail_precision_one_finite_guess_counterexample :
    lowerTailPrecision (∅ : Language) oneShotInvalidExhaustion = 1 ∧
      lowerMembershipPrecision (∅ : Language) oneShotInvalidExhaustion = 0 := by
  constructor
  · have heventual :
        (fun n => stepTailPrecision (∅ : Language)
          oneShotInvalidExhaustion n) =ᶠ[atTop]
            (fun _ : ℕ => (1 : ℝ)) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero => omega
          | succ n => simp [stepTailPrecision]
    have htendsto :
        Tendsto
          (stepTailPrecision (∅ : Language) oneShotInvalidExhaustion)
          atTop (nhds 1) :=
      tendsto_const_nhds.congr' heventual.symm
    exact htendsto.liminf_eq
  · have hzero : ∀ n,
        membershipFraction (∅ : Language)
          (oneShotInvalidExhaustion.stage n) = 0 := by
      intro n
      simp [membershipFraction_eq, countIn_eq_filter_card]
    unfold lowerMembershipPrecision
    have htendsto :
        Tendsto
          (fun n => membershipFraction (∅ : Language)
            (oneShotInvalidExhaustion.stage n))
          atTop (nhds 0) := by
      simpa only [hzero] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    exact htendsto.liminf_eq

end GenLimit.InfinitelyManyHallucinations
