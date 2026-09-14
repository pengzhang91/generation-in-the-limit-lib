import GenLimit.Paper15_PartialEnumeration.Results.Overview
import GenLimit.Paper32_InfinitelyManyHallucinations.BoundedPrecision
import GenLimit.Paper32_InfinitelyManyHallucinations.Diagnostics
import GenLimit.Paper32_InfinitelyManyHallucinations.NoNovelty
import GenLimit.Paper32_InfinitelyManyHallucinations.NoNoveltyExploration

/-!
# Paper 32: main-results overview

This is the public results facade for Strauss--Butoi--Cotterell,
*Generating in the Limit with Infinitely Many Hallucinations*
(arXiv:2606.28354v1).  The declarations below are aliases of canonical
proofs; no proof is duplicated here.

## Coverage boundary

Theorem 2.1, Lemma 2.2, Proposition 2.4, Proposition 3.3, Theorem 4.3,
Lemma 4.7, the existence of the exploration schedules used by the paper, and
the appendix parrot baseline are complete semantic results.  Theorem 2.1
states explicitly the source's standing assumption that the guess exhaustion
has infinite limit and repairs the appendix's finite-valid-part case.  Theorem
4.3 uses a checked history-sensitive, capacity-preserving sparse-exploration
generator over the paper's normalized countable universe `ℕ`.

Theorems 3.5--3.6 restate P15 results.  P15 currently supplies the analytic
fixed-pod endgame of Theorem 3.5, not the full dynamic pod construction, and
has no complete matching upper-bound theorem.  Consequently Lemma 4.5 and
Theorems 4.8--4.9 are exposed only from explicit trace certificates; Lemma
4.6 and the missing pod-state-machine obligations remain open.

The appendix claim that tail precision one implies precision one omits the
infinitude of the generated language used by its proof; a checked
finite-output counterexample and the repaired infinite-output implication are
both exposed below.
-/

namespace GenLimit.InfinitelyManyHallucinations.Results

/-! ## Precision, recall, and tail precision -/

/-- Theorem 2.1: the best lower precision among target exhaustions obeying the
same pointwise batch bound as an infinite guess exhaustion equals that guess's
membership-side lower precision. -/
alias theorem_2_1 :=
  GenLimit.InfinitelyManyHallucinations.theorem_2_1

/-- Lemma 2.2: optimizing exhaustion-level lower recall over all guess
exhaustions gives the target-exhaustion coverage value. -/
alias lemma_2_2 :=
  GenLimit.InfinitelyManyHallucinations.lemma_2_2

alias proposition_2_4_single_step :=
  GenLimit.InfinitelyManyHallucinations.proposition_2_4_singleStep

alias proposition_2_4_constant_step :=
  GenLimit.InfinitelyManyHallucinations.proposition_2_4_constantStep

alias proposition_3_3 :=
  GenLimit.InfinitelyManyHallucinations.proposition_3_3

alias lemma_4_7 :=
  GenLimit.InfinitelyManyHallucinations.lemma_4_7

/-! ## Generation results -/

/-- Theorem 4.3 with the explicit capacity-preserving sparse-exploration
generator. -/
alias theorem_4_3 :=
  GenLimit.InfinitelyManyHallucinations.theorem_4_3

/-- Lemma 4.5's complete density/precision/novelty endgame, conditional on
the dynamic batched-pod trace certificate that remains to be constructed. -/
alias lemma_4_5_of_trace_certificate :=
  GenLimit.InfinitelyManyHallucinations.lemma_4_5_of_certificate

/-- Theorem 4.8's complete analytic assembly from the two algorithmic trace
guarantees; construction of the strict-novelty trace remains open. -/
alias theorem_4_8_of_trace_certificate :=
  GenLimit.InfinitelyManyHallucinations.theorem_4_8_of_certificate

/-- Theorem 4.9's complete analytic assembly from the gamma-novelty trace;
construction of the safe pod component remains open. -/
alias theorem_4_9_of_trace_certificate :=
  GenLimit.InfinitelyManyHallucinations.theorem_4_9_of_certificate

/-! ## Reused and appendix results -/

/-- The reused P15 fixed-pod limiting passage behind restated Theorem 3.5. -/
alias theorem_3_5_fixed_pod_endgame :=
  GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_3_5_fixed_pod_endgame

/-- Appendix baseline: copying the adversary preserves its lower recall and
batch bound and gives perfect precision and tail precision. -/
alias appendix_valid_generation_without_novelty :=
  GenLimit.InfinitelyManyHallucinations.valid_generation_without_novelty

/-- A gamma-admissible exploration set exists for every `γ < 1`. -/
alias gamma_admissible_exploration_exists :=
  GenLimit.InfinitelyManyHallucinations.exists_gammaAdmissible_explorationSet

/-- Diagnostic for the appendix lemma missing an infinite-output premise. -/
alias tail_precision_one_finite_guess_counterexample :=
  GenLimit.InfinitelyManyHallucinations.tail_precision_one_finite_guess_counterexample

/-- Repaired Appendix Lemma D.1: for an exhaustion with infinitely many
distinct outputs, lower tail precision one implies lower membership precision
one. -/
alias appendix_lemma_D_1_of_limit_infinite :=
  GenLimit.InfinitelyManyHallucinations.appendix_lemma_D_1_of_limit_infinite

end GenLimit.InfinitelyManyHallucinations.Results
