import GenLimit.Paper30_TimeSensitiveLanguageGeneration.DensityReduction
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.FlooredRateBudget
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.MeasureZeroDensity
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TheoremFour
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TotalizedGCGMain

/-!
# Paper 30: main-results overview

This is the public results facade for Ganju--McVoy--Dughmi--Teng,
*A Theory of Time-Sensitive Language Generation: Sparse Hallucination Beats
Mode Collapse* (arXiv:2605.11302v2).  The declarations below are thin aliases
for canonical proofs; proof bodies are not duplicated here.

## Coverage boundary

The deterministic finite-prefix, density-reduction, deadline-diagonal,
feasible-profile, measure-zero-chain, and Appendix-E arithmetic cores are
kernel-checked.  Theorem 4 / Appendix Theorem 12 now has a concrete causal
`OnTimeUnused` machine, a rank-aware stable-stage proof, and a transparent
queue-totalized repair proving eventual consistency, cofinal target
checkpoints, and instance-level upper timely density at least `1/2`.

The Kleinberg--Wei turn-taking upper endpoint is instantiated by a concrete
online adversary.  Ordinary rounds take the least unused target point and
round `2^(n+1)` catches up target-valued generator output `n`.  Lean proves
that this stream is an exact presentation, that its catch-up budget is at
most logarithmic, and hence that the repaired GCG's worst-case
instance-level timely upper density is exactly `1/2`.  The headline theorem
has no adversary certificate premise.

Theorems 1--3, Lemmas 1 and 3, Appendix Theorems 9 and 11, and the full
probabilistic parts of the paper remain open.  They require a joint
randomized-run semantics, expectations, concentration, and almost-sure
reasoning.  The repository's P09 discrete per-round distribution API is
reusable groundwork, but it does not by itself provide that process layer.

The complete claim matrix and exact qualifications are recorded in
`PaperMaps/Paper30_TimeSensitiveLanguageGeneration.md`.
-/

namespace GenLimit.TimeSensitive.Results

open Filter

/-- Deterministic pathwise counting core used by Lemma 1 and hence by
Theorems 1--2: eventual consistency bounds the credited prefix by its
intersection with an intermediate language plus a finite burn-in. -/
theorem theorems_1_2_pathwise_counting_core
    (S R : ℕ → α) (L : Set α) {T i t : ℕ}
    (hvalid : ∀ k, T ≤ k → S k ∈ L) :
    (prefixWiseElements S R (fun _ => t) i).card ≤
      targetIntersectionCount R L i + T :=
  prefix_credit_le_target_intersection_add_burnIn S R L hvalid

/-- Lemma 2 / Appendix Lemma 5's pathwise analytic endgame: a vanishing
deadline-exception ratio transfers a prefix-wise lower-density bound to the
element-wise timely metric.  Constructing the full feasible-profile pair and
transferring hallucination rates remain separate obligations. -/
theorem lemma_2_density_endgame
    (S R : ℕ → α) (hR : Function.Injective R)
    (D : Deadline) (F : ℕ → ℕ)
    (hvanishing :
      Tendsto (deadlineExceptionRatio D F) atTop (nhds 0)) :
    lowerPrefixWiseDensity S R F ≤ lowerTimelyDensity S R D :=
  lowerPrefixWiseDensity_le_lowerTimelyDensity_of_exceptionRatio
    S R hR D F hvanishing

/-- Appendix Lemmas 5--8's deterministic rate package from a raw
real-valued rate.  The composed prefix deadline's discrete convexity and the
probabilistic black-box generator are not asserted. -/
theorem appendix_D_rate_core
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (hstrict : D.EventuallyStrict)
    (H : ℕ → ℝ)
    (hH : ∀ t, 0 ≤ H t)
    (hHanti : Antitone H)
    (hvanishing : Tendsto H atTop (nhds 0))
    (hfeasible :
      NatLittleOAlongRealBudget
        (D.inverse hD.isUnbounded)
        (fun t : ℕ => (t : ℝ) * H t)) :
    let P := NaturalFeasibleProfile.ofRawRate
      D hD hstrict H hfeasible
    Antitone P.monotonePrefixRate ∧
      Tendsto P.monotonePrefixRate atTop (nhds 0) ∧
      (∀ᶠ t : ℕ in atTop, P.monotonePrefixRate t ≤ H t) ∧
      Tendsto
        (fun t =>
          natRatio
              (P.prefixDeadline.inverse
                P.prefixDeadline_isUnbounded) t /
            P.monotonePrefixRate t)
        atTop (nhds 0) :=
  NaturalFeasibleProfile.appendixD_raw_rate_monotone_prefix_estimates
    D hD hstrict H hH hHanti hvanishing hfeasible

/-- Theorem 4 / Appendix Theorem 12's reusable checkpoint-to-limsup
implication. -/
theorem theorem_4_density_endgame
    (S R : ℕ → α)
    (hcheckpoints : ∀ m N : ℕ, ∃ i : ℕ,
      N ≤ i ∧ gcgThreshold m ≤ timelyDensity S R id i) :
    (1 / 2 : ℝ) ≤ upperTimelyDensity S R id :=
  GenLimit.TimeSensitive.theorem_4_density_endgame_of_cofinal_checkpoints
    S R hcheckpoints

/-- Appendix Theorem 12 is the paper's restatement of Theorem 4, so it uses
the same qualified endpoint rather than a duplicate proof. -/
abbrev theorem_12_density_endgame := @theorem_4_density_endgame

/-- The repaired GCG construction proves eventual consistency and the
constructive `>= 1/2` half of Theorem 4 for every exact target presentation. -/
theorem theorem_4_totalized_gcg_lower
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (F.language z))
    (hfirst :
      GenLimit.KleinbergWei.DensityMeasures.FirstOccurrence F.language z) :
    (∃ T, ∀ t, T ≤ t →
      totalizedGCGOutput F stream t ∈ F.language z) ∧
    (1 / 2 : ℝ) ≤
      upperTimelyDensity (totalizedGCGOutput F stream)
        (F.order z).enumeration id :=
  GenLimit.TimeSensitive.totalizedGCG_theorem_4_lower
    F stream z hP hfirst

/-- The full equality wrapper with the operational turn-taking certificate
left explicit as a reusable intermediate theorem. -/
abbrev theorem_4_totalized_gcg_eq_of_turnTaking :=
  @GenLimit.TimeSensitive.totalizedGCG_theorem_4_eq_of_turnTaking

/-- Full repaired Theorem 4: every exact presentation attains at least one
half, and the concrete sparse adaptive exact presentation attains equality. -/
abbrev theorem_4_totalized_gcg :=
  @GenLimit.TimeSensitive.totalizedGCG_theorem_4

/-- Appendix Theorem 12 restates the same unconditional repaired result. -/
abbrev theorem_12_totalized_gcg := @theorem_4_totalized_gcg

/-- The lower half remains separately available for downstream reuse. -/
abbrev theorem_12_totalized_gcg_lower := @theorem_4_totalized_gcg_lower

end GenLimit.TimeSensitive.Results
