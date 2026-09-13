import GenLimit.Paper32_InfinitelyManyHallucinations.Exploration
import GenLimit.Paper32_InfinitelyManyHallucinations.Novelty
import GenLimit.Paper32_InfinitelyManyHallucinations.Precision
import GenLimit.Paper32_InfinitelyManyHallucinations.Recall
import GenLimit.Paper32_InfinitelyManyHallucinations.TailPrecision

/-!
# Checked endgames for the Paper 32 algorithms

The source algorithms combine a Kleinberg--Wei safe routine with sparse
exploration.  This module isolates the exact trace certificates needed by the
main theorem proofs and verifies every analytic and density-combination step.
Constructing those certificates from the full pod-state machines is kept
separate, so the public API does not hide which algorithmic obligations are
still open.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter
open GenLimit.KleinbergWei

/-- The common sparse-error certificate: stage cardinalities diverge, and
every invalid output can be charged to an exploration position no larger
than the current output cardinality. -/
structure SparseExplorationCertificate
    (E : ExplorationSet) (L : Language) (guess : Exhaustion) where
  card_tendsto_atTop : Tendsto (fun n => (guess.stage n).card) atTop atTop
  invalid_le_exploration : ∀ n,
    invalidCount L (guess.stage n) ≤
      explorationCount E.carrier (guess.stage n).card

namespace SparseExplorationCertificate

/-- Sparse exploration gives membership precision one.  This is the shared
analytic endgame of Theorems 4.3, 4.8, and 4.9. -/
theorem precision_one
    {E : ExplorationSet} {L : Language} {guess : Exhaustion}
    (hcert : SparseExplorationCertificate E L guess) :
    lowerMembershipPrecision L guess = 1 := by
  have hpositive :
      ∀ᶠ n : ℕ in atTop, (guess.stage n).card ≠ 0 := by
    filter_upwards
      [hcert.card_tendsto_atTop.eventually (eventually_ge_atTop 1)]
      with n hn
    omega
  let error : ℕ → ℝ := fun n =>
    (explorationCount E.carrier (guess.stage n).card : ℝ) /
      ((guess.stage n).card : ℝ)
  have herror : Tendsto error atTop (nhds 0) :=
    E.prefixRatio_tendsto_zero.comp hcert.card_tendsto_atTop
  apply lowerMembershipPrecision_eq_one_of_error_envelope
    hpositive _ herror
  filter_upwards [hpositive] with n hn
  have hraw := invalidFraction_le_of_count_le L
    (hcert.invalid_le_exploration n)
  simpa [error, hn] using hraw

end SparseExplorationCertificate

/-- Variant used when exploration is scheduled by an external monotone size
clock (Algorithm 4.3 uses the amount of adversarial progress).  The final
field says that the output can lag behind that clock only by the number of
exploration positions. -/
structure ControlledSparseExplorationCertificate
    (E : ExplorationSet) (L : Language) (guess : Exhaustion) where
  control : ℕ → ℕ
  control_tendsto_atTop : Tendsto control atTop atTop
  invalid_le_exploration : ∀ n,
    invalidCount L (guess.stage n) ≤ explorationCount E.carrier (control n)
  control_le_guess_add_exploration : ∀ n,
    control n ≤ (guess.stage n).card + explorationCount E.carrier (control n)

namespace ControlledSparseExplorationCertificate

theorem precision_one
    {E : ExplorationSet} {L : Language} {guess : Exhaustion}
    (hcert : ControlledSparseExplorationCertificate E L guess) :
    lowerMembershipPrecision L guess = 1 := by
  let errorRatio : ℕ → ℝ := fun n =>
    (explorationCount E.carrier (hcert.control n) : ℝ) /
      (hcert.control n : ℝ)
  have hratio : Tendsto errorRatio atTop (nhds 0) :=
    E.prefixRatio_tendsto_zero.comp hcert.control_tendsto_atTop
  have hcontrolPositive :
      ∀ᶠ n : ℕ in atTop, 0 < hcert.control n :=
    hcert.control_tendsto_atTop.eventually (eventually_gt_atTop 0)
  have hratioHalf :
      ∀ᶠ n : ℕ in atTop, errorRatio n < (1 / 2 : ℝ) :=
    (tendsto_order.1 hratio).2 (1 / 2 : ℝ) (by norm_num)
  have hguessPositive :
      ∀ᶠ n : ℕ in atTop, (guess.stage n).card ≠ 0 := by
    filter_upwards [hcontrolPositive, hratioHalf] with n hcontrol hhalf
    let e := explorationCount E.carrier (hcert.control n)
    let g := (guess.stage n).card
    let c := hcert.control n
    have hcReal : (0 : ℝ) < c := by exact_mod_cast hcontrol
    have htwoE : (2 : ℝ) * e < c := by
      have := (div_lt_iff₀ hcReal).mp hhalf
      dsimp only [errorRatio, e, c] at this ⊢
      nlinarith
    have hlag : c ≤ g + e := by
      simpa [c, g, e] using hcert.control_le_guess_add_exploration n
    have htwoENat : 2 * e ≤ c := by exact_mod_cast htwoE.le
    have : 0 < g := by omega
    exact Nat.ne_of_gt this
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        invalidFraction L (guess.stage n) ≤ 2 * errorRatio n := by
    filter_upwards [hcontrolPositive, hratioHalf, hguessPositive]
      with n hcontrol hhalf hguess
    let e := explorationCount E.carrier (hcert.control n)
    let g := (guess.stage n).card
    let c := hcert.control n
    have hcReal : (0 : ℝ) < c := by exact_mod_cast hcontrol
    have hgReal : (0 : ℝ) < g := by
      exact_mod_cast Nat.pos_of_ne_zero hguess
    have htwoE : (2 : ℝ) * e ≤ c := by
      have := (div_lt_iff₀ hcReal).mp hhalf
      dsimp only [errorRatio, e, c] at this ⊢
      linarith
    have hlagReal : (c : ℝ) ≤ (g : ℝ) + (e : ℝ) := by
      exact_mod_cast hcert.control_le_guess_add_exploration n
    have heLeG : (e : ℝ) ≤ (g : ℝ) := by linarith
    have heOverG : (e : ℝ) / (g : ℝ) ≤
        2 * ((e : ℝ) / (c : ℝ)) := by
      rw [show 2 * ((e : ℝ) / (c : ℝ)) =
          (2 * (e : ℝ)) / (c : ℝ) by ring]
      rw [div_le_div_iff₀ hgReal hcReal]
      calc
        (e : ℝ) * c ≤ (e : ℝ) * (g + e) :=
          mul_le_mul_of_nonneg_left hlagReal (Nat.cast_nonneg e)
        _ = (e : ℝ) * g + (e : ℝ) * e := by ring
        _ ≤ (e : ℝ) * g + (e : ℝ) * g :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left heLeG (Nat.cast_nonneg e)) _
        _ = (2 * (e : ℝ)) * g := by ring
    have hinvalid := invalidFraction_le_of_count_le L
      (hcert.invalid_le_exploration n)
    have hinvalid' :
        invalidFraction L (guess.stage n) ≤ (e : ℝ) / (g : ℝ) := by
      simpa [e, g, hguess] using hinvalid
    simpa [errorRatio, e, c] using hinvalid'.trans heOverG
  apply lowerMembershipPrecision_eq_one_of_error_envelope
    hguessPositive hbound
  have htwo :
      Tendsto (fun n => 2 * errorRatio n) atTop (nhds (2 * 0)) :=
    tendsto_const_nhds.mul hratio
  simpa using htwo

end ControlledSparseExplorationCertificate

/-- The exact trace obligations of Algorithm 4.3 (no novelty). -/
structure NoNoveltyCertificate
    (E : ExplorationSet) (L : Language) (f : ℕ → ℕ)
    (guess : Exhaustion) where
  sparse : SparseExplorationCertificate E L guess
  bounded : guess.BoundedBy f
  covers_universe : (Set.univ : Language) ⊆ guess.limit

/-- Theorem 4.3's conclusion from the concrete algorithm's trace
certificates. -/
theorem theorem_4_3_of_certificate
    (target : OrderedLanguage) (E : ExplorationSet)
    (L : Language) (f : ℕ → ℕ) (guess : Exhaustion)
    (hcert : NoNoveltyCertificate E L f guess) :
    guess.BoundedBy f ∧
      lowerRecall target guess.limit = 1 ∧
      lowerMembershipPrecision L guess = 1 := by
  refine ⟨hcert.bounded, ?_, hcert.sparse.precision_one⟩
  apply lowerRecall_eq_one_of_target_subset
  exact fun x _hx => hcert.covers_universe (Set.mem_univ x)

/-- A source-shaped certificate for the `k`-batched pods lower bound.  The
eventual prefix inequality is precisely the output of the appendix charging
argument; all limit arithmetic is checked below. -/
structure BatchedPodsCertificate
    (target : OrderedLanguage) (L : Language)
    (adversary guess : Exhaustion) (k : ℕ) where
  overhead : ℕ → ℝ
  overhead_tendsto_zero : Tendsto overhead atTop (nhds 0)
  prefix_bound : ∀ᶠ n : ℕ in atTop,
    target.prefixRatio adversary.limit n ≤
      (k + 1 : ℕ) * target.prefixRatio guess.limit n + overhead n
  novel : Novel adversary guess
  precision_one : lowerMembershipPrecision L guess = 1
  tail_precision_one : lowerTailPrecision L guess = 1

namespace BatchedPodsCertificate

theorem lowerRecall_div
    {target : OrderedLanguage} {L : Language}
    {adversary guess : Exhaustion} {k : ℕ}
    (hcert : BatchedPodsCertificate target L adversary guess k) :
    lowerRecall target adversary.limit / (k + 1 : ℕ) ≤
      lowerRecall target guess.limit := by
  unfold lowerRecall
  apply OrderedLanguage.lowerDensity_div_le_of_eventually_prefixRatio_le
    target adversary.limit guess.limit (k + 1 : ℕ) (by positivity)
    hcert.overhead hcert.overhead_tendsto_zero hcert.prefix_bound

end BatchedPodsCertificate

/-- Lemma 4.5's numerical conclusion, once the batched pod construction has
supplied its charging certificate. -/
theorem lemma_4_5_of_certificate
    {target : OrderedLanguage} {L : Language}
    {adversary guess : Exhaustion} {k : ℕ}
    (hcert : BatchedPodsCertificate target L adversary guess k)
    {α : ℝ} (hα : α ≤ lowerRecall target adversary.limit) :
    α / (k + 1 : ℕ) ≤ lowerRecall target guess.limit ∧
      Novel adversary guess ∧
      lowerMembershipPrecision L guess = 1 ∧
      lowerTailPrecision L guess = 1 := by
  refine ⟨?_, hcert.novel, hcert.precision_one, hcert.tail_precision_one⟩
  exact (div_le_div_of_nonneg_right hα (by positivity)).trans
    hcert.lowerRecall_div

/-- The exact trace obligations used for the strict-novelty construction in
Theorem 4.8. -/
structure StrictNoveltyCertificate
    (E : ExplorationSet) (target : OrderedLanguage)
    (L : Language) (adversary guess : Exhaustion) where
  sparse : SparseExplorationCertificate E L guess
  novel : Novel adversary guess
  recovers_unrevealed : target.carrier \ adversary.limit ⊆ guess.limit
  safe_third : lowerRecall target adversary.limit / 3 ≤
    lowerRecall target guess.limit

/-- Theorem 4.8's precision and `max(1-β, α/3)` recall conclusion from its
two independently checkable output guarantees.  Novelty is returned as the
certificate's trace predicate. -/
theorem theorem_4_8_of_certificate
    (E : ExplorationSet) (target : OrderedLanguage)
    (L : Language) (adversary guess : Exhaustion)
    (hcert : StrictNoveltyCertificate E target L adversary guess) :
    Novel adversary guess ∧
      lowerMembershipPrecision L guess = 1 ∧
      max (1 - upperRecall target adversary.limit)
          (lowerRecall target adversary.limit / 3) ≤
        lowerRecall target guess.limit := by
  refine ⟨hcert.novel, hcert.sparse.precision_one, ?_⟩
  rw [max_le_iff]
  exact ⟨lemma_4_7 target adversary.limit guess.limit
      hcert.recovers_unrevealed,
    hcert.safe_third⟩

/-- The trace obligations of Algorithm 4.9: sparse errors, the required
finite-prefix novelty quota, and exhaustive ambient exploration. -/
structure GammaNoveltyCertificate
    (E : ExplorationSet) (γ : ℝ)
    (L : Language) (adversary guess : Exhaustion) where
  sparse : SparseExplorationCertificate E L guess
  admissible : E.GammaAdmissible γ
  nonNovel_le_exploration : ∀ n,
    (guess.stage n \ novelHistory adversary guess n).card ≤
      explorationCount E.carrier (guess.stage n).card
  covers_universe : (Set.univ : Language) ⊆ guess.limit

/-- Theorem 4.9's full semantic conclusion from the algorithm trace. -/
theorem theorem_4_9_of_certificate
    (E : ExplorationSet) (γ : ℝ)
    (target : OrderedLanguage) (L : Language)
    (adversary guess : Exhaustion)
    (hcert : GammaNoveltyCertificate E γ L adversary guess) :
    GammaNovel γ adversary guess ∧
      lowerRecall target guess.limit = 1 ∧
      lowerMembershipPrecision L guess = 1 := by
  refine ⟨gammaNovel_of_nonNovel_le_exploration hcert.admissible
      adversary guess hcert.nonNovel_le_exploration,
    ?_, hcert.sparse.precision_one⟩
  apply lowerRecall_eq_one_of_target_subset
  exact fun x _hx => hcert.covers_universe (Set.mem_univ x)

end GenLimit.InfinitelyManyHallucinations
