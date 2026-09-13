import GenLimit.Paper32_InfinitelyManyHallucinations.SupremumCharacterizations

/-!
# Paper 32, Theorem 2.1: bounded membership precision

The source proof splits according to the cumulative number of invalid guess
increments.  Its second case uses infinitude of the guess language without
restating the standing hypothesis, and its exact-cardinality assertion fails
when an auxiliary difference language is finite.

The proof below makes the standing infinite-guess hypothesis explicit and
uses an equivalent, total case split.  If the valid part of the guess is
finite, its membership fraction tends to zero.  If it is infinite, the
capacity-preserving sparse scheduler from Theorem 4.3 completes the valid
part to a target exhaustion while losing only a vanishing fraction of valid
guess elements.  This avoids both source-proof defects and preserves the
same pointwise `f` bound.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

/-- The valid part of a guess exhaustion. -/
noncomputable def validPartExhaustion
    (L : Language) (guess : Exhaustion) : Exhaustion :=
  restrictedExhaustion guess L

theorem validPartExhaustion_stage_card
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    ((validPartExhaustion L guess).stage n).card =
      countIn L (guess.stage n) := by
  classical
  simp [validPartExhaustion, restrictedExhaustion,
    finiteRestriction, countIn]

theorem validPartExhaustion_limit
    (L : Language) (guess : Exhaustion) :
    (validPartExhaustion L guess).limit = guess.limit ∩ L :=
  restrictedExhaustion_limit guess L

theorem validPartExhaustion_boundedBy
    (L : Language) {guess : Exhaustion} {f : ℕ → ℕ}
    (hbounded : guess.BoundedBy f) :
    (validPartExhaustion L guess).BoundedBy f :=
  restrictedExhaustion_boundedBy hbounded

/-- If only finitely many generated values are valid while the guess limit
is infinite, the membership precision is zero. -/
theorem lowerMembershipPrecision_eq_zero_of_validPart_finite
    (L : Language) (guess : Exhaustion)
    (hguessInfinite : guess.limit.Infinite)
    (hvalidFinite : (validPartExhaustion L guess).limit.Finite) :
    lowerMembershipPrecision L guess = 0 := by
  classical
  let B := hvalidFinite.toFinset.card
  have hcount : ∀ n, countIn L (guess.stage n) ≤ B := by
    intro n
    unfold countIn
    apply Finset.card_le_card
    intro x hx
    apply Set.Finite.mem_toFinset hvalidFinite |>.2
    exact ⟨n, by
      simpa [validPartExhaustion, restrictedExhaustion,
        finiteRestriction] using hx⟩
  have hcardNat :
      Tendsto (fun n => (guess.stage n).card) atTop atTop :=
    guess.card_tendsto_atTop_of_limit_infinite hguessInfinite
  have hcardReal :
      Tendsto (fun n => ((guess.stage n).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcardNat
  have hmajorant :
      Tendsto (fun n => (B : ℝ) / ((guess.stage n).card : ℝ))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hcardReal
  have htendsto :
      Tendsto (fun n => membershipFraction L (guess.stage n))
        atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => membershipFraction_nonneg L (guess.stage n))
      _ hmajorant
    intro n
    by_cases hstage : (guess.stage n).card = 0
    · simp [membershipFraction, hstage]
    · simp only [membershipFraction, hstage, if_false]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast hcount n) (Nat.cast_nonneg _)
  exact htendsto.liminf_eq

/-! ## Sparse capacity-preserving completion -/

/-- Run the existing capacity-preserving sparse scheduler on the valid part
of the guess and then restrict its ambient exploration back to the target.
The result is a genuine target exhaustion, not merely a trace certificate. -/
noncomputable def sparsePrecisionTarget
    (L : Language) (guess : Exhaustion) : Exhaustion :=
  restrictedExhaustion
    (generatedExhaustion
      (noNoveltyExplorationGenerator 2)
      (validPartExhaustion L guess))
    L

theorem sparsePrecisionTarget_exhausts
    (L : Language) (guess : Exhaustion)
    (hvalidInfinite : (validPartExhaustion L guess).limit.Infinite) :
    (sparsePrecisionTarget L guess).Exhausts L := by
  unfold Exhaustion.Exhausts
  rw [sparsePrecisionTarget, restrictedExhaustion_limit]
  apply Set.Subset.antisymm
  · exact Set.inter_subset_right
  · intro x hxL
    refine ⟨?_, hxL⟩
    exact noNoveltyExplorationGenerator_covers_universe
      (by decide) (validPartExhaustion L guess) hvalidInfinite
      (Set.mem_univ x)

theorem sparsePrecisionTarget_boundedBy
    (L : Language) {guess : Exhaustion} {f : ℕ → ℕ}
    (hbounded : guess.BoundedBy f) :
    (sparsePrecisionTarget L guess).BoundedBy f := by
  apply restrictedExhaustion_boundedBy
  apply generated_boundedBy_noNoveltyExplorationGenerator
    (spacing := 2) (by decide) f
  exact validPartExhaustion_boundedBy L hbounded

/-- The target-stage overlap misses no more valid guess elements than the
number of quadratic exploration positions already crossed. -/
theorem validCount_le_sparseTargetCount_add_exploration
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    countIn L (guess.stage n) ≤
      countIn ((sparsePrecisionTarget L guess).stage n : Language)
          (guess.stage n) +
        explorationCount (quadraticCarrier 2)
          (countIn L (guess.stage n)) := by
  classical
  let valid := validPartExhaustion L guess
  let generated :=
    generatedExhaustion (noNoveltyExplorationGenerator 2) valid
  have hmissing :
      (valid.stage n \
          generatedStages (noNoveltyExplorationGenerator 2) valid n).card ≤
        explorationCount (quadraticCarrier 2) (valid.stage n).card := by
    rw [← explorationIndexPrefix_card_eq_explorationCount
      (spacing := 2) (by decide)]
    exact adversary_missing_generated_card_le_explorationPrefix
      (spacing := 2) (by decide) valid n
  have hvalidCard :
      (valid.stage n).card = countIn L (guess.stage n) := by
    exact validPartExhaustion_stage_card L guess n
  have hoverlap :
      (valid.stage n ∩ generated.stage n).card =
        countIn ((sparsePrecisionTarget L guess).stage n : Language)
          (guess.stage n) := by
    unfold countIn
    congr 1
    ext x
    simp [valid, generated, validPartExhaustion,
      sparsePrecisionTarget, restrictedExhaustion, finiteRestriction,
      generatedExhaustion]
    tauto
  rw [← hvalidCard, ← hoverlap]
  calc
    (valid.stage n).card =
        (valid.stage n ∩ generated.stage n).card +
          (valid.stage n \ generated.stage n).card := by
      exact (Finset.card_inter_add_card_sdiff
        (valid.stage n) (generated.stage n)).symm
    _ ≤ (valid.stage n ∩ generated.stage n).card +
          explorationCount (quadraticCarrier 2) (valid.stage n).card :=
      Nat.add_le_add_left hmissing _

/-- Vanishing error term used to compare the two precision sequences. -/
noncomputable def sparsePrecisionError
    (L : Language) (guess : Exhaustion) (n : ℕ) : ℝ :=
  if (guess.stage n).card = 0 then 0
  else
    (explorationCount (quadraticCarrier 2)
      (countIn L (guess.stage n)) : ℝ) /
      (guess.stage n).card

theorem sparsePrecisionError_nonneg
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    0 ≤ sparsePrecisionError L guess n := by
  unfold sparsePrecisionError
  split_ifs
  · exact le_rfl
  · positivity

theorem sparsePrecisionError_tendsto_zero
    (L : Language) (guess : Exhaustion)
    (hvalidInfinite : (validPartExhaustion L guess).limit.Infinite) :
    Tendsto (sparsePrecisionError L guess) atTop (nhds 0) := by
  have hvalidCard :
      Tendsto (fun n => countIn L (guess.stage n)) atTop atTop := by
    simpa only [validPartExhaustion_stage_card] using
      (validPartExhaustion L guess).card_tendsto_atTop_of_limit_infinite
        hvalidInfinite
  have hquadratic :
      Tendsto
        (fun n =>
          (explorationCount (quadraticCarrier 2)
            (countIn L (guess.stage n)) : ℝ) /
              (countIn L (guess.stage n) : ℝ))
        atTop (nhds 0) :=
    (quadratic_prefixRatio_tendsto_zero (spacing := 2) (by decide)).comp
      hvalidCard
  apply squeeze_zero'
  · exact Eventually.of_forall
      (sparsePrecisionError_nonneg L guess)
  · have hpositive :
        ∀ᶠ n : ℕ in atTop, 0 < countIn L (guess.stage n) :=
      hvalidCard.eventually (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hguessPositive : 0 < (guess.stage n).card :=
      lt_of_lt_of_le hn (countIn_le L (guess.stage n))
    simp only [sparsePrecisionError, Nat.ne_of_gt hguessPositive,
      if_false]
    have hnReal :
        (0 : ℝ) < (countIn L (guess.stage n) : ℝ) := by
      exact_mod_cast hn
    have hcountReal :
        (countIn L (guess.stage n) : ℝ) ≤
          ((guess.stage n).card : ℝ) := by
      exact_mod_cast countIn_le L (guess.stage n)
    exact div_le_div_of_nonneg_left
      (Nat.cast_nonneg _)
      hnReal hcountReal
  · exact hquadratic

theorem membershipFraction_le_sparseTargetFraction_add_error
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    membershipFraction L (guess.stage n) ≤
      membershipFraction
          ((sparsePrecisionTarget L guess).stage n : Language)
          (guess.stage n) +
        sparsePrecisionError L guess n := by
  have hcount := validCount_le_sparseTargetCount_add_exploration
    L guess n
  by_cases hstage : (guess.stage n).card = 0
  · simp [membershipFraction, sparsePrecisionError, hstage]
  · simp only [membershipFraction, sparsePrecisionError, hstage,
      if_false]
    rw [← add_div]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast hcount) (Nat.cast_nonneg _)

/-! ## A general liminf perturbation lemma -/

theorem liminf_le_liminf_of_eventually_le_add_tendsto_zero
    {u v error : ℕ → ℝ}
    (huNonneg : ∀ n, 0 ≤ u n) (huOne : ∀ n, u n ≤ 1)
    (hvOne : ∀ n, v n ≤ 1)
    (hcompare : ∀ᶠ n in atTop, u n ≤ v n + error n)
    (herror : Tendsto error atTop (nhds 0)) :
    liminf u atTop ≤ liminf v atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have herrorSmall : ∀ᶠ n in atTop, error n ≤ ε :=
    ((tendsto_order.1 herror).2 ε hε).mono fun _ h => h.le
  have hshift : ∀ᶠ n in atTop, u n - ε ≤ v n := by
    filter_upwards [hcompare, herrorSmall] with n hcomp herr
    linarith
  have hlim :
      liminf (fun n => u n - ε) atTop ≤ liminf v atTop := by
    exact liminf_le_liminf hshift
      (isBoundedUnder_of ⟨-ε, fun n => by
        linarith [huNonneg n]⟩)
      (isCoboundedUnder_ge_of_le atTop hvOne)
  rw [liminf_sub_const atTop u ε
    (isCoboundedUnder_ge_of_le atTop huOne)
    (isBoundedUnder_of ⟨0, huNonneg⟩)] at hlim
  linarith

theorem sparsePrecisionTarget_lowerPrecision
    (L : Language) (guess : Exhaustion)
    (hvalidInfinite : (validPartExhaustion L guess).limit.Infinite) :
    exhaustionLowerPrecision (sparsePrecisionTarget L guess) guess =
      lowerMembershipPrecision L guess := by
  apply le_antisymm
  · exact exhaustionLowerPrecision_le_membership
      (sparsePrecisionTarget L guess) guess L
      (sparsePrecisionTarget_exhausts L guess hvalidInfinite)
  · unfold exhaustionLowerPrecision lowerMembershipPrecision
    apply liminf_le_liminf_of_eventually_le_add_tendsto_zero
    · exact fun n => membershipFraction_nonneg L (guess.stage n)
    · exact fun n => membershipFraction_le_one L (guess.stage n)
    · exact fun n => membershipFraction_le_one
        ((sparsePrecisionTarget L guess).stage n : Language)
        (guess.stage n)
    · exact Eventually.of_forall
        (membershipFraction_le_sparseTargetFraction_add_error L guess)
    · exact sparsePrecisionError_tendsto_zero
        L guess hvalidInfinite

theorem boundedLowerPrecisionValues_bddAbove
    (f : ℕ → ℕ) (L : Language) (guess : Exhaustion) :
    BddAbove (boundedLowerPrecisionValues f L guess) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨target, _hexhausts, _hbounded, rfl⟩ := hr
  exact exhaustionLowerPrecision_le_one target guess

/-- Theorem 2.1, with the paper's standing infinitude of the guess language
made explicit.  Existence of the infinite `f`-bounded guess already implies
the usable cumulative capacity condition on `f`. -/
theorem theorem_2_1
    (f : ℕ → ℕ) (L : Language) (guess : Exhaustion)
    (hguessInfinite : guess.limit.Infinite)
    (hguessBounded : guess.BoundedBy f) :
    bestBoundedLowerPrecision f L guess =
      lowerMembershipPrecision L guess := by
  apply le_antisymm
  · exact bestBoundedLowerPrecision_le_membership
      f L guess hguessInfinite hguessBounded
  · by_cases hvalidFinite :
        (validPartExhaustion L guess).limit.Finite
    · have hzero := lowerMembershipPrecision_eq_zero_of_validPart_finite
        L guess hguessInfinite hvalidFinite
      rw [hzero]
      let target := cardinalityClockedExhaustion L guess
      exact (exhaustionLowerPrecision_nonneg target guess).trans
        (le_csSup
          (boundedLowerPrecisionValues_bddAbove f L guess)
          ⟨target,
            cardinalityClockedExhaustion_exhausts
              L guess hguessInfinite,
            cardinalityClockedExhaustion_boundedBy L hguessBounded,
            rfl⟩)
    · have hvalidInfinite :
          (validPartExhaustion L guess).limit.Infinite := hvalidFinite
      rw [← sparsePrecisionTarget_lowerPrecision
        L guess hvalidInfinite]
      exact le_csSup
        (boundedLowerPrecisionValues_bddAbove f L guess)
        ⟨sparsePrecisionTarget L guess,
          sparsePrecisionTarget_exhausts L guess hvalidInfinite,
          sparsePrecisionTarget_boundedBy L hguessBounded,
          rfl⟩

end GenLimit.InfinitelyManyHallucinations
