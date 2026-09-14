import GenLimit.Paper32_InfinitelyManyHallucinations.Precision
import Mathlib.Order.Filter.Finite

/-!
# Tail precision and eventual validity

This module formalizes Proposition 2.4's single-step clause and Proposition
3.3 of Strauss--Butoi--Cotterell, arXiv:2606.28354v1.  The latter is the exact
equivalence between eventual validity and finite-time stabilization of
step-wise tail precision at one.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

theorem countIn_eq_card_iff (L : Language) (S : Finset ℕ) :
    countIn L S = S.card ↔ (S : Set ℕ) ⊆ L := by
  classical
  unfold countIn
  simpa using (Finset.card_filter_eq_iff (s := S) (p := fun x => x ∈ L))

theorem stepTailPrecision_nonneg
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    0 ≤ stepTailPrecision L guess n := by
  by_cases hzero : (guess.increment n).card = 0
  · simp [stepTailPrecision, hzero]
  · simp only [stepTailPrecision, hzero, if_false]
    positivity

theorem stepTailPrecision_le_one
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    stepTailPrecision L guess n ≤ 1 := by
  by_cases hzero : (guess.increment n).card = 0
  · simp [stepTailPrecision, hzero]
  · simp only [stepTailPrecision, hzero, if_false]
    have hpos : (0 : ℝ) < (guess.increment n).card := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast countIn_le L (guess.increment n)

/-- A step has tail precision one exactly when every newly generated string
is target-valid.  Empty steps satisfy both sides. -/
theorem stepTailPrecision_eq_one_iff
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    stepTailPrecision L guess n = 1 ↔
      (guess.increment n : Set ℕ) ⊆ L := by
  by_cases hzero : (guess.increment n).card = 0
  · have hempty : guess.increment n = ∅ := Finset.card_eq_zero.mp hzero
    simp [stepTailPrecision, hempty]
  · simp only [stepTailPrecision, hzero, if_false]
    constructor
    · intro hratio
      have hdenom : ((guess.increment n).card : ℝ) ≠ 0 := by
        exact_mod_cast hzero
      have hcast :
          (countIn L (guess.increment n) : ℝ) =
            ((guess.increment n).card : ℝ) :=
        (div_eq_one_iff_eq hdenom).mp hratio
      apply (countIn_eq_card_iff L (guess.increment n)).mp
      exact_mod_cast hcast
    · intro hsubset
      have hcount :=
        (countIn_eq_card_iff L (guess.increment n)).mpr hsubset
      rw [hcount]
      exact div_self (by exact_mod_cast hzero)

/-- Proposition 3.3: eventual validity is exactly finite-time stabilization
of tail precision at one. -/
theorem proposition_3_3
    (L : Language) (guess : Exhaustion) :
    EventuallyValid L guess ↔
      TailPrecisionOneFromFiniteTime L guess := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn =>
      (stepTailPrecision_eq_one_iff L guess n).mpr (hN n hn)⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn =>
      (stepTailPrecision_eq_one_iff L guess n).mp (hN n hn)⟩

theorem lowerTailPrecision_nonneg (L : Language) (guess : Exhaustion) :
    0 ≤ lowerTailPrecision L guess := by
  unfold lowerTailPrecision
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => stepTailPrecision_le_one L guess n)
  · exact Eventually.of_forall
      (fun n => stepTailPrecision_nonneg L guess n)

theorem lowerTailPrecision_le_one (L : Language) (guess : Exhaustion) :
    lowerTailPrecision L guess ≤ 1 := by
  unfold lowerTailPrecision
  apply liminf_le_of_frequently_le
  · exact (Eventually.of_forall
      (fun n => stepTailPrecision_le_one L guess n)).frequently
  · exact isBoundedUnder_of
      ⟨0, fun n => stepTailPrecision_nonneg L guess n⟩

/-! ## Appendix D: tail precision one implies precision one -/

/-- Step-wise tail precision and the rejected fraction of the same increment
are exact complements, including at empty steps under the paper's convention. -/
theorem stepTailPrecision_eq_one_sub_invalidFraction
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    stepTailPrecision L guess n =
      1 - invalidFraction L (guess.increment n) := by
  by_cases hzero : (guess.increment n).card = 0
  · simp [stepTailPrecision, invalidFraction_eq, hzero]
  · simpa [stepTailPrecision, membershipFraction_eq, hzero] using
      membershipFraction_eq_one_sub_invalidFraction
        L (S := guess.increment n) hzero

/-- Rejected counts add across disjoint finite samples. -/
theorem invalidCount_union_of_disjoint
    (L : Language) {S T : Finset ℕ} (hdisjoint : Disjoint S T) :
    invalidCount L (S ∪ T) = invalidCount L S + invalidCount L T := by
  classical
  simp only [invalidCount_eq_filter_card, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

theorem invalidCount_stage_succ
    (L : Language) (guess : Exhaustion) (n : ℕ) :
    invalidCount L (guess.stage (n + 1)) =
      invalidCount L (guess.stage n) +
        invalidCount L (guess.increment (n + 1)) := by
  rw [guess.stage_succ_eq_stage_union_increment]
  exact invalidCount_union_of_disjoint L
    (guess.increment_disjoint_previous n).symm

theorem card_stage_succ
    (guess : Exhaustion) (n : ℕ) :
    (guess.stage (n + 1)).card =
      (guess.stage n).card + (guess.increment (n + 1)).card := by
  rw [guess.stage_succ_eq_stage_union_increment]
  exact Finset.card_union_of_disjoint
    (guess.increment_disjoint_previous n).symm

/-- If every increment after a prefix has rejected fraction at most `ε`,
then the cumulative rejected count is bounded by the prefix error plus
`ε` times the cumulative output count. -/
theorem invalidCount_stage_le_prefix_add_rate
    {L : Language} {guess : Exhaustion} {N : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hincrement : ∀ n, N < n →
      (invalidCount L (guess.increment n) : ℝ) ≤
        ε * (guess.increment n).card) :
    ∀ n, N ≤ n →
      (invalidCount L (guess.stage n) : ℝ) ≤
        invalidCount L (guess.stage N) + ε * (guess.stage n).card := by
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero =>
      simp only [Nat.add_zero]
      exact le_add_of_nonneg_right
        (mul_nonneg hε (Nat.cast_nonneg (guess.stage N).card))
  | succ d ih =>
      simp only [Nat.add_succ]
      have hstep := hincrement (N + d + 1) (by omega)
      have hcountReal :
          (invalidCount L (guess.stage (N + d + 1)) : ℝ) =
            invalidCount L (guess.stage (N + d)) +
              invalidCount L (guess.increment (N + d + 1)) := by
        exact_mod_cast invalidCount_stage_succ L guess (N + d)
      have hcardReal :
          ((guess.stage (N + d + 1)).card : ℝ) =
            (guess.stage (N + d)).card +
              (guess.increment (N + d + 1)).card := by
        exact_mod_cast card_stage_succ guess (N + d)
      rw [hcountReal, hcardReal]
      calc
        (invalidCount L (guess.stage (N + d)) : ℝ) +
              invalidCount L (guess.increment (N + d + 1)) ≤
            (invalidCount L (guess.stage N) +
                ε * (guess.stage (N + d)).card) +
              ε * (guess.increment (N + d + 1)).card :=
          add_le_add (ih (by omega)) hstep
        _ = invalidCount L (guess.stage N) +
              ε * ((guess.stage (N + d)).card +
                (guess.increment (N + d + 1)).card) := by ring

/-- Vanishing rejected fractions in the successive increments give a
vanishing cumulative rejected fraction, provided the exhaustion has
infinitely many distinct outputs. -/
theorem invalidFraction_stage_tendsto_zero_of_increment_tendsto_zero
    {L : Language} {guess : Exhaustion}
    (hinfinite : guess.limit.Infinite)
    (hincrement :
      Tendsto (fun n => invalidFraction L (guess.increment n))
        atTop (nhds 0)) :
    Tendsto (fun n => invalidFraction L (guess.stage n))
      atTop (nhds 0) := by
  have hcardNat :
      Tendsto (fun n => (guess.stage n).card) atTop atTop :=
    guess.card_tendsto_atTop_of_limit_infinite hinfinite
  have hcardReal :
      Tendsto (fun n => ((guess.stage n).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcardNat
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n =>
      ha.trans_le (invalidFraction_nonneg L (guess.stage n))
  · intro b hb
    let ε : ℝ := b / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hlateFraction :
        ∀ᶠ n : ℕ in atTop,
          invalidFraction L (guess.increment n) < ε :=
      (tendsto_order.1 hincrement).2 ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 hlateFraction
    let C := invalidCount L (guess.stage N)
    have hprefixRatio :
        Tendsto (fun n => (C : ℝ) / ((guess.stage n).card : ℝ))
          atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hcardReal
    have hprefixSmall :
        ∀ᶠ n : ℕ in atTop,
          (C : ℝ) / ((guess.stage n).card : ℝ) < ε :=
      (tendsto_order.1 hprefixRatio).2 ε hε
    have hpositive :
        ∀ᶠ n : ℕ in atTop, (guess.stage n).card ≠ 0 := by
      filter_upwards [hcardNat.eventually (eventually_ge_atTop 1)]
        with n hn
      omega
    have hstepBound : ∀ k, N < k →
        (invalidCount L (guess.increment k) : ℝ) ≤
          ε * (guess.increment k).card := by
      intro k hk
      have hfrac := hN k (Nat.le_of_lt hk)
      by_cases hzero : (guess.increment k).card = 0
      · have hinvalidZero : invalidCount L (guess.increment k) = 0 :=
          Nat.eq_zero_of_le_zero
            ((invalidCount_le L (guess.increment k)).trans_eq hzero)
        simp [hinvalidZero, hzero]
      · simp only [invalidFraction_eq, hzero, if_false] at hfrac
        have hcardPositive :
            (0 : ℝ) < (guess.increment k).card := by
          exact_mod_cast Nat.pos_of_ne_zero hzero
        exact ((div_lt_iff₀ hcardPositive).mp hfrac).le
    filter_upwards
      [eventually_ge_atTop N, hprefixSmall, hpositive]
      with n hn hprefix hstage
    have htotal := invalidCount_stage_le_prefix_add_rate
      hε.le hstepBound n hn
    have hcardNonzero : ((guess.stage n).card : ℝ) ≠ 0 := by
      exact_mod_cast hstage
    simp only [invalidFraction_eq, hstage, if_false]
    calc
      (invalidCount L (guess.stage n) : ℝ) /
            (guess.stage n).card ≤
          ((C : ℝ) + ε * (guess.stage n).card) /
            (guess.stage n).card :=
        div_le_div_of_nonneg_right (by simpa [C] using htotal)
          (Nat.cast_nonneg _)
      _ = (C : ℝ) / (guess.stage n).card + ε := by
        rw [add_div, mul_div_cancel_right₀ ε hcardNonzero]
      _ < ε + ε := add_lt_add_right hprefix ε
      _ = b := by
        dsimp [ε]
        ring

/-- Repaired form of Appendix Lemma D.1.  The printed proof uses that the
generated language is infinite, so Lean exposes that premise explicitly.
Under it, lower tail precision one implies lower membership precision one. -/
theorem appendix_lemma_D_1_of_limit_infinite
    {L : Language} {guess : Exhaustion}
    (hinfinite : guess.limit.Infinite)
    (htail : lowerTailPrecision L guess = 1) :
    lowerMembershipPrecision L guess = 1 := by
  have htailTendsto :
      Tendsto (stepTailPrecision L guess) atTop (nhds 1) := by
    apply tendsto_of_le_liminf_of_limsup_le
    · simpa [lowerTailPrecision] using htail.symm.le
    · apply limsup_le_of_le
      · exact isCoboundedUnder_le_of_le atTop
          (fun n => stepTailPrecision_nonneg L guess n)
      · exact Eventually.of_forall
          (fun n => stepTailPrecision_le_one L guess n)
    · exact isBoundedUnder_of
        ⟨1, fun n => stepTailPrecision_le_one L guess n⟩
    · exact isBoundedUnder_of
        ⟨0, fun n => stepTailPrecision_nonneg L guess n⟩
  have hincrementErrors :
      Tendsto (fun n => invalidFraction L (guess.increment n))
        atTop (nhds 0) := by
    have hcomplement :
        (fun n => invalidFraction L (guess.increment n)) =
          fun n => 1 - stepTailPrecision L guess n := by
      funext n
      rw [stepTailPrecision_eq_one_sub_invalidFraction]
      ring
    rw [hcomplement]
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
          htailTendsto
  apply lowerMembershipPrecision_eq_one_of_invalidFraction_tendsto_zero
  · filter_upwards
      [(guess.card_tendsto_atTop_of_limit_infinite hinfinite).eventually
        (eventually_ge_atTop 1)] with n hn
    omega
  · exact invalidFraction_stage_tendsto_zero_of_increment_tendsto_zero
      hinfinite hincrementErrors

theorem lowerTailPrecision_eq_one_of_finiteTime
    {L : Language} {guess : Exhaustion}
    (h : TailPrecisionOneFromFiniteTime L guess) :
    lowerTailPrecision L guess = 1 := by
  obtain ⟨N, hN⟩ := h
  have heq :
      (fun n => stepTailPrecision L guess n) =ᶠ[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    (eventually_atTop.2 ⟨N, hN⟩)
  have htendsto :
      Tendsto (stepTailPrecision L guess) atTop (nhds 1) :=
    tendsto_const_nhds.congr' heq.symm
  exact htendsto.liminf_eq

/-- Proposition 3.3 also implies the numerical lower-tail-precision
conclusion stated by the paper. -/
theorem eventuallyValid_implies_lowerTailPrecision_one
    {L : Language} {guess : Exhaustion}
    (h : EventuallyValid L guess) :
    lowerTailPrecision L guess = 1 :=
  lowerTailPrecision_eq_one_of_finiteTime
    ((proposition_3_3 L guess).mp h)

/-- The finite-time attainment notion in Proposition 2.4's footnote. -/
def LowerTailPrecisionAttained
    (L : Language) (guess : Exhaustion) : Prop :=
  ∃ N,
    stepTailPrecision L guess N = lowerTailPrecision L guess ∧
    ∀ n, N ≤ n →
      lowerTailPrecision L guess ≤ stepTailPrecision L guess n

theorem stepTailPrecision_zero_or_one_of_singleStep
    {L : Language} {guess : Exhaustion}
    (hsingle : guess.IsSingleStep) (n : ℕ) :
    stepTailPrecision L guess (n + 1) = 0 ∨
      stepTailPrecision L guess (n + 1) = 1 := by
  have hcard : (guess.increment (n + 1)).card ≤ 1 := by
    simpa [Exhaustion.IsSingleStep, Exhaustion.BoundedBy] using hsingle n
  by_cases hzero : (guess.increment (n + 1)).card = 0
  · exact Or.inr (by simp [stepTailPrecision, hzero])
  · have hone : (guess.increment (n + 1)).card = 1 := by omega
    have hcount := countIn_le L (guess.increment (n + 1))
    have hcountCases :
        countIn L (guess.increment (n + 1)) = 0 ∨
          countIn L (guess.increment (n + 1)) = 1 := by
      omega
    rcases hcountCases with hcountZero | hcountOne
    · exact Or.inl (by simp [stepTailPrecision, hzero, hcountZero])
    · exact Or.inr (by simp [stepTailPrecision, hcountOne, hone])

/-- Proposition 2.4, single-step clause.  Lower tail precision is binary and
its value is attained after a finite round in the precise footnote sense. -/
theorem proposition_2_4_singleStep
    {L : Language} {guess : Exhaustion}
    (hsingle : guess.IsSingleStep) :
    (lowerTailPrecision L guess = 0 ∨
      lowerTailPrecision L guess = 1) ∧
      LowerTailPrecisionAttained L guess := by
  classical
  let p : ℕ → ℝ := stepTailPrecision L guess
  have hzeroRound : p 0 = 1 := by
    simp [p, stepTailPrecision]
  have hdichotomy : ∀ n, p n = 0 ∨ p n = 1 := by
    intro n
    cases n with
    | zero => exact Or.inr hzeroRound
    | succ n =>
        simpa [p] using
          stepTailPrecision_zero_or_one_of_singleStep
            (L := L) hsingle n
  by_cases heventual : ∀ᶠ n : ℕ in atTop, p n = 1
  · have heq : p =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ)) := heventual
    have htendsto : Tendsto p atTop (nhds 1) :=
      tendsto_const_nhds.congr' heq.symm
    have hlim : lowerTailPrecision L guess = 1 := by
      exact htendsto.liminf_eq
    refine ⟨Or.inr hlim, ?_⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 heventual
    refine ⟨N, ?_, ?_⟩
    · exact (hN N le_rfl).trans hlim.symm
    · intro n hn
      rw [hlim]
      change (1 : ℝ) ≤ p n
      rw [hN n hn]
  · have hfrequentNot : ∃ᶠ n : ℕ in atTop, p n ≠ 1 :=
      by simpa [Filter.Frequently] using heventual
    have hfrequentZero : ∃ᶠ n : ℕ in atTop, p n = 0 :=
      hfrequentNot.mono fun n hn =>
        (hdichotomy n).resolve_right hn
    have hle : lowerTailPrecision L guess ≤ 0 := by
      unfold lowerTailPrecision
      apply liminf_le_of_frequently_le
      · exact hfrequentZero.mono fun n hn => hn.le
      · exact isBoundedUnder_of
          ⟨0, fun n => stepTailPrecision_nonneg L guess n⟩
    have hlim : lowerTailPrecision L guess = 0 :=
      le_antisymm hle (lowerTailPrecision_nonneg L guess)
    refine ⟨Or.inl hlim, ?_⟩
    obtain ⟨N, hN⟩ := hfrequentZero.exists
    refine ⟨N, ?_, ?_⟩
    · exact hN.trans hlim.symm
    · intro n _hn
      rw [hlim]
      exact stepTailPrecision_nonneg L guess n

/-! ## The general constant-batch clause of Proposition 2.4 -/

/-- The finite set containing every possible tail-precision value of a
`c`-step exhaustion. -/
noncomputable def boundedTailValues (c : ℕ) : Finset ℝ := by
  classical
  exact insert 1 <|
    (Finset.range (c + 1)).biUnion fun j =>
      (Finset.range (j + 1)).image fun i : ℕ => (i : ℝ) / (j : ℝ)

theorem stepTailPrecision_mem_boundedTailValues
    {L : Language} {guess : Exhaustion} {c : ℕ}
    (hbounded : guess.BoundedBy fun _ => c) (n : ℕ) :
    stepTailPrecision L guess n ∈ boundedTailValues c := by
  classical
  cases n with
  | zero => simp [boundedTailValues, stepTailPrecision]
  | succ n =>
      have hcard : (guess.increment (n + 1)).card ≤ c := by
        simpa [Exhaustion.BoundedBy] using hbounded n
      by_cases hzero : (guess.increment (n + 1)).card = 0
      · simp [boundedTailValues, stepTailPrecision, hzero]
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_biUnion.mpr
        refine ⟨(guess.increment (n + 1)).card, ?_, ?_⟩
        · exact Finset.mem_range.mpr (by omega)
        · apply Finset.mem_image.mpr
          refine ⟨countIn L (guess.increment (n + 1)), ?_, ?_⟩
          · exact Finset.mem_range.mpr (by
              have := countIn_le L (guess.increment (n + 1))
              omega)
          · simp [stepTailPrecision, hzero]

/-- A bounded real sequence taking values in a finite set has its `liminf`
as an eventually minimal value occurring at an actual finite index. -/
theorem liminf_attained_of_mem_finset
    (S : Finset ℝ) (p : ℕ → ℝ)
    (hp : ∀ n, p n ∈ S)
    (hlower : ∀ n, 0 ≤ p n)
    (hupper : ∀ n, p n ≤ 1) :
    ∃ N,
      p N = liminf p atTop ∧
      ∀ n, N ≤ n → liminf p atTop ≤ p n := by
  classical
  let T := S.filter fun x => ∃ᶠ n : ℕ in atTop, p n = x
  have hTnonempty : T.Nonempty := by
    by_contra hTempty
    have hTzero : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTempty
    have havoidEach :
        ∀ x ∈ S, ∀ᶠ n : ℕ in atTop, p n ≠ x := by
      intro x hx
      have hxnot : ¬∃ᶠ n : ℕ in atTop, p n = x := by
        intro hxfreq
        have : x ∈ T := Finset.mem_filter.mpr ⟨hx, hxfreq⟩
        simp [hTzero] at this
      simpa [Filter.Frequently] using hxnot
    have havoidAll :
        ∀ᶠ n : ℕ in atTop, ∀ x ∈ S, p n ≠ x :=
      (S.eventually_all).2 havoidEach
    obtain ⟨n, hn⟩ := havoidAll.exists
    exact hn (p n) (hp n) rfl
  let a := T.min' hTnonempty
  have haMem : a ∈ T := T.min'_mem hTnonempty
  have haFrequently : ∃ᶠ n : ℕ in atTop, p n = a :=
    (Finset.mem_filter.mp haMem).2
  let B := S.filter fun x => x < a
  have havoidBelowEach :
      ∀ x ∈ B, ∀ᶠ n : ℕ in atTop, p n ≠ x := by
    intro x hxB
    have hxS : x ∈ S := (Finset.mem_filter.mp hxB).1
    have hxa : x < a := (Finset.mem_filter.mp hxB).2
    have hxnot : ¬∃ᶠ n : ℕ in atTop, p n = x := by
      intro hxfreq
      have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hxS, hxfreq⟩
      exact (T.min'_le x hxT).not_gt hxa
    simpa [Filter.Frequently] using hxnot
  have havoidBelow :
      ∀ᶠ n : ℕ in atTop, ∀ x ∈ B, p n ≠ x :=
    (B.eventually_all).2 havoidBelowEach
  have heventLower : ∀ᶠ n : ℕ in atTop, a ≤ p n := by
    filter_upwards [havoidBelow] with n hn
    by_contra hnot
    have hlt : p n < a := lt_of_not_ge hnot
    exact hn (p n) (Finset.mem_filter.mpr ⟨hp n, hlt⟩) rfl
  have hleLiminf : a ≤ liminf p atTop := by
    apply le_liminf_of_le
    · exact isCoboundedUnder_ge_of_le atTop hupper
    · exact heventLower
  have hliminfLe : liminf p atTop ≤ a := by
    apply liminf_le_of_frequently_le
    · exact haFrequently.mono fun n hn => hn.le
    · exact isBoundedUnder_of ⟨0, hlower⟩
  have hliminf : liminf p atTop = a := le_antisymm hliminfLe hleLiminf
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 heventLower
  obtain ⟨N, hNge, hNa⟩ :=
    ((eventually_ge_atTop N₀).and_frequently haFrequently).exists
  refine ⟨N, ?_, ?_⟩
  · exact hNa.trans hliminf.symm
  · intro n hn
    rw [hliminf]
    exact hN₀ n (hNge.trans hn)

/-- Proposition 2.4, constant-batch clause: for every `c`-step exhaustion,
lower tail precision is attained after finitely many steps in the paper's
footnote sense. -/
theorem proposition_2_4_constantStep
    {L : Language} {guess : Exhaustion} {c : ℕ}
    (hbounded : guess.BoundedBy fun _ => c) :
    LowerTailPrecisionAttained L guess := by
  let p : ℕ → ℝ := stepTailPrecision L guess
  obtain ⟨N, hvalue, hlower⟩ :=
    liminf_attained_of_mem_finset (boundedTailValues c) p
      (fun n => stepTailPrecision_mem_boundedTailValues hbounded n)
      (fun n => stepTailPrecision_nonneg L guess n)
      (fun n => stepTailPrecision_le_one L guess n)
  exact ⟨N, hvalue, hlower⟩

end GenLimit.InfinitelyManyHallucinations
