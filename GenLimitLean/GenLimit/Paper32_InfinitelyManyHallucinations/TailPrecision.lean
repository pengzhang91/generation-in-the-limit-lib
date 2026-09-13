import GenLimit.Paper32_InfinitelyManyHallucinations.Definitions
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
