import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite ordered IID samples from a discrete distribution

The sample is a list, retaining multiplicities and order. All events are
measured with the discrete PMF outer measure, so no extra measurability
premise is hidden in the interfaces. This infrastructure is independent of
any language family or learning algorithm.
-/

namespace GenLimit.DiscreteIID

noncomputable section

variable {α : Type*}

/-- The law of an ordered list of `n` independent draws from `p`. -/
def samples (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun x => (samples p n).map (List.cons x)

/-- Real-valued probability of an event under a discrete distribution. -/
def probability (p : PMF α) (E : Set α) : ℝ :=
  (p.toOuterMeasure E).toReal

@[simp] theorem probability_univ (p : PMF α) : probability p Set.univ = 1 := by
  unfold probability
  rw [PMF.toOuterMeasure_apply]
  simp only [Set.indicator_univ, PMF.tsum_coe, ENNReal.toReal_one]

/-- Applying a function to each draw commutes with taking an IID sample. -/
theorem samples_map {β : Type*} (p : PMF α) (f : α → β) (n : ℕ) :
    samples (p.map f) n = (samples p n).map (List.map f) := by
  induction n with
  | zero => simp [samples, PMF.pure_map]
  | succ n ih =>
    simp only [samples, PMF.bind_map, PMF.map_bind, ih, PMF.map_comp]
    congr 1

theorem event_le_one (p : PMF α) (E : Set α) : p.toOuterMeasure E ≤ 1 := by
  calc
    p.toOuterMeasure E ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := by rw [PMF.toOuterMeasure_apply]; simp

theorem event_ne_top (p : PMF α) (E : Set α) : p.toOuterMeasure E ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one p E)

theorem probability_nonneg (p : PMF α) (E : Set α) : 0 ≤ probability p E :=
  ENNReal.toReal_nonneg

theorem probability_le_one (p : PMF α) (E : Set α) : probability p E ≤ 1 := by
  exact (ENNReal.toReal_le_toReal (event_ne_top p E) ENNReal.one_ne_top).mpr
    (event_le_one p E)

theorem probability_mono (p : PMF α) {E F : Set α} (h : E ⊆ F) :
    probability p E ≤ probability p F :=
  ENNReal.toReal_mono (event_ne_top p F) (p.toOuterMeasure.mono h)

theorem probability_union_le (p : PMF α) (E F : Set α) :
    probability p (E ∪ F) ≤ probability p E + probability p F := by
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨event_ne_top p E, event_ne_top p F⟩)
    (MeasureTheory.measure_union_le (μ := p.toOuterMeasure) E F)
  simpa [probability, ENNReal.toReal_add (event_ne_top p E) (event_ne_top p F)] using h

theorem probability_biUnion_le (p : PMF α) {β : Type*} (T : Finset β) (E : β → Set α) :
    probability p (⋃ x ∈ T, E x) ≤ ∑ x ∈ T, probability p (E x) := by
  have hfin : (∑ x ∈ T, p.toOuterMeasure (E x)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr fun x _ => event_ne_top p (E x)
  have h := ENNReal.toReal_mono hfin
    (MeasureTheory.measure_biUnion_finset_le (μ := p.toOuterMeasure) T E)
  simpa [probability, ENNReal.toReal_sum (fun x _ => event_ne_top p (E x))] using h

theorem probability_compl (p : PMF α) (E : Set α) :
    probability p Eᶜ = 1 - probability p E := by
  classical
  have h : p.toOuterMeasure E + p.toOuterMeasure Eᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    convert p.tsum_coe using 1
    apply tsum_congr; intro x; by_cases hx : x ∈ E <;> simp [hx]
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (event_ne_top p E) (event_ne_top p Eᶜ)] at hr
  simp only [ENNReal.toReal_one] at hr
  unfold probability
  linarith

theorem probability_bind_ge (p : PMF α) {β : Type*} (q : α → PMF β)
    (E : Set β) (a : α) :
    (p a).toReal * probability (q a) E ≤ probability (p.bind q) E := by
  unfold probability
  rw [← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono (event_ne_top (p.bind q) E)
  rw [PMF.toOuterMeasure_bind_apply]
  exact ENNReal.le_tsum a

/-- Discrete expectation formula for a randomized kernel's event probability. -/
theorem probability_bind_eq_tsum (p : PMF α) {β : Type*} (q : α → PMF β) (E : Set β) :
    probability (p.bind q) E = ∑' a, (p a).toReal * probability (q a) E := by
  unfold probability
  rw [PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq]
  · simp_rw [ENNReal.toReal_mul]
  · intro a
    exact ENNReal.mul_ne_top (p.apply_ne_top a) (event_ne_top (q a) E)

theorem probability_inter_support (p : PMF α) (E : Set α) :
    probability p (E ∩ p.support) = probability p E := by
  unfold probability
  rw [PMF.toOuterMeasure_apply_inter_support]

theorem samples_support (p : PMF α) (n : ℕ) (xs : List α) :
    xs ∈ (samples p n).support ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ p.support := by
  induction n generalizing xs with
  | zero =>
    simp only [samples, PMF.support_pure, Set.mem_singleton_iff]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, _⟩; exact List.length_eq_zero_iff.mp h
  | succ n ih =>
    cases xs with
    | nil => simp [samples]
    | cons x xs =>
      simp [samples, ih, and_assoc, and_comm]

theorem samples_all (p : PMF α) (S : Set α) (n : ℕ) :
    (samples p n).toOuterMeasure {xs | ∀ x ∈ xs, x ∈ S} = (p.toOuterMeasure S) ^ n := by
  classical
  induction n with
  | zero => simp [samples]
  | succ n ih =>
    rw [samples, PMF.toOuterMeasure_bind_apply]
    have h (x : α) :
        ((samples p n).map (List.cons x)).toOuterMeasure {xs | ∀ y ∈ xs, y ∈ S} =
          if x ∈ S then (p.toOuterMeasure S) ^ n else 0 := by
      rw [PMF.toOuterMeasure_map_apply]
      by_cases hx : x ∈ S
      · simpa [Set.preimage, hx] using ih
      · simp [Set.preimage, hx]
    simp_rw [h]
    calc
      _ = ∑' a, S.indicator p a * (p.toOuterMeasure S) ^ n := by
        apply tsum_congr; intro a; by_cases ha : a ∈ S <;> simp [ha]
      _ = (∑' a, S.indicator p a) * (p.toOuterMeasure S) ^ n := ENNReal.tsum_mul_right
      _ = _ := by rw [← PMF.toOuterMeasure_apply, pow_succ']

theorem samples_replicate (p : PMF α) (x : α) (n : ℕ) :
    samples p n (List.replicate n x) = (p x) ^ n := by
  have heq : {xs : List α | ∀ y ∈ xs, y ∈ ({x} : Set α)} ∩ (samples p n).support =
      {List.replicate n x} ∩ (samples p n).support := by
    ext xs
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, hs⟩
      refine ⟨?_, hs⟩
      have hl := (samples_support p n xs).mp hs
      exact (List.eq_replicate_iff.mpr ⟨hl.1, h⟩)
    · rintro ⟨rfl, hs⟩
      exact ⟨by simp, hs⟩
  have := PMF.toOuterMeasure_apply_eq_of_inter_support_eq (samples p n) heq
  rw [PMF.toOuterMeasure_apply_singleton, samples_all,
    PMF.toOuterMeasure_apply_singleton] at this
  exact this.symm

/-- The probability of never seeing a specified point in `n` IID draws. -/
theorem missing_probability (p : PMF α) (x : α) (n : ℕ) :
    probability (samples p n) {xs | x ∉ xs} = (1 - (p x).toReal) ^ n := by
  classical
  have heq : {xs : List α | x ∉ xs} = {xs | ∀ y ∈ xs, y ∈ ({x} : Set α)ᶜ} := by
    ext xs; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h y hy he; exact h (he ▸ hy)
    · intro h hx; exact h x hx rfl
  unfold probability
  rw [heq, samples_all, ENNReal.toReal_pow]
  change (probability p ({x} : Set α)ᶜ) ^ n = _
  rw [probability_compl]
  simp [probability, PMF.toOuterMeasure_apply_singleton]

/-- Union-bound form, retaining the individual atom masses. -/
theorem finite_missing_bound [DecidableEq α] (p : PMF α) (T : Finset α) (n : ℕ) :
    probability (samples p n) {xs | ¬∀ x ∈ T, x ∈ xs} ≤
      ∑ x ∈ T, (1 - (p x).toReal) ^ n := by
  have heq : {xs : List α | ¬∀ x ∈ T, x ∈ xs} = ⋃ x ∈ T, {xs | x ∉ xs} := by
    ext xs; simp
  rw [heq]
  simpa [missing_probability] using probability_biUnion_le (samples p n) T (fun x => {xs | x ∉ xs})

/-- A finite set of positive-mass atoms has a positive uniform mass bound. -/
theorem finite_mass_lower_bound (p : PMF α) (T : Finset α)
    (hT : ∀ x ∈ T, p x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T, c ≤ (p x).toReal := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a T ha ih =>
    obtain ⟨c, hc, hcm⟩ := ih (fun x hx => hT x (Finset.mem_insert_of_mem hx))
    have hap : 0 < (p a).toReal := ENNReal.toReal_pos (hT a (by simp)) (p.apply_ne_top a)
    refine ⟨min c (p a).toReal, lt_min hc hap, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcm x hx)

/-- Every finite set of positive-mass atoms is covered at an exponential rate. -/
theorem finite_missing_exponential [DecidableEq α] (p : PMF α) (T : Finset α)
    (hT : ∀ x ∈ T, p x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      probability (samples p n) {xs | ¬∀ x ∈ T, x ∈ xs} ≤
        (T.card : ℝ) * Real.exp (-c * n) := by
  obtain ⟨c, hc, hm⟩ := finite_mass_lower_bound p T hT
  refine ⟨c, hc, fun n => (finite_missing_bound p T n).trans ?_⟩
  calc
    _ ≤ ∑ _x ∈ T, Real.exp (-c * (n : ℝ)) := by
      apply Finset.sum_le_sum; intro x hx
      have hp : (p x).toReal ≤ 1 := by
        simpa [probability, PMF.toOuterMeasure_apply_singleton] using probability_le_one p {x}
      have hbase : 1 - (p x).toReal ≤ Real.exp (-c) := by
        have := Real.add_one_le_exp (-c)
        linarith [hm x hx]
      calc
        _ ≤ Real.exp (-c) ^ n := pow_le_pow_left₀ (by linarith) hbase n
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ = _ := by simp

end
end GenLimit.DiscreteIID
