import GenLimit.Core.GenericGeneration
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedMaximizer
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.NoisyLogBounds
import GenLimit.Core.Text

/-! # Noisy multiplicative weights for finite and increasing active classes

At each round the learner maximizes weighted membership among fresh points.
A missed target increases its weight, and a demonstration outside the target
decreases its weight. The next demonstration is itself an admissible fresh
choice, giving a non-increasing active potential even under noisy input.
-/
namespace GenLimit.MistakeBounded
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

structure NoisyRule (ι α : Type*) where
  languages : ι → Set α
  active : ℕ → Finset ι
  prior : ι → ℝ
  rate : ℝ

namespace NoisyRule
variable [Infinite α] (R : NoisyRule ι α)

def pick (history : List α) (weight : ι → ℝ) : α := by
  classical
  exact infiniteFreshWeightedMaximizer (R.active history.length) weight R.languages history.toFinset

def factor (i : ι) (prediction demo : α) : ℝ :=
  (if prediction ∈ R.languages i then 1 else 1+R.rate) *
    (if demo ∈ R.languages i then 1 else 1-R.rate)

/-- The history is stored newest first to permit structural recursion. -/
def weights : List α → ι → ℝ
  | [] => R.prior
  | x :: xs => fun i => if i ∈ R.active xs.length then
      weights xs i * R.factor i (R.pick xs (weights xs)) x else weights xs i

def generator : Generic.Generator α := fun _ h =>
  let xs := (List.ofFn h).reverse
  R.pick xs (R.weights xs)

private def past (s : ℕ → α) (t : ℕ) := (textPrefix s t).reverse

omit [Infinite α] in
private theorem past_length (s : ℕ → α) (t : ℕ) : (past s t).length = t := by simp [past]
omit [Infinite α] in
private theorem past_succ (s : ℕ → α) (t : ℕ) : past s (t+1) = s t :: past s t := by
  simp [past,textPrefix_succ]

private theorem output_eq (s : ℕ → α) (t : ℕ) :
    Generic.output R.generator s t = R.pick (past s t) (R.weights (past s t)) := by
  simp [Generic.output,generator,past,textPrefix_eq_ofFn]

theorem fresh (t : ℕ) (h : Fin t → α) (i : Fin t) : R.generator t h ≠ h i := by
  classical
  let xs := (List.ofFn h).reverse
  have away := infiniteFreshWeightedMaximizer_not_mem (R.active xs.length)
    (R.weights xs) R.languages xs.toFinset
  intro eq
  apply away
  change R.pick xs (R.weights xs) = h i at eq
  change R.pick xs (R.weights xs) ∈ xs.toFinset
  rw [eq]
  simp [xs]

omit [Infinite α] in
private theorem factor_nonneg (hg : 0 ≤ R.rate) (hu : R.rate ≤ 1) (i : ι) (x y : α) :
    0 ≤ R.factor i x y := by
  unfold factor
  split_ifs <;> apply mul_nonneg <;> linarith

private theorem weights_nonneg (hp : ∀ i, 0 ≤ R.prior i) (hg : 0 ≤ R.rate)
    (hu : R.rate ≤ 1) (xs : List α) (i : ι) : 0 ≤ R.weights xs i := by
  induction xs with
  | nil => exact hp i
  | cons x xs ih =>
    simp only [weights]
    split_ifs
    · exact mul_nonneg ih (R.factor_nonneg hg hu ..)
    · exact ih

omit [Infinite α] in
private theorem demo_fresh {s : ℕ → α} (hs : Function.Injective s) (t : ℕ) :
    s t ∉ (past s t).toFinset := by
  simp only [past,List.mem_toFinset,List.mem_reverse,textPrefix,List.mem_map,List.mem_range]
  rintro ⟨i,hi,eq⟩
  exact hi.ne (hs eq)

private theorem mass_step (s : ℕ → α) (hs : Function.Injective s)
    (hp : ∀ i, 0 ≤ R.prior i) (hg : 0 ≤ R.rate) (hu : R.rate ≤ 1)
    (t : ℕ) (J : Finset ι) (inside : R.active t ⊆ J) :
    ∑ i ∈ J, R.weights (past s (t+1)) i ≤ ∑ i ∈ J, R.weights (past s t) i := by
  classical
  let w := R.weights (past s t)
  let x := R.pick (past s t) w
  let y := s t
  let A := R.active t
  let mass (z : α) (i : ι) : ℝ := if z ∈ R.languages i then w i else 0
  have best : (∑ i ∈ A, mass y i) ≤ ∑ i ∈ A, mass x i := by
    have b := infiniteFreshWeightedMaximizer_spec (R.active (past s t).length) w R.languages
      (past s t).toFinset y (demo_fresh hs t)
    simpa only [weightedScore,Finset.sum_filter,past_length,A,x,pick,mass] using b
  have point (i : ι) (hi : i ∈ A) :
      R.weights (past s (t+1)) i ≤ w i + R.rate * (mass y i - mass x i) := by
    change i ∈ R.active t at hi
    simp only [past_succ,weights,past_length,if_pos hi]
    change w i * R.factor i x y ≤ _
    unfold factor mass
    have wn := R.weights_nonneg hp hg hu (past s t) i
    change 0 ≤ w i at wn
    split_ifs <;> nlinarith [mul_nonneg wn (sq_nonneg R.rate)]
  have active_le : (∑ i ∈ A, R.weights (past s (t+1)) i) ≤ ∑ i ∈ A, w i := by
    apply (Finset.sum_le_sum point).trans
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib]
    linarith [mul_nonpos_of_nonneg_of_nonpos hg (sub_nonpos.mpr best)]
  rw [← Finset.sum_sdiff inside, ← Finset.sum_sdiff inside (f := fun i => R.weights (past s t) i)]
  apply add_le_add _ active_le
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  simp only [past_succ,weights,past_length,if_neg (Finset.mem_sdiff.mp hi).2]

private theorem mass_bound (s : ℕ → α) (hs : Function.Injective s)
    (hp : ∀ i, 0 ≤ R.prior i) (hg : 0 ≤ R.rate) (hu : R.rate ≤ 1)
    (T : ℕ) (J : Finset ι) (inside : ∀ t < T, R.active t ⊆ J) :
    ∑ i ∈ J, R.weights (past s T) i ≤ ∑ i ∈ J, R.prior i := by
  induction T with
  | zero => exact le_rfl
  | succ t ih =>
    exact (R.mass_step s hs hp hg hu t J (inside t (by omega))).trans
      (ih (fun j hj => inside j (by omega)))

/-- Count mistakes on the active rounds of one expert. -/
def activeMistakes (z : ℕ → α) (i : ι) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, if i ∈ R.active t ∧ z t ∉ R.languages i then 1 else 0

private theorem log_weight (s : ℕ → α) (i : ι) (hp : R.prior i > 0)
    (hg : 0 < R.rate) (hu : R.rate < 1) (T : ℕ) :
    0 < R.weights (past s T) i ∧
    Real.log (R.weights (past s T) i) = Real.log (R.prior i) +
      R.activeMistakes (Generic.output R.generator s) i T * Real.log (1+R.rate) +
      R.activeMistakes s i T * Real.log (1-R.rate) := by
  induction T with
  | zero => simpa [activeMistakes,past,textPrefix,weights] using hp
  | succ t ih =>
    have plus : 0 < 1+R.rate := by linarith
    have minus : 0 < 1-R.rate := by linarith
    simp only [past_succ,weights,past_length,activeMistakes,Finset.sum_range_succ,Nat.cast_add]
    rw [← R.output_eq]
    have wp := ih.1
    by_cases ha : i ∈ R.active t <;> by_cases hx : Generic.output R.generator s t ∈ R.languages i <;>
      by_cases hy : s t ∈ R.languages i <;>
      simp [ha,hx,hy,factor,Real.log_mul,ih.1.ne',plus.ne',minus.ne',ih.2,activeMistakes] <;>
      (try constructor) <;> first | assumption | positivity | ring

theorem active_mistake_bound (s : ℕ → α) (hs : Function.Injective s)
    (hp : ∀ i, 0 ≤ R.prior i) (hg : 0 < R.rate) (hu : R.rate ≤ 3/4)
    (T : ℕ) (J : Finset ι) (inside : ∀ t < T, R.active t ⊆ J)
    (i : ι) (hi : i ∈ J) (pos : 0 < R.prior i) :
    (R.activeMistakes (Generic.output R.generator s) i T : ℝ) ≤
      (1+2*R.rate)*R.activeMistakes s i T +
        Real.logb 2 ((∑ j ∈ J, R.prior j) / R.prior i) / R.rate := by
  classical
  let W := ∑ j ∈ J, R.prior j
  have lw := R.log_weight s i pos hg (by linarith) T
  have wi := R.weights_nonneg hp hg.le (by linarith) (past s T)
  have bound := (Finset.single_le_sum (fun j _ => wi j) hi).trans
    (R.mass_bound s hs hp hg.le (by linarith) T J inside)
  have Wpos : 0 < W := lw.1.trans_le bound
  have logs := Real.log_le_log lw.1 bound
  rw [lw.2] at logs
  change _ ≤ Real.log W at logs
  rw [Real.logb,Real.log_div Wpos.ne' pos.ne']
  have b2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have b1 : 0 < Real.log (1+R.rate) := Real.log_pos (by linarith)
  have ratio : 0 ≤ Real.log W - Real.log (R.prior i) :=
    sub_nonneg.mpr (Real.log_le_log pos (Finset.single_le_sum (fun j _ => hp j) hi))
  have loss := mul_le_mul_of_nonneg_left (noisy_log_loss hg.le hu)
    (Nat.cast_nonneg (R.activeMistakes s i T) (α := ℝ))
  have gain := noisy_log_gain hg.le hu
  apply (mul_le_mul_iff_left₀ b1).mp
  have denom : 0 < Real.log 2 * R.rate := mul_pos b2 hg
  have frac : (Real.log W - Real.log (R.prior i)) ≤
      (Real.log W - Real.log (R.prior i)) / Real.log 2 / R.rate * Real.log (1+R.rate) := by
    rw [div_div,div_mul_eq_mul_div,le_div_iff₀ denom]
    nlinarith [mul_nonneg ratio (sub_nonneg.mpr gain)]
  nlinarith

/-- At a mistake on an active infinite target, some fresh point in that
target has score at least its own weight. The chosen point is outside the
target and has at least that score, so its weight is at most half the mass. -/
theorem miss_log_le_half (s : ℕ → α) (hs : Function.Injective s)
    (hp : ∀ i, 0 ≤ R.prior i) (hg : 0 < R.rate) (hu : R.rate < 1)
    (t : ℕ) (growing : ∀ j < t, R.active j ⊆ R.active t)
    (total : ∑ j ∈ R.active t, R.prior j ≤ 1) (i : ι) (ha : i ∈ R.active t)
    (inf : (R.languages i).Infinite) (pos : 0 < R.prior i)
    (miss : Generic.output R.generator s t ∉ R.languages i) :
    Real.log (R.prior i) + R.activeMistakes (Generic.output R.generator s) i t * Real.log (1+R.rate)
      + R.activeMistakes s i t * Real.log (1-R.rate) ≤ Real.log (1/2) := by
  classical
  let A := R.active t
  let w := R.weights (past s t)
  let x := Generic.output R.generator s t
  have wn (j : ι) : 0 ≤ w j := R.weights_nonneg hp hg.le hu.le _ _
  obtain ⟨v,hv,fresh⟩ := inf.exists_notMem_finset (past s t).toFinset
  have best : weightedScore A w R.languages v ≤ weightedScore A w R.languages x := by
    simpa only [x,output_eq,pick,past_length,A,w] using
      infiniteFreshWeightedMaximizer_spec (R.active (past s t).length) w R.languages
        (past s t).toFinset v fresh
  have lo : w i ≤ weightedScore A w R.languages v := by
    simpa only [weightedScore,if_pos hv] using
      (Finset.single_le_sum (f := fun j => if v ∈ R.languages j then w j else 0)
        (fun j _ => by dsimp; split <;> simp [wn]) ha)
  have comp : w i + weightedScore A w R.languages x ≤ ∑ j ∈ A, w j := by
    unfold weightedScore
    have eq : (∑ j ∈ A, if j = i then w j else 0) = w i := by simp [ha,A]
    rw [← eq,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases e : j = i
    · subst j
      simp [x,miss]
    · simp [e]
      split <;> simp [wn]
  have mass := (R.mass_bound s hs hp hg.le hu.le t _ growing).trans total
  have half : w i ≤ 1/2 := by
    change (∑ j ∈ A, w j) ≤ 1 at mass
    linarith
  have lw := R.log_weight s i pos hg hu t
  exact lw.2 ▸ Real.log_le_log lw.1 half

end NoisyRule
end
end GenLimit.MistakeBounded
