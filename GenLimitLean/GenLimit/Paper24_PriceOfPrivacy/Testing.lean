import GenLimit.Support.DiscreteIID

/-! Private two-point testing for randomized estimators on ordered samples.
All probabilities are evaluated in the discrete PMF model of P20.
An infinite privacy budget imposes no restriction. -/

namespace GenLimit.PriceOfPrivacy

open DiscreteIID
open scoped ENNReal Classical
noncomputable section

/-- Pure replacement privacy on equal-length ordered samples. -/
def IsPrivate (ε : ℝ≥0∞) (A : List X → PMF Y) : Prop :=
  ε ≠ ⊤ → ∀ (pre : List X) (x y : X) (post : List X) (F : Set Y),
    (A (pre ++ x :: post)).toOuterMeasure F ≤
      ENNReal.ofReal (Real.exp ε.toReal) * (A (pre ++ y :: post)).toOuterMeasure F

/-- The probability factor retained for one replacement, including ε = ∞. -/
def retention (ε : ℝ≥0∞) : ℝ := if ε = ⊤ then 0 else Real.exp (-ε.toReal)

theorem retention_mem (ε : ℝ≥0∞) : retention ε ∈ Set.Icc 0 1 := by
  unfold retention
  split
  · exact ⟨le_rfl,zero_le_one⟩
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg)⟩

private theorem retain_one {A : List X → PMF Y} {ε} (dp : IsPrivate ε A)
    (pre : List X) (x y : X) (post : List X) (F : Set Y) :
    ENNReal.ofReal (retention ε) * (A (pre ++ x :: post)).toOuterMeasure F ≤
      (A (pre ++ y :: post)).toOuterMeasure F := by
  by_cases top : ε = ⊤
  · simp [retention,top]
  · have h := mul_le_mul_left' (dp top pre x y post F) (ENNReal.ofReal (retention ε))
    rw [←mul_assoc,retention,if_neg top,← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ←Real.exp_add,neg_add_cancel,Real.exp_zero,ENNReal.ofReal_one,one_mul] at h
    simpa only [retention,if_neg top] using h

/-- Nonnegative expectation. Its finite products may be integrated without
any exchange of conditionally convergent sums. -/
def moment (q : PMF X) (f : X → ℝ≥0∞) : ℝ≥0∞ := ∑' x, q x * f x

theorem moment_pure (x : X) (f : X → ℝ≥0∞) : moment (PMF.pure x) f = f x := by
  classical
  unfold moment
  rw [tsum_eq_single x (fun z hz => by simp [PMF.pure_apply,hz])]
  simp

theorem moment_bind (p : PMF X) (q : X → PMF Y) (f : Y → ℝ≥0∞) :
    moment (p.bind q) f = moment p (fun x => moment (q x) f) := by
  unfold moment
  simp only [PMF.bind_apply,← ENNReal.tsum_mul_right,mul_assoc,← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

theorem moment_map (p : PMF X) (g : X → Y) (f : Y → ℝ≥0∞) :
    moment (p.map g) f = moment p (fun x => f (g x)) := by
  change moment (p.bind (fun x => PMF.pure (g x))) f = _
  simp only [moment_bind,moment_pure]

def productWeight (w : X → ℝ≥0∞) (xs : List X) := (xs.map w).prod

theorem product_moment (p : PMF X) (w : X → ℝ≥0∞) (n : ℕ) :
    moment (samples p n) (productWeight w) = moment p w ^ n := by
  induction n with
  | zero => simp [samples,moment_pure,productWeight]
  | succ n ih =>
    rw [samples,moment_bind]
    simp_rw [moment_map]
    have split (x : X) : moment (samples p n) (fun ys => productWeight w (x::ys)) =
        w x * moment (samples p n) (productWeight w) := by
      unfold moment
      simp only [productWeight,List.map_cons,List.prod_cons,←ENNReal.tsum_mul_left]
      exact tsum_congr fun _ => mul_left_comm ..
    simp_rw [split,ih]
    rw [pow_succ',moment]
    simp_rw [←mul_assoc]
    rw [ENNReal.tsum_mul_right]
    rfl

/-- A latent label outside D gives exactly the same observation to both
experiments. Inside D one replacement costs at most exp(ε). -/
def coordinateWeight (ε : ℝ≥0∞) (D : Set Z) (z : Z) : ℝ≥0∞ :=
  if z ∈ D then ENNReal.ofReal (retention ε) else 1

private theorem weight_le_one (ε) (D : Set Z) (zs : List Z) :
    productWeight (coordinateWeight ε D) zs ≤ 1 := by
  induction zs with
  | nil => simp [productWeight]
  | cons z zs ih =>
    have hw : coordinateWeight ε D z ≤ 1 := by
      unfold coordinateWeight
      split
      · exact_mod_cast ENNReal.ofReal_le_ofReal (retention_mem ε).2
      · exact le_rfl
    exact (mul_le_mul' hw ih).trans_eq (one_mul 1)

private theorem retain_prefix {A : List X → PMF Y} {ε} (dp : IsPrivate ε A)
    (f g : Z → X) (D : Set Z) (agree : ∀ z ∉ D, f z = g z)
    (F : Set Y) (zs : List Z) (pre : List X) :
    productWeight (coordinateWeight ε D) zs * (A (pre ++ zs.map f)).toOuterMeasure F ≤
      (A (pre ++ zs.map g)).toOuterMeasure F := by
  induction zs generalizing pre with
  | nil => simp [productWeight]
  | cons z zs ih =>
    have head : coordinateWeight ε D z * (A (pre ++ f z :: zs.map f)).toOuterMeasure F ≤
        (A (pre ++ g z :: zs.map f)).toOuterMeasure F := by
      by_cases hz : z ∈ D
      · simpa [coordinateWeight,hz] using retain_one dp pre (f z) (g z) (zs.map f) F
      · simp [coordinateWeight,hz,agree z hz]
    have tail := ih (pre ++ [g z])
    simp only [List.append_assoc,List.singleton_append] at tail
    change (coordinateWeight ε D z * productWeight (coordinateWeight ε D) zs) * _ ≤ _
    rw [mul_comm (coordinateWeight ε D z),mul_assoc]
    exact (mul_le_mul_left' head _).trans tail

private theorem mass_compl_add (p : PMF Y) (F : Set Y) :
    p.toOuterMeasure Fᶜ + p.toOuterMeasure F = 1 := by
  classical
  rw [PMF.toOuterMeasure_apply,PMF.toOuterMeasure_apply,←ENNReal.tsum_add,←p.tsum_coe]
  exact tsum_congr fun y => by by_cases h : y ∈ F <;> simp [h]

/-- The IID form of Lemma 2.3. A common latent draw gives arbitrary coupled
observations f(z), g(z). The same event is tested on the two randomized outputs. -/
theorem private_two_point {A : List X → PMF Y} {ε} (dp : IsPrivate ε A)
    (p : PMF Z) (f g : Z → X) (D : Set Z) (agree : ∀ z ∉ D, f z = g z)
    (F : Set Y) (n : ℕ) :
    (moment p (coordinateWeight ε D)).toReal ^ n ≤
      probability ((samples (p.map f) n).bind A) Fᶜ +
      probability ((samples (p.map g) n).bind A) F := by
  have point (zs : List Z) :
      productWeight (coordinateWeight ε D) zs ≤ (A (zs.map f)).toOuterMeasure Fᶜ +
        (A (zs.map g)).toOuterMeasure F := by
    have right := retain_prefix dp f g D agree F zs []
    simp only [List.nil_append] at right
    let w := productWeight (coordinateWeight ε D) zs
    have left := mul_le_mul_right' (weight_le_one ε D zs) ((A (zs.map f)).toOuterMeasure Fᶜ)
    rw [one_mul] at left
    have add := add_le_add left right
    rwa [←mul_add,mass_compl_add,mul_one] at add
  let q := samples p n
  have lower := ENNReal.tsum_le_tsum (fun zs => mul_le_mul_left' (point zs) (q zs))
  change moment q (productWeight (coordinateWeight ε D)) ≤ _ at lower
  rw [product_moment] at lower
  simp_rw [mul_add] at lower
  rw [ENNReal.tsum_add] at lower
  simp only [samples_map,PMF.bind_map]
  unfold probability
  have h₀ := event_ne_top (q.bind (A ∘ List.map f)) Fᶜ
  have h₁ := event_ne_top (q.bind (A ∘ List.map g)) F
  rw [← ENNReal.toReal_add h₀ h₁,← ENNReal.toReal_pow]
  apply ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h₀,h₁⟩)
  simpa only [PMF.toOuterMeasure_bind_apply] using lower

end
end GenLimit.PriceOfPrivacy
