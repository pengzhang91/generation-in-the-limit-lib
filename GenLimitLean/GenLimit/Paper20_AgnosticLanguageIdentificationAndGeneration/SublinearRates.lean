import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.IdentificationUpper

/-! # Choosing a window for the introduction's sublinear exponents

One window works for every positive distribution-dependent exponent in
Theorems 2.1 and 2.4. It depends only on the requested rate. -/
namespace GenLimit.AgnosticLanguage
open Filter Asymptotics
open scoped Classical Topology
noncomputable section

theorem sublinear_window (g : ℕ → ℝ) (hg : g =o[atTop] (fun n : ℕ ↦ (n:ℝ))) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧ ∀ d > (0:ℝ), ∀ᶠ n : ℕ in atTop,
      (f n:ℝ)*Real.exp (-d*n/(f n)^2) ≤ Real.exp (-g n) := by
  let P := fun (n m : ℕ) ↦ m^5 ≤ n ∧ g n * (m:ℝ)^4 ≤ n
  let f := fun n ↦ Nat.findGreatest (P n) n
  have eventual (m : ℕ) : ∀ᶠ n : ℕ in atTop, P n m := by
    have hc : 0 < (1:ℝ)/((m:ℝ)^4+1) := by positivity
    filter_upwards [eventually_ge_atTop (m^5), hg.def hc] with n hn h
    refine ⟨hn,?_⟩
    simp only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)] at h
    have hn' : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hh : |g n| *((m:ℝ)^4+1) ≤ n := by
      apply (le_div_iff₀ (by positivity)).mp
      simpa [div_eq_mul_inv,mul_comm] using h
    have hm := mul_le_mul_of_nonneg_right (le_abs_self (g n)) (show 0 ≤ (m:ℝ)^4 by positivity)
    nlinarith [abs_nonneg (g n)]
  have hf : Tendsto f atTop atTop := by
    apply tendsto_atTop.mpr
    intro m
    filter_upwards [eventually_ge_atTop m,eventual m] with n hn hp using Nat.le_findGreatest hn hp
  refine ⟨f,hf,?_⟩
  intro d hd
  obtain ⟨K,hK⟩ := exists_nat_ge (2/d)
  filter_upwards [hf.eventually (eventually_ge_atTop (max K 1))] with n hn
  have hP : P n (f n) :=
    Nat.findGreatest_spec (P := P n) (Nat.zero_le n) (show P n 0 by simp [P])
  have hf₁ : (1:ℝ) ≤ f n := by exact_mod_cast (le_max_right K 1).trans hn
  have hk : (K:ℝ) ≤ f n := by exact_mod_cast (le_max_left K 1).trans hn
  have hp : 0 < (f n:ℝ)^2 := by positivity
  have hf₂ : 2 ≤ d*(f n:ℝ)^2 := by
    have hle := (div_le_iff₀ hd).mp (hK.trans hk)
    have hsq : (f n:ℝ) ≤ (f n:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hf₁) (Nat.cast_nonneg (f n))]
    nlinarith [mul_le_mul_of_nonneg_left hsq hd.le]
  have hf₅ : (f n:ℝ)^5 ≤ n := by exact_mod_cast hP.1
  have htotal : (g n+(f n:ℝ))*(f n:ℝ)^4 ≤ 2*n := by nlinarith [hP.2]
  have hscaled : (g n+(f n:ℝ))*(f n:ℝ)^2 ≤ d*n := by
    apply (le_of_mul_le_mul_right _ hp)
    have hh := mul_le_mul_of_nonneg_right hf₂ (Nat.cast_nonneg n)
    nlinarith only [htotal,hh]
  calc
    _ ≤ Real.exp (f n) * Real.exp (-d*n/(f n)^2) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (f n)]) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [←Real.exp_add,Real.exp_le_exp]
      have h := (le_div_iff₀ hp).mpr hscaled
      linarith [show -d*(n:ℝ)/(f n)^2 = -(d*n/(f n)^2) by ring]

/-- One choice of window gives both sublinear-exponent upper bounds from
informal Theorems 1.1 and 1.3, uniformly in the family and distribution. -/
theorem identification_sublinear_exponents (g : ℕ → ℝ) (hg : g =o[atTop] (fun n : ℕ ↦ (n:ℝ))) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧ ∀ {α : Type} [Countable α] (C : Generic.LanguageFamily α) (p : PMF α),
      ((∃ i, Optimal C p i) → ∀ᶠ n in atTop, idErr C (deterministic (algorithmOne C f)) p n ≤ 2*Real.exp (-g n)) ∧
      (HasSupportedTellTale C p → ∃ c > (0:ℝ), ∀ᶠ n in atTop,
        idP C (deterministic (algorithmTwo C f)) p n ≤ c*Real.exp (-g n)) := by
  obtain ⟨f,hf,hr⟩ := sublinear_window g hg
  refine ⟨f,hf,?_⟩
  intro α _ C p
  constructor
  · intro ho
    filter_upwards [weak_near_exponential C f hf p ho,hr (1/2) (by norm_num)] with n hn h
    apply hn.2.trans
    rw [show -(n:ℝ)/(2*(f n:ℝ)^2) = -(1/2:ℝ)*n/(f n:ℝ)^2 by ring,mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  · intro ht
    obtain ⟨c,hc,d,hd,hbound⟩ := minimal_near_exponential C f hf p ht
    refine ⟨c,hc,?_⟩
    filter_upwards [hbound,hr d hd] with n hn h
    exact hn.trans ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left h hc.le))

end
end GenLimit.AgnosticLanguage
