import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleColoring

/-! Uniform additive logarithmic discrepancy for arbitrary point sets.
This is the static estimate needed in the filtered generation problem:
its constants depend on dimension and tolerance and are uniform over
positions, aspect ratios and point sets. -/
namespace GenLimit.KleinbergWei.Banach
open TierGeometry TierWeights Real Finset
open scoped Classical
noncomputable section

private theorem card_le_span {d} (P : Set (Lattice d)) (l u : Lattice d) :
    (Rectangles.box P l u).card ≤ (span l u)^d := by
  apply (Finset.card_filter_le ..).trans
  rw [Pi.card_Icc]
  calc
    _ ≤ ∏ _ : Fin d, span l u := by
      apply Finset.prod_le_prod' (fun i _ => ?_)
      rw [Int.card_Icc]
      have h := Finset.le_sup (f := fun i => (u i-l i).toNat) (Finset.mem_univ i)
      dsimp only at h; unfold span; omega
    _ = _ := by simp

private theorem tier_log_bound {B : ℝ} (b k : ℕ) (hb : 0 < b) (hk : 0 < k) (hB : 0 < B) :
    (tier (B*b) k hk : ℝ)*log 2 ≤ |log (2*B)| + log b := by
  let j := tier (B*b) k hk
  have bp : (0:ℝ) < b := by exact_mod_cast hb
  have logb : 0 ≤ log b := log_nonneg (by exact_mod_cast hb)
  by_cases z : j=0
  · change (j:ℝ)*_ ≤ _; rw [z]; simp only [Nat.cast_zero,zero_mul]; positivity
  obtain ⟨i,eq⟩ := Nat.exists_eq_succ_of_ne_zero z
  have less : (k:ℝ)*2^i < B*b := lt_of_not_ge fun ge =>
    (show i < j by omega).not_ge (tier_minimal _ k hk ge)
  have k1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have ble : (2:ℝ)^i < B*b := (le_mul_of_one_le_left (by positivity) k1).trans_lt less
  have bound : (2:ℝ)^j ≤ 2*B*b := by rw [eq,pow_succ]; linarith
  have lp := Real.log_le_log (by positivity) bound
  rw [Real.log_pow,Real.log_mul (by positivity) bp.ne'] at lp
  exact lp.trans (add_le_add_right (le_abs_self _) _)

private theorem threshold_linear {δ p : ℝ} (hd : 0 < δ) (hp : 0 ≤ p) (k j : ℕ) (hk : 0 < k) :
    threshold (δ/2) p k j ≤ δ*k +
      ((p+1)*(j*log 2) + (p+2)*log k + 2*log 2)/(δ/2) := by
  let a := sqrt (2*(p+1)*log 2)*sqrt j
  let b := sqrt (2*(p+2)*log k + 4*log 2)
  let t := sqrt k
  have lk : 0 ≤ log k := log_nonneg (by exact_mod_cast hk)
  have aa : a^2 = 2*(p+1)*log 2*j := by
    dsimp [a]; rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
  have bb : b^2 = 2*(p+2)*log k+4*log 2 := Real.sq_sqrt (by positivity)
  have tt : t^2 = k := Real.sq_sqrt (by positivity)
  have th : threshold (δ/2) p k j = δ/2*k+a*t+b*t := by
    unfold threshold a b t; rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ k)]; ring
  rw [th,←sub_le_iff_le_add' ,le_div_iff₀ (by positivity : 0 < δ/2)]
  nlinarith only [sq_nonneg (a-(δ/2)*t),sq_nonneg (b-(δ/2)*t),aa,bb,
    congrArg (fun r : ℝ => (δ/2)^2*r) tt]

/-- One coloring controls all rectangular traces up to a chosen relative
error and an additive term proportional to one plus the logarithm of the
largest lattice-side count. The constant is independent of the point set. -/
theorem filtered_discrepancy {d : ℕ} (hd : 0 < d) (δ : ℝ) (positive : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Set (Lattice d), ∃ c : Lattice d → Bool, ∀ l u,
      let T := Rectangles.box P l u
      |∑ v ∈ T, RandomSigns.sign (c v)| ≤
        δ*T.card+C*(1+log (span l u)) := by
  let ε := δ/2
  let p := scale d 1
  let B := baseline ε 1 d
  let c₁ := (p+1)*|log (2*B)|+2*log 2
  let c₂ := (p+1)+(p+2)*d
  have he : 0 < ε := by dsimp [ε]; positivity
  have hp : 0 ≤ p := by dsimp [p,scale]; positivity
  have hB : 0 < B := by dsimp [B,baseline]; positivity
  have h₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have h₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  refine ⟨(c₁+c₂)/ε,by positivity,fun P => ?_⟩
  obtain ⟨c,good⟩ := rectangle_coloring hd P ε 1 he one_pos
  refine ⟨c,fun l u => ?_⟩
  let T := Rectangles.box P l u
  let b := span l u
  have hb : 0 < b := Nat.succ_pos _
  have logb : 0 ≤ log b := log_nonneg (by exact_mod_cast hb)
  rcases T.eq_empty_or_nonempty with empty | ne
  · change |∑ v ∈ T, _| ≤ δ*T.card+((c₁+c₂)/ε)*(1+log b)
    rw [empty]; simp only [Finset.sum_empty,abs_zero,Finset.card_empty,Nat.cast_zero,mul_zero,zero_add]
    positivity
  let k := T.card
  let j := tier (B*b) k ne.card_pos
  have bound := good l u ne
  simp only [Real.rpow_one] at bound
  change _ ≤ threshold ε p k j at bound
  have lc := log_le_log (show 0 < (k:ℝ) by exact_mod_cast ne.card_pos)
    (show (k:ℝ) ≤ (b:ℝ)^d by exact_mod_cast card_le_span P l u)
  rw [Real.log_pow] at lc
  have lj := tier_log_bound b k hb ne.card_pos hB
  change (j:ℝ)*log 2 ≤ _ at lj
  apply (bound.trans (threshold_linear positive hp k j ne.card_pos)).trans
  apply add_le_add_left
  rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right he]
  have e₁ := mul_le_mul_of_nonneg_left lj (show 0 ≤ p+1 by positivity)
  have e₂ := mul_le_mul_of_nonneg_left lc (show 0 ≤ p+2 by positivity)
  change _ ≤ (c₁+c₂)*(1+log b)
  have extra := mul_nonneg h₁ logb
  dsimp only [c₁,c₂] at *
  nlinarith only [e₁,e₂,extra,h₂]

end
end GenLimit.KleinbergWei.Banach
