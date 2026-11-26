import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LogPowerCriterion
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.MovingCubes

/-! Equation (19) of P23. The dilation parameter is real and the translation
is an integer vector. The lower limit requires both the dilation and the
target count divided by the square of its logarithm to tend to infinity. -/
namespace GenLimit.KleinbergWei.Banach.FixedShape
open Finset Real Filter
open scoped Classical ENNReal
noncomputable section

abbrev Box (d : ℕ) := Lattice d × Lattice d

/-- Closed lattice points in the real dilate translated by z. -/
def dilate {d} (R : Box d) (z : Lattice d) (r : ℝ) : Box d :=
  (fun i => z i+⌈r*(R.1 i:ℝ)⌉, fun i => z i+⌊r*(R.2 i:ℝ)⌋)

def admissible {d} (R : Box d) (K : Set (Lattice d)) (n : ℕ) (p : Lattice d × ℝ) : Prop :=
  let Q := dilate R p.1 p.2
  2 ≤ p.2 ∧ n ≤ p.2 ∧ (n:ℝ) ≤ (Rectangles.box K Q.1 Q.2).card/(log p.2)^2

def density {d} (R : Box d) (O K : Set (Lattice d)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ p : {p // admissible R K n p},
    let Q := dilate R p.val.1 p.val.2
    ((Rectangles.box (O ∩ K) Q.1 Q.2).card:ℝ≥0∞)/(Rectangles.box K Q.1 Q.2).card

private def cutoff {d} (R : Box d) := 4+Finset.univ.sup (fun i => (R.2 i-R.1 i).toNat)

private theorem widths {d} (R : Box d) (wide : ∀ i, R.1 i < R.2 i)
    (z : Lattice d) {r : ℝ} (hr : (cutoff R:ℝ) ≤ r) (i : Fin d) :
    let Q := dilate R z r
    2 ≤ Q.2 i-Q.1 i ∧ ((Q.2 i-Q.1 i:ℤ):ℝ) ≤ r^2 := by
  have fourCut : (4:ℝ) ≤ cutoff R := by exact_mod_cast (Nat.le_add_right 4 _ : 4 ≤ cutoff R)
  have four := fourCut.trans hr
  have low : (1:ℝ) ≤ (R.2 i:ℝ)-(R.1 i:ℝ) := by exact_mod_cast (show 1 ≤ R.2 i-R.1 i by have := wide i; omega)
  have bound := Finset.le_sup (f:=fun j => (R.2 j-R.1 j).toNat) (Finset.mem_univ i)
  have wi : (R.2 i-R.1 i).toNat ≤ cutoff R := bound.trans (Nat.le_add_left ..)
  have high : (R.2 i:ℝ)-(R.1 i:ℝ) ≤ r := by
    have nz : 0 ≤ R.2 i-R.1 i := by have := wide i; omega
    have eq : (((R.2 i-R.1 i).toNat:ℕ):ℤ) = R.2 i-R.1 i := Int.toNat_of_nonneg nz
    have le : ((R.2 i-R.1 i:ℤ):ℝ) ≤ cutoff R := by exact_mod_cast (eq ▸ (Int.ofNat_le.mpr wi))
    exact (by simpa only [Int.cast_sub] using le : (R.2 i:ℝ)-(R.1 i:ℝ) ≤ cutoff R).trans hr
  have l := Int.le_ceil (r*(R.1 i:ℝ))
  have u := Int.floor_le (r*(R.2 i:ℝ))
  have l' := Int.ceil_lt_add_one (r*(R.1 i:ℝ))
  have u' := Int.lt_floor_add_one (r*(R.2 i:ℝ))
  have ri : (0:ℝ) ≤ r := by linarith
  have lower : (2:ℝ) ≤ (⌊r*(R.2 i:ℝ)⌋:ℤ)-(⌈r*(R.1 i:ℝ)⌉:ℤ) := by
    nlinarith only [four,l',u',mul_le_mul_of_nonneg_left low ri]
  have upper : ((⌊r*(R.2 i:ℝ)⌋:ℤ):ℝ)-(⌈r*(R.1 i:ℝ)⌉:ℤ) ≤ r^2 := by
    nlinarith only [l,u,mul_le_mul_of_nonneg_left high ri]
  simp only [dilate,add_sub_add_left_eq_sub,Int.cast_sub]
  exact ⟨by exact_mod_cast lower,upper⟩

private theorem volume_bounds {d} (hd : 0 < d) (R : Box d) (wide : ∀ i, R.1 i < R.2 i)
    (z : Lattice d) {r : ℝ} (hr : (cutoff R:ℝ) ≤ r) :
    let Q := dilate R z r
    let V := geometricVolume Q.1 Q.2
    (∀ i, Q.1 i < Q.2 i) ∧ 2 ≤ V ∧ log V ≤ (2*d:ℕ)*log r := by
  let Q := dilate R z r
  let V := geometricVolume Q.1 Q.2
  have span (i : Fin d) : 2 ≤ Q.2 i-Q.1 i := (widths R wide z hr i).1
  have two (i : Fin d) : 2 ≤ (Q.2 i-Q.1 i).toNat := by have := span i; omega
  have big : 2 ≤ V := (two ⟨0,hd⟩).trans (Finset.single_le_prod'
    (fun i _ => (show 1 ≤ (Q.2 i-Q.1 i).toNat from by have := two i; omega)) (Finset.mem_univ _))
  have limit : (V:ℝ) ≤ (r^2)^d := by
    change ((∏ i, (Q.2 i-Q.1 i).toNat:ℕ):ℝ) ≤ _
    rw [Nat.cast_prod,←show ∏ _ : Fin d, r^2 = (r^2)^d by simp]
    apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => ?_)
    have eq : (((Q.2 i-Q.1 i).toNat:ℕ):ℤ) = Q.2 i-Q.1 i := Int.toNat_of_nonneg (by have := span i; omega)
    have co : (((Q.2 i-Q.1 i).toNat:ℕ):ℝ) = ((Q.2 i-Q.1 i:ℤ):ℝ) := by exact_mod_cast eq
    rw [co]; exact (widths R wide z hr i).2
  have logs := Real.log_le_log (by exact_mod_cast (show 0 < V by omega)) limit
  simp only [Real.log_pow,Nat.cast_ofNat] at logs
  refine ⟨?_,big,?_⟩
  · intro i
    change Q.1 i < Q.2 i
    have := span i
    omega
  change log (V:ℝ) ≤ ((2*d:ℕ):ℝ)*log r
  push_cast
  linarith only [logs]

/-- Transfer an all-rectangle level estimate with the later paper's log
power of the lattice-site count to P23's source filter. The constants and
the starting volume are independent of the location and the target. -/
theorem rectangular_of_site_power_tests {d} (O K : Set (Lattice d)) (f : ℕ → ℝ)
    {τ B a : ℝ} (ht : 0 ≤ τ)
    (dominates : ∀ᶠ V : ℕ in atTop, (log V)^τ ≤ B*f V)
    (levels : ∀ b : ℝ, 0 ≤ b → b < a → ∃ c : ℝ, 0 < c ∧ ∀ Q : Box d,
      (∀ i, Q.1 i < Q.2 i) →
      c*(LogPowerCriterion.logSites Q)^(1+τ) ≤ (Rectangles.box K Q.1 Q.2).card →
      b ≤ ((Rectangles.box (O ∩ K) Q.1 Q.2).card:ℝ)/(Rectangles.box K Q.1 Q.2).card) :
    ENNReal.ofReal a ≤ filteredRectangularDensity f O K := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  obtain ⟨c,cp,level⟩ := levels r r.coe_nonneg ((ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp hr)
  let F := LogPowerCriterion.factor d
  have fn : 0 ≤ F := by
    dsimp [F,LogPowerCriterion.factor]
    have h := Real.log_nonneg (show 1 ≤ 2+(2:ℝ)^d by linarith [show 0 ≤ (2:ℝ)^d by positivity])
    linarith
  let A := (2*F)^(1+τ)
  have an : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  obtain ⟨k,after⟩ := eventually_atTop.mp dominates
  obtain ⟨N,large⟩ := exists_nat_gt (c*A*B)
  let k₀ := max (max N k) 4
  obtain ⟨M,hn,grow⟩ := large_volume_of_admissible (d:=d) f k₀
  apply le_trans _ (le_iSup (fun m => ⨅ Q : {Q // admissibleBox f K m Q},
    ((Rectangles.box (O ∩ K) Q.val.1 Q.val.2).card:ℝ≥0∞)/(Rectangles.box K Q.val.1 Q.val.2).card) M)
  apply le_iInf
  rintro ⟨Q,adm⟩
  let V := geometricVolume Q.1 Q.2
  have vk : k₀ ≤ V := grow K Q adm
  have four : 4 ≤ V := (le_max_right ..).trans vk
  have vfour : (4:ℝ) ≤ V := by exact_mod_cast four
  have one : 1 ≤ log V := (Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < V by omega))).mpr
    (Real.exp_one_lt_d9.le.trans (by linarith))
  have lp : 0 < log V := zero_lt_one.trans_le one
  have combined := after V ((le_max_right ..).trans ((le_max_left ..).trans vk))
  have logs := LogPowerCriterion.log_comparison Q adm.1
  have bound : LogPowerCriterion.logSites Q ≤ 2*F*log V := logs.2.2.trans (by
    change F*(1+log V) ≤ 2*F*log V
    nlinarith only [mul_le_mul_of_nonneg_left one fn])
  have raised := Real.rpow_le_rpow (zero_le_one.trans logs.1) bound (by linarith : 0 ≤ 1+τ)
  rw [Real.mul_rpow (by positivity : 0 ≤ 2*F) lp.le,Real.rpow_add lp,Real.rpow_one] at raised
  have nle : c*A*B ≤ M := large.le.trans (by exact_mod_cast (le_max_left N k).trans ((le_max_left ..).trans hn))
  have den : 0 < f V*log V := mul_pos adm.2.2.1 lp
  have mass := (le_div_iff₀ den).mp adm.2.2.2
  have cost : c*(LogPowerCriterion.logSites Q)^(1+τ) ≤ (Rectangles.box K Q.1 Q.2).card := by
    calc
      _ ≤ c*(A*(log V*(log V)^τ)) := mul_le_mul_of_nonneg_left raised cp.le
      _ ≤ c*(A*(log V*(B*f V))) := by gcongr
      _ = c*A*B*(f V*log V) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right nle den.le).trans mass
  have positive : 0 < ((Rectangles.box K Q.1 Q.2).card:ℝ) :=
    (mul_pos cp (Real.rpow_pos_of_pos (zero_lt_one.trans_le logs.1) _)).trans_le cost
  simpa only [ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_div_of_pos positive,ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal (level Q adm.1 cost)

/-- The original all-rectangle density with filter f(V)=log V implies
the fixed-shape density (19), uniformly over all translations. -/
theorem of_rectangular {d} (hd : 0 < d) (R : Box d) (wide : ∀ i, R.1 i < R.2 i)
    (O K : Set (Lattice d)) :
    filteredRectangularDensity (fun V => log V) O K ≤ density R O K := by
  apply iSup_le
  intro n
  let C := 2*d
  let N := max (cutoff R) (n*C^2)
  apply le_trans _ (le_iSup (fun m => ⨅ p : {p // admissible R K m p},
    let Q := dilate R p.val.1 p.val.2
    ((Rectangles.box (O ∩ K) Q.1 Q.2).card:ℝ≥0∞)/(Rectangles.box K Q.1 Q.2).card) N)
  apply le_iInf
  rintro ⟨⟨z,r⟩,hr,atN,score⟩
  let Q := dilate R z r
  let V := geometricVolume Q.1 Q.2
  have after : (cutoff R:ℝ) ≤ r := (Nat.cast_le.mpr (le_max_left ..)).trans atN
  obtain ⟨qw,big,bound⟩ := volume_bounds hd R wide z after
  have lv : 0 < log V := Real.log_pos (by exact_mod_cast (show 1 < V from big))
  have lr : 0 < log r := Real.log_pos (by linarith)
  have test : admissibleBox (fun V => log V) K n Q := by
    refine ⟨qw,big,lv,(le_div_iff₀ (mul_pos lv lv)).mpr ?_⟩
    have scale : (n:ℝ)*(C:ℝ)^2 ≤ N := by exact_mod_cast le_max_right (cutoff R) (n*C^2)
    have m := (le_div_iff₀ (sq_pos_of_pos lr)).mp score
    have b : log V ≤ (C:ℝ)*log r := bound
    have sq := mul_self_le_mul_self lv.le b
    have total := (mul_le_mul_of_nonneg_right scale (sq_nonneg (log r))).trans m
    change (n:ℝ)*(log V*log V) ≤ (Rectangles.box K Q.1 Q.2).card
    nlinarith only [mul_le_mul_of_nonneg_left sq (Nat.cast_nonneg (α:=ℝ) n),total]
  exact iInf_le_of_le (⟨Q,test⟩ : {Q // admissibleBox (fun V => log V) K n Q}) le_rfl

/-- The two copies impose the lower and upper faces independently. Both
have positive widths, including when an original side is a singleton. -/
def liftShape {d} (R : Box d) : Box (d+d) :=
  (Fin.append R.1 (fun i => min (R.1 i) (R.2 i) - 1),
   Fin.append (fun i => max (R.1 i) (R.2 i) + 1) R.2)

theorem liftShape_wide {d} (R : Box d) (i : Fin (d+d)) : (liftShape R).1 i < (liftShape R).2 i := by
  induction i using Fin.addCases with
  | left j => simp only [liftShape,Fin.append_left]; omega
  | right j => simp only [liftShape,Fin.append_right]; omega

private theorem liftShape_mem {d} (R : Box d) (z x : Lattice d) {r : ℝ} (hr : 0 ≤ r) :
    let Q := dilate (liftShape R) (MovingCubes.diagonal z) r
    let P := dilate R z r
    MovingCubes.diagonal x ∈ Finset.Icc Q.1 Q.2 ↔ x ∈ Finset.Icc P.1 P.2 := by
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨lo,hi⟩
    exact ⟨fun i => by simpa only [dilate,liftShape,MovingCubes.diagonal,Fin.append_left] using lo (Fin.castAdd d i),
      fun i => by simpa only [dilate,liftShape,MovingCubes.diagonal,Fin.append_right] using hi (Fin.natAdd d i)⟩
  · rintro ⟨lo,hi⟩
    constructor <;> intro j <;> induction j using Fin.addCases with
    | left i =>
      simp only [dilate,liftShape,MovingCubes.diagonal,Fin.append_left]
      first | exact lo i | apply (hi i).trans; apply add_le_add_left; apply Int.floor_mono
                           apply mul_le_mul_of_nonneg_left _ hr
                           exact_mod_cast (show R.2 i ≤ max (R.1 i) (R.2 i)+1 by omega)
    | right i =>
      simp only [dilate,liftShape,MovingCubes.diagonal,Fin.append_right]
      first | exact hi i | apply le_trans _ (lo i); apply add_le_add_left; apply Int.ceil_mono
                           apply mul_le_mul_of_nonneg_left _ hr
                           exact_mod_cast (show min (R.1 i) (R.2 i)-1 ≤ R.1 i by omega)

private theorem liftShape_card {d} (R : Box d) (z : Lattice d) {r : ℝ} (hr : 0 ≤ r) (K : Set (Lattice d)) :
    let Q := dilate (liftShape R) (MovingCubes.diagonal z) r
    let P := dilate R z r
    (Rectangles.box (MovingCubes.diagonal '' K) Q.1 Q.2).card = (Rectangles.box K P.1 P.2).card := by
  let Q := dilate (liftShape R) (MovingCubes.diagonal z) r
  let P := dilate R z r
  have eq : Rectangles.box (MovingCubes.diagonal '' K) Q.1 Q.2 =
      (Rectangles.box K P.1 P.2).image MovingCubes.diagonal := by
    ext y
    constructor
    · intro hy
      obtain ⟨inside,x,hx,rfl⟩ := Rectangles.mem_box.mp hy
      exact Finset.mem_image.mpr ⟨x,Rectangles.mem_box.mpr
        ⟨Finset.mem_Icc.mp ((liftShape_mem R z x hr).mp (Finset.mem_Icc.mpr inside)),hx⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨inside,member⟩ := Rectangles.mem_box.mp hx
      exact Rectangles.mem_box.mpr ⟨Finset.mem_Icc.mp ((liftShape_mem R z x hr).mpr
        (Finset.mem_Icc.mpr inside)),x,member,rfl⟩
  change (Rectangles.box _ Q.1 Q.2).card = _
  rw [eq,Finset.card_image_of_injective _ (MovingCubes.diagonal_injective d)]

/-- Uniform fixed-shape density for positive-width templates in doubled
dimension entails the same guarantee even on templates with zero-width
sides. The common real dilation and lattice translation are preserved. -/
theorem diagonal_density {d} (R : Box d) (K O : Set (Lattice d)) (Y : Set (Lattice (d+d)))
    (captured : MovingCubes.diagonal ⁻¹' Y ⊆ O) :
    density (liftShape R) Y (MovingCubes.diagonal '' K) ≤ density R O K := by
  apply iSup_le
  intro n
  apply le_trans _ (le_iSup _ n)
  apply le_iInf
  rintro ⟨⟨z,r⟩,two,large,mass⟩
  have pos : 0 ≤ r := by linarith
  let Q := dilate (liftShape R) (MovingCubes.diagonal z) r
  let P := dilate R z r
  have admiss : admissible (liftShape R) (MovingCubes.diagonal '' K) n (MovingCubes.diagonal z,r) :=
    ⟨two,large,by simpa only [liftShape_card R z pos K] using mass⟩
  apply iInf_le_of_le (⟨(MovingCubes.diagonal z,r),admiss⟩ :
    {p // admissible (liftShape R) (MovingCubes.diagonal '' K) n p})
  change ((Rectangles.box (Y ∩ MovingCubes.diagonal '' K) Q.1 Q.2).card:ℝ≥0∞) / _ ≤ _
  rw [←Set.image_preimage_inter,liftShape_card R z pos,liftShape_card R z pos]
  have sub : Rectangles.box ((MovingCubes.diagonal ⁻¹' Y) ∩ K) P.1 P.2 ⊆ Rectangles.box (O ∩ K) P.1 P.2 := by
    intro x hx
    obtain ⟨inside,hit,mem⟩ := Rectangles.mem_box.mp hx
    exact Rectangles.mem_box.mpr ⟨inside,captured hit,mem⟩
  change ((Rectangles.box ((MovingCubes.diagonal ⁻¹' Y) ∩ K) P.1 P.2).card:ℝ≥0∞) /
      (Rectangles.box K P.1 P.2).card ≤
    ((Rectangles.box (O ∩ K) P.1 P.2).card:ℝ≥0∞) / (Rectangles.box K P.1 P.2).card
  exact ENNReal.div_le_div_right (by exact_mod_cast Finset.card_le_card sub) _

end
end GenLimit.KleinbergWei.Banach.FixedShape
