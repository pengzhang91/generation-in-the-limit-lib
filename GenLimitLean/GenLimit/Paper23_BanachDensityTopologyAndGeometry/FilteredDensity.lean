import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredBoxes

/-! The ratio filter in Definition 5.3, on closed integer rectangles with
positive side lengths and defined, positive logarithmic denominator. -/
namespace GenLimit.KleinbergWei.Banach
open Finset Real Filter
open scoped Classical ENNReal
noncomputable section

/-- A closed integer box has at most two lattice sites per unit of
geometric length on each positive side. -/
theorem card_le_geometricVolume {d} (P : Set (Lattice d)) {l u : Lattice d}
    (widths : ∀ i, l i < u i) :
    (Rectangles.box P l u).card ≤ 2^d * geometricVolume l u := by
  apply (Finset.card_filter_le ..).trans
  rw [Pi.card_Icc]
  calc
    _ ≤ ∏ i, 2*(u i-l i).toNat := by
      apply Finset.prod_le_prod' (fun i _ => ?_)
      rw [Int.card_Icc]
      have h := widths i
      omega
    _ = _ := by simp [Finset.prod_mul_distrib,geometricVolume]

/-- The boxes tested at threshold n in Definition 5.3. A volume of one
has zero logarithmic denominator. -/
def admissibleBox {d} (f : ℕ → ℝ) (P : Set (Lattice d)) (n : ℕ)
    (r : Lattice d × Lattice d) : Prop :=
  let V := geometricVolume r.1 r.2
  (∀ j, r.1 j < r.2 j) ∧ 2 ≤ V ∧ 0 < f V ∧
    n ≤ (Rectangles.box P r.1 r.2).card / (f V * log V)

/-- The relative filtered rectangular lower density. An empty family of
tests has infimum top in the extended nonnegative reals. -/
def filteredRectangularDensity {d} (f : ℕ → ℝ) (O P : Set (Lattice d)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ r : {r // admissibleBox f P n r},
    ((Rectangles.box (O ∩ P) r.val.1 r.val.2).card : ℝ≥0∞) /
      (Rectangles.box P r.val.1 r.val.2).card

/-- Definition 5.3 with the admissible rectangles further restricted to a
prescribed family of tests. Taking all tests gives the source density. -/
def filteredRectangularDensityOn {d} (test : (Lattice d × Lattice d) → Prop)
    (f : ℕ → ℝ) (O P : Set (Lattice d)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ r : {r // admissibleBox f P n r ∧ test r},
    ((Rectangles.box (O ∩ P) r.val.1 r.val.2).card : ℝ≥0∞) /
      (Rectangles.box P r.val.1 r.val.2).card

theorem admissibleBox_anti {d} {f : ℕ → ℝ} {P : Set (Lattice d)} {n m : ℕ}
    {r : Lattice d × Lattice d} (le : n ≤ m) (adm : admissibleBox f P m r) :
    admissibleBox f P n r :=
  ⟨adm.1,adm.2.1,adm.2.2.1,(Nat.cast_le.mpr le).trans adm.2.2.2⟩

/-- Tests can be restricted after an arbitrary finite threshold. -/
theorem filteredDensityOn_mono_eventually {d} (f : ℕ → ℝ) (O P : Set (Lattice d))
    (S T : (Lattice d × Lattice d) → Prop) (N : ℕ)
    (inside : ∀ r, admissibleBox f P N r → T r → S r) :
    filteredRectangularDensityOn S f O P ≤ filteredRectangularDensityOn T f O P := by
  apply iSup_le
  intro n
  apply le_trans _ (le_iSup (fun m => ⨅ r : {r // admissibleBox f P m r ∧ T r},
    ((Rectangles.box (O ∩ P) r.val.1 r.val.2).card:ℝ≥0∞)/(Rectangles.box P r.val.1 r.val.2).card) (max n N))
  apply le_iInf
  rintro ⟨r,adm,test⟩
  exact iInf_le_of_le (⟨r,admissibleBox_anti (le_max_left ..) adm,
    inside r (admissibleBox_anti (le_max_right ..) adm) test⟩ : {r // admissibleBox f P n r ∧ S r}) le_rfl

theorem filteredDensityOn_all {d} (f : ℕ → ℝ) (O P : Set (Lattice d)) :
    filteredRectangularDensityOn (fun _ => True) f O P = filteredRectangularDensity f O P := by
  apply congrArg iSup
  funext n
  apply le_antisymm <;> apply le_iInf
  · rintro ⟨r,adm⟩
    exact iInf_le_of_le (⟨r,adm,trivial⟩ : {r // admissibleBox f P n r ∧ True}) le_rfl
  · rintro ⟨r,adm,_⟩
    exact iInf_le_of_le (⟨r,adm⟩ : {r // admissibleBox f P n r}) le_rfl

private theorem positive_denom {f : ℕ → ℝ} {V : ℕ} (hv : 2 ≤ V) (hf : 0 < f V) :
    0 < f V*log V :=
  mul_pos hf (Real.log_pos (by exact_mod_cast (show 1 < V by omega)))

/-- High ratio forces large volume uniformly over the position and the target. -/
theorem large_volume_of_admissible {d} (f : ℕ → ℝ) (N : ℕ) :
    ∃ M : ℕ, N ≤ M ∧ ∀ (P : Set (Lattice d)) r, admissibleBox f P M r →
      N ≤ geometricVolume r.1 r.2 := by
  let cap (V : ℕ) := ((2^d*V : ℕ):ℝ)/(f V*log V)
  let bound := ∑ V ∈ Finset.range N, |cap V|
  obtain ⟨m,hm⟩ := exists_nat_gt bound
  refine ⟨max m N,le_max_right ..,?_⟩
  intro P r h
  obtain ⟨w,v,hf,big⟩ := h
  let V := geometricVolume r.1 r.2
  by_contra! short
  have total := Finset.single_le_sum (f := fun v => |cap v|) (fun v _ => abs_nonneg _) (Finset.mem_range.mpr short)
  have cap_le : cap V ≤ bound := (le_abs_self _).trans total
  have count : ((Rectangles.box P r.1 r.2).card:ℝ) ≤ ((2^d*V : ℕ):ℝ) := by
    exact_mod_cast card_le_geometricVolume P w
  have ratio := div_le_div_of_nonneg_right count (positive_denom v hf).le
  have msmall : (m:ℝ) ≤ max m N := by exact_mod_cast le_max_left m N
  exact (not_le_of_gt hm) (msmall.trans (big.trans (ratio.trans cap_le)))

/-- For a growing filter, every sufficiently high admissible ratio
also forces an arbitrarily large target count. -/
theorem large_count_of_admissible {d} (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) (H : ℕ) :
    ∃ N : ℕ, ∀ (P : Set (Lattice d)) r, admissibleBox f P N r →
      H ≤ (Rectangles.box P r.1 r.2).card := by
  obtain ⟨t,after⟩ := eventually_atTop.mp ((tendsto_atTop.mp grows) 1)
  obtain ⟨N,hn,large⟩ := large_volume_of_admissible (d := d) f (max H (max 4 t))
  refine ⟨N,fun P r h => ?_⟩
  let V := geometricVolume r.1 r.2
  have big := large P r h
  have four : 4 ≤ V := (le_max_left ..).trans ((le_max_right ..).trans big)
  have ft := after V ((le_max_right ..).trans ((le_max_right ..).trans big))
  have ln : 1 ≤ log V := by
    apply (Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < V by omega))).2
    have v4 : (4:ℝ) ≤ V := by exact_mod_cast four
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have den : 1 ≤ f V*log V := one_le_mul_of_one_le_of_one_le ft ln
  have cnt := (le_div_iff₀ (lt_of_lt_of_le zero_lt_one den)).mp h.2.2.2
  have nc : (N:ℝ) ≤ (Rectangles.box P r.1 r.2).card :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) den).trans cnt
  exact ((le_max_left ..).trans hn).trans (by exact_mod_cast nc : N ≤ _)

/-- The same static coloring simultaneously achieves the source's ratio-filter
density for each of its two classes. -/
theorem static_filtered_density {d} (hd : 0 < d) {ε : ℝ} (he : 0 < ε)
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) (P : Set (Lattice d)) :
    ∃ c : Lattice d → Bool, ∀ b,
      ENNReal.ofReal (1/2-ε) ≤ filteredRectangularDensity f {v | c v=b} P := by
  obtain ⟨N,split⟩ := static_filtered_split hd he f grows
  obtain ⟨c,parts⟩ := split P
  obtain ⟨M,big,large⟩ := large_volume_of_admissible (d := d) f (N+1)
  refine ⟨c,fun b => ?_⟩
  apply le_trans _ (le_iSup (fun n => ⨅ r : {r // admissibleBox f P n r},
    ((Rectangles.box ({v | c v=b} ∩ P) r.val.1 r.val.2).card : ℝ≥0∞) /
      (Rectangles.box P r.val.1 r.val.2).card) M)
  apply le_iInf
  rintro ⟨⟨l,u⟩,h⟩
  have size := large P _ h
  obtain ⟨w,hv,hf,ratio⟩ := h
  let V := geometricVolume l u
  let T := Rectangles.box P l u
  have den := positive_denom hv hf
  have mul := (le_div_iff₀ den).mp ratio
  have nm : (N:ℝ) ≤ M := by exact_mod_cast (show N ≤ M by omega)
  have mp : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have enough : (N:ℝ)*f V*log V ≤ T.card := by
    change (M:ℝ)*(f V*log V) ≤ T.card at mul
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_right nm den.le).trans mul
  have hsize : N ≤ geometricVolume l u := by dsimp at size; omega
  have density := parts l u w hsize enough b
  have count_pos : 0 < (T.card:ℝ) := (mul_pos mp den).trans_le mul
  have eq : Rectangles.box ({v | c v=b} ∩ P) l u = T.filter (fun x => c x=b) := by
    ext x; simp [T,Rectangles.box,Set.mem_inter_iff]; tauto
  change ENNReal.ofReal (1/2-ε) ≤ ((Rectangles.box ({v | c v=b} ∩ P) l u).card:ℝ≥0∞)/T.card
  rw [eq]
  have real_bound := ENNReal.ofReal_le_ofReal ((le_div_iff₀ count_pos).2 density)
  simpa only [ENNReal.ofReal_div_of_pos count_pos, ENNReal.ofReal_natCast] using real_bound

/-- For the permitted growth function g(v)=v, the ratio in Definition
5.3 is bounded by 2^d/log 2 for all targets. Corollary 5.4 requires a
nonempty cofinal filter to yield density zero. -/
theorem linear_filter_empty {d} (P O : Set (Lattice d)) :
    filteredRectangularDensity (fun v => v) O P = ⊤ := by
  obtain ⟨N,hn⟩ := exists_nat_gt ((2:ℝ)^d/log 2)
  apply top_unique
  apply le_trans _ (le_iSup (fun n => ⨅ r : {r // admissibleBox (fun v => v) P n r},
    ((Rectangles.box (O ∩ P) r.val.1 r.val.2).card : ℝ≥0∞) /
      (Rectangles.box P r.val.1 r.val.2).card) N)
  apply le_iInf
  rintro ⟨⟨l,u⟩,w,hv,hf,ratio⟩
  let V := geometricVolume l u
  have pos : (0:ℝ) < V := hf
  have den : 0 < (V:ℝ)*log V := positive_denom (f := fun v => v) hv hf
  have two : (0:ℝ) < log 2 := Real.log_pos (by norm_num)
  have le : log 2 ≤ log V := Real.log_le_log (by norm_num) (by exact_mod_cast hv)
  have h := (le_div_iff₀ den).mp ratio
  have card : ((Rectangles.box P l u).card:ℝ) ≤ (2:ℝ)^d*V := by exact_mod_cast card_le_geometricVolume P w
  have lt := (div_lt_iff₀ two).mp hn
  have worse := mul_le_mul_of_nonneg_left le (Nat.cast_nonneg (α := ℝ) N)
  exfalso
  nlinarith only [mul_lt_mul_of_pos_right (lt_of_lt_of_le lt worse) pos, h.trans card]

end
end GenLimit.KleinbergWei.Banach
