import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilterShells
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredDensity

/-! Assembly of per-shell logarithmic losses on the source density filter.
The geometrical cover and the absorption of startup costs are independent
of how a strategy earns its local outputs. -/
namespace GenLimit.KleinbergWei.Banach.FilterShells
open Finset Filter Set Real
open scoped Classical ENNReal
noncomputable section

/-- A logarithmic loss per intersected shell suffices for the exact filtered
lower density, even after a fixed finite startup loss. -/
theorem density_of_shell_counts_on {d} (test : (Lattice d × Lattice d) → Prop) (P O : Set (Lattice d)) (f : ℕ → ℝ)
    (grows : Tendsto f atTop atTop) (a C H : ℝ) (hc : 0 ≤ C) (hh : 0 ≤ H)
    (counts : ∀ l u, test (l,u) → ∀ J : Finset ℕ, (∀ x ∈ Finset.Icc l u, index f grows (radius x) ∈ J) →
      (∀ i, l i < u i) → a*((Rectangles.box P l u).card:ℝ) ≤
        (Rectangles.box (O ∩ P) l u).card + J.card * C * (1+log (geometricVolume l u)) + H) :
    ENNReal.ofReal a ≤ filteredRectangularDensityOn test f O P := by
  apply ENNReal.le_of_forall_nnreal_lt; intro r hr
  have less : (r:ℝ) < a := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp hr
  let δ := a-r
  have dp : 0 < δ := sub_pos.mpr less
  obtain ⟨n,hn⟩ := exists_nat_gt ((6*C+H)/δ)
  obtain ⟨t,ft⟩ := eventually_atTop.mp ((tendsto_atTop.mp grows) 1)
  obtain ⟨M,high,size⟩ := large_volume_of_admissible (d:=d) f (max 4 (max t (n+1)))
  apply le_trans _ (le_iSup (fun k => ⨅ p : {p // admissibleBox f P k p ∧ test p},
    ((Rectangles.box (O ∩ P) p.val.1 p.val.2).card:ℝ≥0∞)/(Rectangles.box P p.val.1 p.val.2).card) M)
  apply le_iInf
  rintro ⟨⟨l,u⟩,adm,tested⟩
  let V := geometricVolume l u
  let m := (Rectangles.box P l u).card
  have four : 4 ≤ V := (le_max_left ..).trans (size P (l,u) adm)
  have tg : t ≤ V := (le_max_left ..).trans ((le_max_right ..).trans (size P (l,u) adm))
  have nm : n+1 ≤ M := (le_max_right ..).trans ((le_max_right ..).trans high)
  have fp := ft V tg
  have lp : 1 ≤ log V := by
    apply (Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < V by omega))).2
    have v4 : (4:ℝ) ≤ V := by exact_mod_cast four
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have den : 1 ≤ f V*log V := one_le_mul_of_one_le_of_one_le fp lp
  have ratio : (M:ℝ)*(f V*log V) ≤ m := (le_div_iff₀ (lt_of_lt_of_le zero_lt_one den)).mp adm.2.2.2
  have mp : (0:ℝ) < m := (mul_pos (by exact_mod_cast (show 0 < M by omega)) (lt_of_lt_of_le zero_lt_one den)).trans_le ratio
  obtain ⟨J,small,cover⟩ := rectangle_cover f grows l u adm.1 (by linarith : 0 ≤ f V)
  have bound := counts l u tested J cover adm.1
  have pay : (J.card:ℝ)*C*(1+log V)+H ≤ (6*C+H)*(f V*log V) := by
    have j : (J.card:ℝ) ≤ 3*f V := by change _ ≤ f V + 2 at small; linarith
    have p := mul_le_mul j (by linarith : 1+log V ≤ 2*log V) (by linarith) (by linarith)
    nlinarith only [mul_le_mul_of_nonneg_right p hc,mul_le_mul_of_nonneg_right den hh]
  have nM : (n:ℝ) ≤ M := by exact_mod_cast (show n ≤ M by omega)
  have budget : 6*C+H ≤ δ*M := by
    have := (div_lt_iff₀ dp).mp hn
    nlinarith [mul_le_mul_of_nonneg_left nM dp.le]
  have charge : (J.card:ℝ)*C*(1+log V)+H ≤ δ*m := by
    apply pay.trans; nlinarith only [mul_le_mul_of_nonneg_right budget (zero_le_one.trans den),
      mul_le_mul_of_nonneg_left ratio dp.le]
  have ans : (r:ℝ) ≤ ((Rectangles.box (O ∩ P) l u).card:ℝ)/m := by
    change a*(m:ℝ) ≤ (Rectangles.box (O ∩ P) l u).card + J.card*C*(1+log V)+H at bound
    apply (le_div_iff₀ mp).2; dsimp [δ] at charge; linarith
  simpa only [ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_div_of_pos mp,ENNReal.ofReal_natCast]
    using ENNReal.ofReal_le_ofReal ans

theorem density_of_shell_counts {d} (P O : Set (Lattice d)) (f : ℕ → ℝ)
    (grows : Tendsto f atTop atTop) (a C H : ℝ) (hc : 0 ≤ C) (hh : 0 ≤ H)
    (counts : ∀ l u, ∀ J : Finset ℕ, (∀ x ∈ Finset.Icc l u, index f grows (radius x) ∈ J) →
      (∀ i, l i < u i) → a*((Rectangles.box P l u).card:ℝ) ≤
        (Rectangles.box (O ∩ P) l u).card + J.card * C * (1+log (geometricVolume l u)) + H) :
    ENNReal.ofReal a ≤ filteredRectangularDensity f O P := by
  simpa only [filteredDensityOn_all] using
    density_of_shell_counts_on (fun _ => True) P O f grows a C H hc hh (fun l u _ => counts l u)

end
end GenLimit.KleinbergWei.Banach.FilterShells
