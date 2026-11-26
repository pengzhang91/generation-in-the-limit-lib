import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TileAccounting
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LatticeTransport

/-! A local online estimate for arbitrary point sets and general finite-rank
families. The volume coefficient can be made arbitrarily small before play.
The remaining additive constant is independent of the tested rectangle. -/
namespace GenLimit.KleinbergWei.Banach
open Set Filter Real DensityMeasures LatticeTiles TileGenerator
open scoped Classical Topology
noncomputable section

private theorem small_loss (d R : ℕ) {q η : ℝ} (eta : 0 < η) :
    ∃ L : ℕ, 0 < L ∧ (3:ℝ)^d*(R*loss d L q) ≤ η*L := by
  have logs : Tendsto (fun L : ℕ => log L/(L:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have inv : Tendsto (fun L : ℕ => (1:ℝ)/(L:ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop _
  have limit : Tendsto (fun L : ℕ => (3:ℝ)^d*(R*loss d L q)/L) atTop (𝓝 0) := by
    have h := ((inv.const_mul (log (1+q))).add (logs.const_mul (2*(d:ℝ)))).const_mul ((3:ℝ)^d*R/(2*q))
    convert h using 1
    · funext L; unfold loss; ring
    · simp
  have ev := (limit.eventually_lt_const eta).and (eventually_ge_atTop 1)
  obtain ⟨L,small,hp⟩ := ev.exists
  exact ⟨L,hp,by have := (div_lt_iff₀ (by exact_mod_cast hp : (0:ℝ)<L)).mp small; linarith⟩

theorem section_card {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (K : Set ℕ) (l u : Lattice d) :
    (sectionWords e inj K l u).card = (Rectangles.box (e '' K) l u).card := by
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    obtain ⟨rect,mem⟩ := (mem_section e inj).mp hx
    exact Rectangles.mem_box.mpr ⟨Finset.mem_Icc.mp rect,x,mem,rfl⟩
  · exact fun _ _ _ _ eq => inj eq
  · intro x hx
    obtain ⟨rect,i,mem,rfl⟩ := Rectangles.mem_box.mp hx
    exact ⟨i,(mem_section e inj).mpr ⟨Finset.mem_Icc.mpr rect,mem⟩,rfl⟩

/-- For any two positive error allowances, one valid generator achieves
an additive error bounded by q times the target count plus η times the
volume with singleton sides counted as one plus a presentation-dependent constant, uniformly
over all sizes, positions and aspect ratios. -/
theorem rectangular_unit_volume_error {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R) {q η : ℝ}
    (hq : 0 < q) (h1 : q ≤ 1/2) (eta : 0 < η) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧ ∃ H : ℝ, ∀ l u, l ≤ u →
        let K := e '' C z
        let O := range (cubePlay A s)
        (1/2-q)*((Rectangles.box K l u).card:ℝ) ≤
          (Rectangles.box (O ∩ K) l u).card + η*unitVolume l u + H := by
  obtain ⟨L,hL,small⟩ := small_loss d R (q:=q) eta
  let G := rule (L:=L) rank e inj q inf
  refine ⟨LatticeTransport.lift e G,fun z s pres => ?_⟩
  let t := Function.invFun e ∘ s
  obtain ⟨full,outputs,carries⟩ := LatticeTransport.run e inj pres G
  refine ⟨carries (validity rank e inj q inf full),?_⟩
  obtain ⟨H,est⟩ := global_count rank e inj hL hq h1 inf full
  let a := (R:ℝ)*loss d L q
  have an : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (loss_nonneg d hL hq)
  refine ⟨H+(3:ℝ)^d*a,fun l u widths => ?_⟩
  let O := range (OrderedFocus.play G t)
  let K := C z
  have eq : (sectionWords e inj K l u).filter (· ∈ O) = sectionWords e inj (O ∩ K) l u := by
    ext; simp only [Finset.mem_filter,mem_section,Set.mem_inter_iff]; tauto
  have bound := est l u
  change (1/2-q)*((sectionWords e inj K l u).card:ℝ) ≤
    (((sectionWords e inj K l u).filter (· ∈ O)).card:ℝ) + (indices L l u).card*a + H at bound
  rw [eq,section_card,section_card] at bound
  dsimp only; rw [outputs,←Set.image_inter inj]
  let V := unitVolume l u
  have cnt : (L:ℝ)*(indices L l u).card ≤ (3:ℝ)^d*(L+V) := by
    exact_mod_cast card_indices hL widths
  have lpos : (0:ℝ) < L := by exact_mod_cast hL
  have charge : ((indices L l u).card:ℝ)*a ≤ (3:ℝ)^d*a+η*V := by
    apply le_of_mul_le_mul_left (a := (L:ℝ)) _ lpos
    nlinarith only [mul_le_mul_of_nonneg_right cnt an,
      mul_le_mul_of_nonneg_right small (Nat.cast_nonneg (α:=ℝ) V)]
  change (1/2-q)*((Rectangles.box (e '' K) l u).card:ℝ) ≤
    (Rectangles.box (e '' (O ∩ K)) l u).card+η*V+(H+(3:ℝ)^d*a)
  linarith

/-- On positive-width boxes the geometric volume yields the same estimate. -/
theorem rectangular_volume_error {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R) {q η : ℝ}
    (hq : 0 < q) (h1 : q ≤ 1/2) (eta : 0 < η) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧ ∃ H : ℝ, ∀ l u, (∀ j, l j < u j) →
        let K := e '' C z
        let O := range (cubePlay A s)
        (1/2-q)*((Rectangles.box K l u).card:ℝ) ≤
          (Rectangles.box (O ∩ K) l u).card + η*geometricVolume l u + H := by
  obtain ⟨A,proof⟩ := rectangular_unit_volume_error e inj C inf rank hq h1 eta
  refine ⟨A,fun z s pres => ?_⟩
  obtain ⟨ok,H,bound⟩ := proof z s pres
  exact ⟨ok,H,fun l u h => by simpa only [unitVolume_eq h] using bound l u (fun i => (h i).le)⟩

end
end GenLimit.KleinbergWei.Banach
