import GenLimit.Paper23_BanachDensityTopologyAndGeometry.VolumeError
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredDensity

/-! The positive-occupancy case of Theorem 5.5. Occupancy is required
only on the boxes tested at a sufficiently high filter threshold. -/
namespace GenLimit.KleinbergWei.Banach
open Set Filter Real
open scoped Classical ENNReal
noncomputable section

private theorem admissible_lower {d} {f : ℕ → ℝ} {P : Set (Lattice d)} {r}
    {n m : ℕ} (le : n ≤ m) (h : admissibleBox f P m r) : admissibleBox f P n r :=
  ⟨h.1,h.2.1,h.2.2.1,(by exact_mod_cast le : (n:ℝ) ≤ m).trans h.2.2.2⟩

/-- Local geometric occupancy on the cofinal rectangle filter suffices
for one online generator to attain 1/2 minus ε on arbitrary finite-rank
families. The generator is independent of the target and the filter. -/
theorem filtered_dense_box_generation {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R)
    {ε ρ : ℝ} (he : 0 < ε) (density : 0 < ρ) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧ ∀ f : ℕ → ℝ, Tendsto f atTop atTop →
        (∃ N : ℕ, ∀ l u, admissibleBox f (e '' C z) N (l,u) →
          ρ*geometricVolume l u ≤ (Rectangles.box (e '' C z) l u).card) →
        ENNReal.ofReal (1/2-ε) ≤ filteredRectangularDensity f (range (cubePlay A s)) (e '' C z) := by
  let q := min (ε/4) (1/4)
  have qp : 0 < q := lt_min (by positivity) (by norm_num)
  have q1 : q ≤ 1/2 := (min_le_right ..).trans (by norm_num)
  have qe : 3*q ≤ ε := by have h : q ≤ ε/4 := min_le_left ..; linarith
  obtain ⟨A,guarantee⟩ := rectangular_volume_error e inj C inf rank qp q1 (mul_pos qp density)
  refine ⟨A,fun z s pres => ?_⟩
  obtain ⟨valid,H,all⟩ := guarantee z s pres
  refine ⟨valid,?_⟩
  intro f grows dense
  obtain ⟨N,dense⟩ := dense
  obtain ⟨n,hn⟩ := exists_nat_gt (H/q)
  obtain ⟨M,large⟩ := large_count_of_admissible (d:=d) f grows (n+1)
  let t := max M N
  let P := e '' C z
  let O := range (cubePlay A s)
  apply le_trans _ (le_iSup (fun a => ⨅ r : {r // admissibleBox f P a r},
    ((Rectangles.box (O ∩ P) r.val.1 r.val.2).card:ℝ≥0∞)/(Rectangles.box P r.val.1 r.val.2).card) t)
  apply le_iInf
  rintro ⟨⟨l,u⟩,test⟩
  let m := (Rectangles.box P l u).card
  have size : n+1 ≤ m := large P (l,u) (admissible_lower (le_max_left ..) test)
  have mp : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have fill : ρ*geometricVolume l u ≤ (m:ℝ) := dense l u (admissible_lower (le_max_right ..) test)
  have fixed : H ≤ q*m := by
    have lt := (div_lt_iff₀ qp).mp hn
    have le : (n:ℝ) ≤ m := by exact_mod_cast (show n ≤ m by omega)
    nlinarith [mul_le_mul_of_nonneg_left le qp.le]
  have count := all l u test.1
  change (1/2-q)*(m:ℝ) ≤ ((Rectangles.box (O ∩ P) l u).card:ℝ)+q*ρ*geometricVolume l u+H at count
  have rat : (1/2-ε) ≤ ((Rectangles.box (O ∩ P) l u).card:ℝ)/m := by
    apply (le_div_iff₀ mp).2
    nlinarith only [count,fixed,mul_le_mul_of_nonneg_left fill qp.le,mul_le_mul_of_nonneg_right qe mp.le]
  simpa only [ENNReal.ofReal_div_of_pos mp,ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal rat

end
end GenLimit.KleinbergWei.Banach
