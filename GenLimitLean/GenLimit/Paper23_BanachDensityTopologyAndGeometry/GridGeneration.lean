import GenLimit.Paper23_BanachDensityTopologyAndGeometry.IntervalOptimality
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.DenseBoxGeneration
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.GridTrace
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleObstruction

/-! Local online generation on a common, arbitrarily sparse rectangular grid.
Here occupancy is measured by grid points, independently of physical volume.
When this occupancy is positive on large target traces, the result holds for
the unfiltered density of Definition 1.1. -/
namespace GenLimit.KleinbergWei.Banach
open Set Filter Real
open scoped Classical ENNReal
noncomputable section

private def onImage {d} (E : Lattice d → Lattice d) (G : List (Lattice d) → Lattice d)
    (p : List (Lattice d)) := E (G (p.map (Function.invFun E)))

private theorem image_play {d} (E : Lattice d → Lattice d) (inj : Function.Injective E)
    {K : Set (Lattice d)} {s : ℕ → Lattice d} (pres : range s = E '' K)
    (G : List (Lattice d) → Lattice d) :
    let t := Function.invFun E ∘ s
    range t = K ∧ range (cubePlay (onImage E G) s) = E '' range (cubePlay G t) ∧
      (cubeValid G t K → cubeValid (onImage E G) s (E '' K)) := by
  let t := Function.invFun E ∘ s
  have left := Function.leftInverse_invFun inj
  have right (i) : E (t i) = s i := by
    obtain ⟨x,_,eq⟩ := (show s i ∈ E '' K from pres ▸ mem_range_self i)
    simp [t,←eq,left x]
  have eq (i) : cubePlay (onImage E G) s i = E (cubePlay G t i) := by
    simp [cubePlay,onImage,t,textPrefix,List.map_map]
  refine ⟨?_,?_,?_⟩
  · rw [range_comp,pres,image_image,show (fun x => Function.invFun E (E x)) = (fun x => x) from funext left,
      Set.image_id']
  · rw [←range_comp]; exact congrArg range (funext eq)
  · rintro ⟨T,ok⟩
    refine ⟨T,fun i hi => ?_⟩
    obtain ⟨y,fresh,recent⟩ := ok i hi
    rw [eq]; exact ⟨⟨_,y,rfl⟩,fun j le h => fresh j le (inj ((right j).trans h)),
      fun j lt h => recent j lt (inj ((eq j).symm.trans h))⟩

/-- Omitting boxes outside a growing ratio filter can only raise the
unrestricted target-count lower density. -/
theorem unfiltered_le_filtered {d} (P O : Set (Lattice d)) (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) :
    Rectangles.lowerDensity O P ≤ filteredRectangularDensity f O P := by
  apply iSup_le; intro n
  obtain ⟨N,size⟩ := large_count_of_admissible (d:=d) f grows n
  apply le_trans _ (le_iSup (fun t => ⨅ r : {r // admissibleBox f P t r},
    ((Rectangles.box (O ∩ P) r.val.1 r.val.2).card:ℝ≥0∞)/(Rectangles.box P r.val.1 r.val.2).card) N)
  apply le_iInf; rintro ⟨r,h⟩
  exact iInf_le (fun b : {b : Lattice d × Lattice d // n ≤ (Rectangles.box P b.1 b.2).card} =>
    ((Rectangles.box (O ∩ P) b.val.1 b.val.2).card:ℝ≥0∞)/(Rectangles.box P b.val.1 b.val.2).card) ⟨r,size P r h⟩

/-- Uniformly grid-dense target traces achieve the near-half bound on every
sufficiently populated rectangle, even after arbitrary coordinate stretches. -/
theorem grid_generation {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (φ : Fin d → ℤ → ℤ) (inc : ∀ j, StrictMono (φ j))
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R) {ε ρ : ℝ} (he : 0 < ε) (hp : 0 < ρ) :
    let E := GridTrace.encode φ
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d),
      let P := E '' (e '' C z)
      range s = P → cubeValid A s P ∧
        ((∃ n : ℕ, ∀ l u, n ≤ (Rectangles.box P l u).card →
          ρ*(Rectangles.box (range E) l u).card ≤ (Rectangles.box P l u).card) →
          ENNReal.ofReal (1/2-ε) ≤ Rectangles.lowerDensity (range (cubePlay A s)) P) := by
  let E := GridTrace.encode φ
  let q := min (ε/4) (1/4)
  have qp : 0 < q := lt_min (by positivity) (by norm_num)
  have q1 : q ≤ 1/2 := (min_le_right ..).trans (by norm_num)
  have qe : 3*q ≤ ε := by have h : q ≤ ε/4 := min_le_left ..; linarith
  obtain ⟨G,strategy⟩ := rectangular_unit_volume_error e inj C inf rank qp q1 (mul_pos qp hp)
  refine ⟨onImage E G,fun z s => ?_⟩
  let K := e '' C z
  let P := E '' K
  change range s = P → _
  intro pres
  let t := Function.invFun E ∘ s
  obtain ⟨full,outputs,valid⟩ := image_play E (GridTrace.injective inc) pres G
  obtain ⟨ok,H,est⟩ := strategy z t full
  refine ⟨valid ok,?_⟩
  rintro ⟨n,dense⟩
  let O := range (cubePlay G t)
  obtain ⟨h,hn⟩ := exists_nat_gt (H/q)
  let N := max n (h+1)
  apply le_trans _ (le_iSup (fun a => ⨅ r : {r : Lattice d × Lattice d // a ≤ (Rectangles.box P r.1 r.2).card},
    ((Rectangles.box (range (cubePlay (onImage E G) s) ∩ P) r.val.1 r.val.2).card:ℝ≥0∞) /
      (Rectangles.box P r.val.1 r.val.2).card) N)
  apply le_iInf
  rintro ⟨⟨l,u⟩,large⟩
  let m := (Rectangles.box P l u).card
  change N ≤ m at large
  have mn : n ≤ m := (le_max_left ..).trans large
  have mh : h+1 ≤ m := (le_max_right ..).trans large
  have pos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < m by omega)
  obtain ⟨rect,y,_,rfl⟩ := Rectangles.mem_box.mp hx
  obtain ⟨a,b,ordered,card,grid⟩ := GridTrace.rectangle φ inc (Finset.mem_Icc.mpr rect)
  have occupy : ρ*(Rectangles.box (range E) l u).card ≤ (m:ℝ) := dense l u mn
  have vol : ρ*(LatticeTiles.unitVolume a b) ≤ (m:ℝ) := by
    rw [grid] at occupy
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast LatticeTiles.unitVolume_le_card ordered) hp.le).trans occupy
  have fixed : H ≤ q*m := by
    have l := (div_lt_iff₀ qp).mp hn
    have le : (h:ℝ) ≤ m := by exact_mod_cast (show h ≤ m by omega)
    nlinarith [mul_le_mul_of_nonneg_left le qp.le]
  have bound := est a b ordered
  change (1/2-q)*((Rectangles.box K a b).card:ℝ) ≤
      (Rectangles.box (O ∩ K) a b).card+q*ρ*LatticeTiles.unitVolume a b+H at bound
  rw [←card K,←card (O ∩ K)] at bound
  change (1/2-q)*(m:ℝ) ≤ _ at bound
  change ENNReal.ofReal (1/2-ε) ≤ ((Rectangles.box (range (cubePlay (onImage E G) s) ∩ P) l u).card:ℝ≥0∞)/m
  change range (cubePlay (onImage E G) s) = E '' O at outputs
  rw [outputs,show P=E '' K from rfl,←Set.image_inter (GridTrace.injective inc)]
  have rat : (1/2-ε) ≤ ((Rectangles.box (E '' (O ∩ K)) l u).card:ℝ)/m := by
    apply (le_div_iff₀ pos).2
    nlinarith only [bound,fixed,mul_le_mul_of_nonneg_left vol qp.le,mul_le_mul_of_nonneg_right qe pos.le]
  simpa only [ENNReal.ofReal_div_of_pos pos,ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal rat

/-- A known product of arbitrarily stretched two-sided coordinate sequences
admits the near-half guarantee without any geometric volume filter. -/
theorem product_grid_generation (d : ℕ) (φ : Fin (d+1) → ℤ → ℤ) (inc : ∀ j, StrictMono (φ j))
    {ε : ℝ} (he : 0 < ε) :
    let P := range (GridTrace.encode φ)
    ∃ A : List (Lattice (d+1)) → Lattice (d+1), ∀ s : ℕ → Lattice (d+1), range s=P →
      cubeValid A s P ∧ ENNReal.ofReal (1/2-ε) ≤ Rectangles.lowerDensity (range (cubePlay A s)) P := by
  let key : ℕ ≃ Lattice (d+1) := Classical.choice (inferInstance : Nonempty (ℕ ≃ Lattice (d+1)))
  let C : LanguageFamily := fun _ => univ
  have full : key '' (Set.univ : Set ℕ) = Set.univ := by simp
  obtain ⟨A,ok⟩ := grid_generation key key.injective φ inc C (fun _ => Set.infinite_univ)
    singleton_rank_one he (show (0:ℝ) < 1 by norm_num)
  refine ⟨A,fun s pres => ?_⟩
  have h := ok 0 s
  simp only [C,full,Set.image_univ] at h
  obtain ⟨valid,dense⟩ := h pres
  exact ⟨valid,dense ⟨0,fun l u _ => by simp⟩⟩

end
end GenLimit.KleinbergWei.Banach
