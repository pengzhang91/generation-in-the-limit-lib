import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FixedShapeDensity
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.MovingCubes
import BanachDensityHD.FiniteRank

/-! P23 Theorem 5.5 for positive logarithmic powers and the generation part
of Corollary 5.7. The imported finite-rank theorem comes from Kleinberg and
Wei's later paper *Characterizing Local Breadth in Language Generation*.
Run `scripts/check_p23_power_filter.py` with their pinned source checkout. -/
namespace GenLimit.KleinbergWei.Banach.FixedShape.SourceBridge
open Set Filter Real BanachDensityHD
open scoped Classical ENNReal
noncomputable section

private def rect {d} (Q : Box d) (wide : ∀ i, Q.1 i < Q.2 i) : Rect d :=
  .mk Q.1 Q.2 (fun i => (wide i).le)

private theorem points {d} (Q : Box d) (wide : ∀ i, Q.1 i < Q.2 i) :
    (rect Q wide).pts = (Finset.Icc Q.1 Q.2 : Finset (Lattice d)) := by
  ext; simp [rect,Rect.pts,Rect.lo,Rect.hi]

private theorem mass_eq {d} (K : Set (Lattice d)) (Q : Box d) (wide : ∀ i, Q.1 i < Q.2 i) :
    mass K (rect Q wide) = (Rectangles.box K Q.1 Q.2).card := by
  have eq : K ∩ (rect Q wide).pts = (Rectangles.box K Q.1 Q.2 : Finset (Lattice d)) := by
    ext; simp [points]; tauto
  rw [mass,eq,Set.ncard_coe_finset]

/-- Lower bounds in the authors' lattice-site normalization imply the
P23 rectangular lower bound whenever the source filter dominates a fixed
positive power of the logarithm. -/
theorem of_deltaH_power {d} (K O : Set (Lattice d)) (f : ℕ → ℝ) {τ B : ℝ}
    (ht : 0 ≤ τ) (dominates : ∀ᶠ V : ℕ in atTop, (log V)^τ ≤ B*f V) :
    ENNReal.ofReal (deltaH (hTau τ) O K) ≤ filteredRectangularDensity f O K := by
  apply rectangular_of_site_power_tests O K f ht dominates
  intro b _ less
  have pos {n : ℕ} (_hn : 1 ≤ n) : 0 < hTau τ n := by
    apply Real.rpow_pos_of_pos
    apply Real.log_pos
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have lim := (deltaH_tendsto (hTau τ) (fun _ hn => pos hn) O K).1
  obtain ⟨v,hv⟩ := eventually_atTop.mp (lim.eventually (lt_mem_nhds less))
  let c := max v 1
  refine ⟨c,zero_lt_one.trans_le (le_max_right ..),fun Q w heavy => ?_⟩
  let L := rect Q w
  let h := hTau τ
  have sites : (rect Q w).vol = (Finset.Icc Q.1 Q.2).card := by rw [Rect.vol,points,Set.ncard_coe_finset]
  have threshold : h L.vol = (LogPowerCriterion.logSites Q)^(1+τ) := by
    change (log (2+((rect Q w).vol:ℝ)))^(1+τ) = _
    rw [sites]; rfl
  have member : ((mass (O ∩ K) L:ℝ)/mass K L) ∈ BasicAux.tests h O K c :=
    ⟨L,by rw [threshold,mass_eq]; exact heavy,rfl⟩
  have bound := (hv c (le_max_left ..)).le
  rw [BasicAux.testInf_eq,if_pos (show (BasicAux.tests h O K c).Nonempty from ⟨_,member⟩)] at bound
  have rat := bound.trans (csInf_le (BasicAux.tests_bdd ..) member)
  simpa only [L,mass_eq] using rat

private def lifted {d} (e : ℕ → Lattice d) (C : LanguageFamily) := range (fun z => e '' C z)

private def carry {d} (e : ℕ → Lattice d) (C : LanguageFamily) (x : TowerTopology.Point (range C)) :
    lifted e C := ⟨e '' x.val,by obtain ⟨z,hz⟩ := x.property; exact ⟨z,congrArg (fun S => e '' S) hz⟩⟩

private theorem carry_surjective {d} (e : ℕ → Lattice d) (C : LanguageFamily) :
    Function.Surjective (carry e C) := by
  rintro ⟨_,⟨z,rfl⟩⟩
  exact ⟨⟨C z,mem_range_self z⟩,rfl⟩

private theorem rank_transport {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) (n : ℕ) (x : TowerTopology.Point (range C))
    (mem : carry e C x ∈ cbDerived (lifted e C) n) : x ∈ TowerTopology.cbDerivative (range C) n := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih _ mem.1,fun F inside => ?_⟩
    by_contra no
    let X := lifted e C
    let E := e '' (F : Set ℕ)
    let U := evidenceSet X (e '' x.val) E
    have isopen : (evidenceTopology X).IsOpen U := TopologicalSpace.GenerateOpen.basic _ ⟨e '' x.val,
      (carry e C x).property,E,F.finite_toSet.image _,Set.image_mono inside,rfl⟩
    apply mem.2
    refine ⟨U,isopen,Set.ext fun y => ?_⟩
    constructor
    · rintro ⟨belongs,old⟩
      obtain ⟨p,rfl⟩ := carry_surjective e C y
      have h1 : E ⊆ e '' p.val := belongs.1
      have h2 : e '' p.val ⊆ e '' x.val := belongs.2
      have cand : p ∈ TowerTopology.basicNeighborhood (range C) x F :=
        ⟨(Set.image_subset_image_iff inj).mp h1,(Set.image_subset_image_iff inj).mp h2⟩
      by_cases eq : p = x
      · subst p; exact Set.mem_singleton _
      · exact (no ⟨p,ih p old,eq,cand⟩).elim
    · rintro (rfl : y = carry e C x)
      exact ⟨⟨Set.image_mono inside,Subset.rfl⟩,mem.1⟩

private theorem finite_rank {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) {n : ℕ} (bound : TowerTopology.FiniteRankAtMost (range C) n) :
    FiniteCBRank (lifted e C) := by
  refine ⟨n,Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro y
  obtain ⟨x,rfl⟩ := carry_surjective e C y
  intro old
  have bad := rank_transport e inj C n x old
  rw [show TowerTopology.cbDerivative (range C) n = ∅ from bound] at bad
  exact bad

private theorem prefix_eq {d} (s : ℕ → Lattice d) (t : ℕ) : inputsUpTo s t = textPrefix s (t+1) := by
  apply List.ext_getElem
  · simp [inputsUpTo,textPrefix]
  · intro i h1 h2
    simp only [inputsUpTo,List.getElem_ofFn,textPrefix,List.getElem_map,List.getElem_range]

private theorem valid_run {d} {G : Generator (Pt d)} {X : Set (Set (Pt d))}
    (valid : G ∈ ValidGen X) {K : Set (Pt d)} (inX : K ∈ X) {s : ℕ → Pt d} (full : range s = K) :
    cubeValid G s K ∧ G.outputSet s = range (cubePlay G s) := by
  have play (t : ℕ) : G.out s t = cubePlay G s t := by simp only [Generator.out,cubePlay,prefix_eq]
  refine ⟨?_,by simp only [Generator.outputSet,show G.out s = cubePlay G s from funext play]⟩
  have finite := valid.2 K inX s full
  obtain ⟨T,after⟩ := finite.bddAbove
  refine ⟨T+1,fun t ht => ?_⟩
  rw [←play]
  have member : G.out s t ∈ K := by
    by_contra bad
    have bound := after (show t ∈ {t | G.out s t ∉ K} from bad)
    omega
  obtain ⟨inputs,outputs⟩ := valid.1 s t
  exact ⟨member,inputs,fun i hi => (play i) ▸ outputs i hi⟩

private theorem vacuous_density {d} (τ : ℝ) (K O : Set (Pt d))
    (hv : ¬ Nonvacuous (hTau τ) K) : deltaH (hTau τ) O K = 1 := by
  have bounded : BddAbove (range fun R : Rect d => (mass K R : ℝ) / hTau τ R.vol) := not_not.mp hv
  obtain ⟨cap, bounds⟩ := bounded
  have pos (n : ℕ) : 0 < hTau τ n := Real.rpow_pos_of_pos (Real.log_pos (by linarith [Nat.cast_nonneg (α:=ℝ) n])) _
  apply tendsto_nhds_unique (deltaH_tendsto _ (fun n _ => pos n) O K).1
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop cap] with c hc
  rw [BasicAux.testInf_eq,if_neg]
  rintro ⟨_,R,eligible,_⟩
  exact hc.not_ge (((le_div_iff₀ (pos _)).mpr eligible).trans (bounds (mem_range_self R)))

private theorem transfer_generation {d} (e : ℕ → Lattice d)
    (C : LanguageFamily) {τ q ε : ℝ} (ht : 0 < τ) (qe : q ≤ ε) (qp : 0 < q)
    (points_rank : ∀ z, ∃ r, PointRank (lifted e C) (e '' C z) r)
    (source : ∃ G ∈ ValidGen (lifted e C), ∀ K ∈ lifted e C, Nonvacuous (hTau τ) K →
      (∃ r, PointRank (lifted e C) K r) → Guarantees (dH (hTau τ)) G K (1/2-q)) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z s, range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ∀ (f : ℕ → ℝ) (B : ℝ),
        (∀ᶠ V : ℕ in atTop, (log V)^τ ≤ B*f V) →
        ENNReal.ofReal (1/2-ε) ≤ filteredRectangularDensity f (range (cubePlay G s)) (e '' C z) := by
  obtain ⟨G,valid,guarantee⟩ := source
  refine ⟨G,fun z s full => ?_⟩
  have member : e '' C z ∈ lifted e C := mem_range_self z
  obtain ⟨success,outputs⟩ := valid_run valid member full
  refine ⟨success,fun f B dom => ?_⟩
  rw [←outputs]
  apply le_trans _ (of_deltaH_power (e '' C z) (G.outputSet s) f ht.le dom)
  apply ENNReal.ofReal_le_ofReal
  by_cases nv : Nonvacuous (hTau τ) (e '' C z)
  · have bound := EReal.coe_le_coe_iff.mp (guarantee _ member nv (points_rank z) s full)
    exact (sub_le_sub_left qe _).trans bound
  · rw [vacuous_density _ _ _ nv]
    linarith

private theorem generation_in_higher_dimension {d} (hd : 2 ≤ d)
    (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {n : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) n) {τ ε : ℝ} (ht : 0 < τ) (he : 0 < ε) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z s, range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ∀ (f : ℕ → ℝ) (B : ℝ),
        (∀ᶠ V : ℕ in atTop, (log V)^τ ≤ B*f V) →
        ENNReal.ofReal (1/2-ε) ≤ filteredRectangularDensity f (range (cubePlay G s)) (e '' C z) := by
  let q := min (ε/2) (1/4)
  have qp : 0 < q := lt_min (by linarith) (by norm_num)
  have qe : q ≤ ε := (min_le_left ..).trans (by linarith)
  have small : q < 1/2 := lt_of_le_of_lt (min_le_right ..) (by norm_num)
  have family : LangClass (lifted e C) :=
    ⟨⟨_,mem_range_self 0⟩,Set.countable_range _,by
      rintro _ ⟨z,rfl⟩
      exact (inf z).image inj.injOn⟩
  apply transfer_generation e C ht qe qp
  · exact fun z => finiteCBRank_pointRank (finite_rank e inj C rank) (mem_range_self z)
  · exact thm_finite_rank_near_half hd family ht qp small

/-- Theorem 5.5 for all filters eventually dominating a fixed positive
power of the logarithm. One generator handles all translations, rectangle
shapes, targets, full presentations, and such filters simultaneously. -/
theorem finite_rank_generation_power {d} (hd : 0 < d) (e : ℕ → Lattice d)
    (inj : Function.Injective e) (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {n : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) n)
    {τ ε : ℝ} (ht : 0 < τ) (he : 0 < ε) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z s, range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ∀ (f : ℕ → ℝ) (B : ℝ),
        (∀ᶠ V : ℕ in atTop, (log V)^τ ≤ B*f V) →
        ENNReal.ofReal (1/2-ε) ≤ filteredRectangularDensity f (range (cubePlay G s)) (e '' C z) := by
  obtain ⟨A,works⟩ := generation_in_higher_dimension (d:=d+d) (by omega)
    (MovingCubes.diagonal ∘ e) ((MovingCubes.diagonal_injective d).comp inj) C inf rank ht he
  apply MovingCubes.descend_generation_power hd (fun z => e '' C z) ht.le A
  simpa only [Set.image_comp] using works

/-- The moving-cube guarantee of Corollary 5.6 under the same logarithmic
power hypothesis as the rectangular generation theorem. -/
theorem corollary_5_6_power {d} (hd : 0 < d) (e : ℕ → Lattice d)
    (inj : Function.Injective e) (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {n : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) n)
    {τ ε : ℝ} (ht : 0 < τ) (he : 0 < ε) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z s, range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ∀ (f : ℕ → ℝ) (B : ℝ),
        (∀ᶠ V : ℕ in atTop, (log V)^τ ≤ B*f V) →
        ENNReal.ofReal (1/2-ε) ≤
          filteredRectangularDensityOn MovingCubes.IsCube f (range (cubePlay G s)) (e '' C z) := by
  obtain ⟨G,works⟩ := finite_rank_generation_power hd e inj C inf rank ht he
  refine ⟨G,fun z s full => ?_⟩
  obtain ⟨valid,lower⟩ := works z s full
  refine ⟨valid,fun f B dom => (lower f B dom).trans ?_⟩
  rw [←filteredDensityOn_all]
  exact filteredDensityOn_mono_eventually _ _ _ _ _ 0 (fun _ _ _ => trivial)

/-- The generation and density conclusion of Corollary 5.7 for every
finite-rank family. One generator works for all templates in equation (19),
including templates with degenerate sides. -/
theorem corollary_5_7_generation {d} (hd : 0 < d) (e : ℕ → Lattice d)
    (inj : Function.Injective e) (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {n : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) n) {ε : ℝ} (he : 0 < ε) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z s, range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ∀ R : Box d,
        ENNReal.ofReal (1/2-ε) ≤ density R (range (cubePlay G s)) (e '' C z) := by
  obtain ⟨A,works⟩ := generation_in_higher_dimension (d:=d+d) (by omega)
    (MovingCubes.diagonal ∘ e) ((MovingCubes.diagonal_injective d).comp inj) C inf rank (τ:=1) zero_lt_one he
  refine ⟨MovingCubes.decode A,fun z s full => ?_⟩
  have full' : range (MovingCubes.diagonal ∘ s) = (MovingCubes.diagonal ∘ e) '' C z := by
    rw [Set.range_comp,full,Set.image_comp]
  obtain ⟨valid,lower⟩ := works z _ full'
  simp only [Set.image_comp] at valid lower
  obtain ⟨ok,captured⟩ := MovingCubes.decoded_run A s (e '' C z) valid
  refine ⟨ok,fun R => ?_⟩
  have rect := lower (fun V => log V) 1 (Eventually.of_forall fun V => by simp)
  exact rect.trans ((of_rectangular (by omega) (liftShape R) (liftShape_wide R) _ _).trans
    (diagonal_density R _ _ _ captured))

end
end GenLimit.KleinbergWei.Banach.FixedShape.SourceBridge

open Lean in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``GenLimit.KleinbergWei.Banach.FixedShape.SourceBridge.finite_rank_generation_power,
      ``GenLimit.KleinbergWei.Banach.FixedShape.SourceBridge.corollary_5_6_power,
      ``GenLimit.KleinbergWei.Banach.FixedShape.SourceBridge.corollary_5_7_generation] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => allowed.contains ax) do
      throwError m!"{name} depends on unexpected axioms {axioms}"
    logInfo m!"{name} depends on {axioms}"
