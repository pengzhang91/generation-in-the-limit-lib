import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LatticeTransport
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.IntervalCounts
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredDensity

/-! Theorem 5.5 for every finite-rank family carried by one coordinatewise
monotone embedded sequence. Rectangles cut a chain in consecutive indices,
including when the rectangle is far from the origin or the chain is sparse. -/
namespace GenLimit.KleinbergWei.Banach
open Set Filter DensityMeasures
open scoped Classical ENNReal
noncomputable section

private theorem chain_trace {d} {e : ℕ → Lattice d} (inj : Function.Injective e)
    (mono : Monotone e) (l u : Lattice d) :
    ∃ a b : ℕ, ∀ S : Set ℕ, (Rectangles.box (e '' S) l u).card =
      ((Finset.Ico a b).filter (· ∈ S)).card := by
  let W := (Finset.Icc l u).preimage e inj.injOn
  have mem {x : ℕ} : x ∈ W ↔ l ≤ e x ∧ e x ≤ u := by simp [W]
  have interval : ∃ a b, W = Finset.Ico a b := by
    by_cases ne : W.Nonempty
    · let a := W.min' ne
      let b := W.max' ne
      refine ⟨a,b+1,Finset.ext fun x => ?_⟩
      rw [Finset.mem_Ico]
      constructor
      · intro h; exact ⟨W.min'_le _ h,Nat.lt_succ_of_le (W.le_max' _ h)⟩
      · rintro ⟨low,up⟩
        exact mem.mpr ⟨(mem.mp (W.min'_mem ne)).1.trans (mono low),
          (mono (Nat.le_of_lt_succ up)).trans (mem.mp (W.max'_mem ne)).2⟩
    · exact ⟨0,0,by simp [Finset.not_nonempty_iff_eq_empty.mp ne]⟩
  obtain ⟨a,b,eq⟩ := interval
  refine ⟨a,b,fun S => ?_⟩
  rw [←eq]; symm
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    obtain ⟨inside,h⟩ := Finset.mem_filter.mp hx
    exact Rectangles.mem_box.mpr ⟨mem.mp inside,x,h,rfl⟩
  · exact fun _ _ _ _ h => inj h
  · intro x hx
    obtain ⟨inside,n,hn,rfl⟩ := Rectangles.mem_box.mp hx
    exact ⟨n,Finset.mem_filter.mpr ⟨mem.mpr inside,hn⟩,rfl⟩

/-- A single finite-history strategy, independent of the test box, the
filter and the tolerance, achieves one half on every target on the chain. -/
theorem filtered_chain_generation {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (mono : Monotone e) (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧ ∀ f : ℕ → ℝ, Tendsto f atTop atTop →
      ENNReal.ofReal (1/2) ≤ filteredRectangularDensity f (range (cubePlay A s)) (e '' C z) := by
  let B := SpatialBins.build C inf
  let G := IntervalGenerator.rule rank B inf
  refine ⟨LatticeTransport.lift e G,fun z s pres => ?_⟩
  let t := Function.invFun e ∘ s
  obtain ⟨full,outputs,carries⟩ := LatticeTransport.run e inj pres G
  refine ⟨carries (IntervalGenerator.validity rank B inf full),?_⟩
  intro f grows
  let O := range (OrderedFocus.play G t)
  rw [outputs]
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have less : (r:ℝ) < 1/2 := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp hr
  obtain ⟨H,all⟩ := interval_counts inf rank B full (sub_pos.mpr less)
  obtain ⟨N,big⟩ := large_count_of_admissible (d := d) f grows (H+1)
  apply le_trans _ (le_iSup (fun n => ⨅ p : {p // admissibleBox f (e '' C z) n p},
    ((Rectangles.box ((e '' O) ∩ (e '' C z)) p.val.1 p.val.2).card:ℝ≥0∞)/
      (Rectangles.box (e '' C z) p.val.1 p.val.2).card) N)
  apply le_iInf
  rintro ⟨⟨l,u⟩,adm⟩
  obtain ⟨a,b,count⟩ := chain_trace inj mono l u
  let K := (Finset.Ico a b).filter (· ∈ C z)
  have large : H+1 ≤ K.card := by simpa only [count] using big _ _ adm
  have hits := all a b (Nat.le_succ H |>.trans large)
  have counted : (Rectangles.box ((e '' O) ∩ (e '' C z)) l u).card =
      (K.filter (· ∈ O)).card := by
    rw [←Set.image_inter inj,count]
    congr 1
    ext; simp [K]; tauto
  change (r:ℝ≥0∞) ≤ ((Rectangles.box ((e '' O) ∩ (e '' C z)) l u).card:ℝ≥0∞)/_
  rw [counted,count]
  have pos : (0:ℝ) < K.card := by exact_mod_cast (show 0 < K.card by omega)
  have rat : (r:ℝ) ≤ ((K.filter (· ∈ O)).card:ℝ)/K.card := by
    apply (le_div_iff₀ pos).2
    change (1/2-(1/2-(r:ℝ)))*(K.card:ℝ) ≤ ((K.filter (· ∈ O)).card:ℝ) at hits
    linarith
  simpa only [ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_div_of_pos pos,ENNReal.ofReal_natCast]
    using ENNReal.ofReal_le_ofReal rat

end
end GenLimit.KleinbergWei.Banach
