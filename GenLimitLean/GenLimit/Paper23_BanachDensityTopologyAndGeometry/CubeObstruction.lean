import GenLimit.Paper23_BanachDensityTopologyAndGeometry.DyadicEnumeration
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredObstruction
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.MovingCubes

/-! The moving-cube strengthening in the proof of P23 Corollary 5.4.
On a single presentation the periodic family misses filled lattice cubes
of every radius. A density-zero conclusion requires a nonempty volume
filter at arbitrarily high thresholds. -/
namespace GenLimit.KleinbergWei.Banach.CubeObstruction
open Set Finset Real Filter DyadicEnumeration MovingCubes
open scoped Classical ENNReal
noncomputable section

private def shifted {d} (l : Lattice d) (t : ℕ) : Lattice d := fun i => l i+2*(t:ℤ)

/-- One countable family forces whole, fully populated cubes to be missed.
The same injective target presentation works for every radius and filter. -/
theorem filled_cube_holes (d : ℕ) :
    ∃ C : Set (Set (Lattice (d+1))), C.Countable ∧ (∀ L ∈ C, L.Infinite) ∧
      ∃ K ∈ C, ∀ A : List (Lattice (d+1)) → Finset (Lattice (d+1)),
        (∀ L ∈ C, ∀ s : ℕ → Lattice (d+1), Set.range s = L → Function.Injective s →
          ∃ T, ∀ t ≥ T, ∀ x ∈ A (textPrefix s t), x ∈ L ∧ x ∉ textPrefix s t) →
        ∃ s : ℕ → Lattice (d+1), Set.range s = K ∧ Function.Injective s ∧
          ∀ t : ℕ, ∃ l : Lattice (d+1), ∀ x ∈ Finset.Icc l (fun i => l i+2*(t:ℤ)),
            x ∈ K ∧ ∀ j, x ∉ A (textPrefix s (j+1)) := by
  let e := point d
  obtain ⟨C,count,inf,mem,obstruction⟩ := FilteredObstruction.coded_holes e (point_injective d)
  let K := e '' Set.univ
  refine ⟨C,count,inf,K,mem,fun A valid => ?_⟩
  obtain ⟨s,pres,inj,T,holes⟩ := obstruction A valid
  refine ⟨s,pres,inj,fun t => ?_⟩
  let k := 2*t+1
  let B := (2^(d+1))^k
  have bp : 0 < B := by dsimp [B]; positivity
  obtain ⟨b,_,gap⟩ := holes (max T (2*B)) (le_max_left ..)
  let v := b/B+1
  have bot : b ≤ v*B := ((Nat.div_lt_iff_lt_mul bp).mp (Nat.lt_succ_self (b/B))).le
  have top : (v+1)*B ≤ b+max T (2*B) := by
    have h := Nat.div_mul_le_self b B
    have hm := le_max_right T (2*B)
    dsimp only [v]; rw [Nat.succ_mul,Nat.succ_mul]; omega
  let l := lower d v k
  refine ⟨l,fun x hx => ?_⟩
  have big : 2*t+1 ≤ 2^k := (Nat.lt_two_pow_self (n:=k)).le
  obtain ⟨xl,xu⟩ := Finset.mem_Icc.mp hx
  have inFull : x ∈ Finset.Icc (lower d v k) (upper d v k) := by
    refine Finset.mem_Icc.mpr ⟨xl,fun i => ?_⟩
    have high : x i ≤ l i+2*(t:ℤ) := xu i
    change x i ≤ l i+((2^k:ℕ):ℤ)-1
    omega
  rw [←block_image] at inFull
  obtain ⟨a,inside,rfl⟩ := Finset.mem_image.mp inFull
  have inBlock : a ∈ Finset.Ico (v*B) ((v+1)*B) := inside
  obtain ⟨al,au⟩ := Finset.mem_Ico.mp inBlock
  refine ⟨⟨a,Set.mem_univ _,rfl⟩,fun j hit => ?_⟩
  have yes : a ∈ (Finset.Ico b (b+max T (2*B))).filter
      (· ∈ e ⁻¹' {x | ∃ z, x ∈ A (textPrefix s (z+1))}) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨bot.trans al,au.trans_le top⟩,j,hit⟩
  exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨_,yes⟩)) gap

/-- Growth condition on the geometric volumes of integer-centered cubes. -/
def feasible (d : ℕ) (f : ℕ → ℝ) : Prop := ∀ n : ℕ, ∃ t : ℕ, 0 < t ∧
  let V := (2*t)^d
  2 ≤ V ∧ 0 < f V ∧ (n:ℝ) ≤ V/(f V*log V)

/-- Empty high-threshold families have infimum top. Therefore density
zero already forces arbitrarily high eligible cube ratios. -/
theorem necessary {d} (f : ℕ → ℝ) (K O : Set (Lattice d))
    (zero : filteredRectangularDensityOn IsCube f O K = 0) : feasible d f := by
  intro n
  let N := n*2^d
  have existsCube : Nonempty {r // admissibleBox f K N r ∧ IsCube r} := by
    by_contra! none
    letI := none
    have h := le_iSup (fun t => ⨅ r : {r // admissibleBox f K t r ∧ IsCube r},
      ((Rectangles.box (O ∩ K) r.val.1 r.val.2).card:ℝ≥0∞)/(Rectangles.box K r.val.1 r.val.2).card) N
    change _ ≤ filteredRectangularDensityOn IsCube f O K at h
    rw [iInf_of_empty,zero] at h
    exact ENNReal.top_ne_zero (le_antisymm h bot_le)
  obtain ⟨⟨R,adm,z,t,tp,lo,hi⟩⟩ := existsCube
  have vol : geometricVolume R.1 R.2 = (2*t)^d := by
    have each (i) : (R.2 i-R.1 i).toNat = 2*t := by rw [lo,hi]; omega
    simp only [geometricVolume,each,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  obtain ⟨w,big,pos,ratio⟩ := adm
  rw [vol] at big pos ratio
  let V := (2*t)^d
  refine ⟨t,tp,big,pos,?_⟩
  have den : 0 < f V*log V := mul_pos pos (Real.log_pos (by exact_mod_cast (show 1 < V from big)))
  have cap := card_le_geometricVolume K w
  rw [vol] at cap
  have cap' : ((Rectangles.box K R.1 R.2).card:ℝ) ≤ (2:ℝ)^d*V := by exact_mod_cast cap
  have hits := (le_div_iff₀ den).mp ratio
  change ((n*2^d:ℕ):ℝ)*(f V*log V) ≤ _ at hits
  push_cast at hits
  apply (le_div_iff₀ den).mpr
  apply le_of_mul_le_mul_left (a:=(2:ℝ)^d) _ (by positivity)
  linarith only [hits.trans cap']

/-- For a nondecreasing divergent filter, passing to the volumes of
even-sided cubes preserves unbounded eligibility. -/
theorem of_rectangular_feasible {d} (hd : 0 < d) {f : ℕ → ℝ}
    (mono : Monotone f) (grows : Tendsto f atTop atTop) (rect : FilteredObstruction.feasible f) :
    feasible d f := by
  let F (t : ℕ) := (2*t)^d
  have strict : StrictMono F := fun _ _ h => Nat.pow_lt_pow_left (by omega) hd.ne'
  obtain ⟨k,hk⟩ := eventually_atTop.mp ((tendsto_atTop.mp grows) 1)
  intro n
  let N := max (n*2^d) (2^d*(k+1))
  obtain ⟨V,big,large,pos,ratio⟩ := rect N
  have existsLarger : ∃ a, V < F a := ⟨V+1,(Nat.lt_succ_self V).trans_le (strict.id_le _)⟩
  let a := Nat.find existsLarger
  have upper : V < F a := Nat.find_spec existsLarger
  have unit : F 1 ≤ V := by
    have h := (le_max_right (n*2^d) (2^d*(k+1))).trans large
    simpa [F] using (Nat.le_mul_of_pos_right (2^d) (Nat.succ_pos k)).trans h
  have a2 : 1 < a := strict.lt_iff_lt.mp (unit.trans_lt upper)
  let t := a-1
  have tp : 0 < t := by dsimp [t]; omega
  have prev : t < a := by dsimp [t]; omega
  have Wle : F t ≤ V := le_of_not_gt (Nat.find_min existsLarger prev)
  have bound : V < 2^d * F t := by
    apply upper.trans_le
    change (2*a)^d ≤ 2^d*(2*t)^d
    rw [←mul_pow]
    exact Nat.pow_le_pow_left (by dsimp [t]; omega) d
  have Wlarge : k ≤ F t := by
    have kV := (le_max_right (n*2^d) (2^d*(k+1))).trans large
    exact (Nat.le_succ k).trans ((Nat.le_of_mul_le_mul_left (kV.trans bound.le) (by positivity)))
  have Wbig : 2 ≤ F t := (show 2 ≤ 2*t by omega).trans (Nat.le_self_pow hd.ne' _)
  have positive : 0 < f (F t) := zero_lt_one.trans_le (hk _ Wlarge)
  refine ⟨t,tp,Wbig,positive,?_⟩
  have wp : (0:ℝ) < F t := by exact_mod_cast (show 0 < F t by omega)
  have lg : 0 < log (F t) := Real.log_pos (by exact_mod_cast (show 1 < F t from Wbig))
  have den := mul_pos positive lg
  have denV : 0 < f V*log V := mul_pos pos (Real.log_pos (by exact_mod_cast (show 1 < V from big)))
  have cheap : f (F t)*log (F t) ≤ f V*log V :=
    mul_le_mul (mono Wle) (Real.log_le_log wp (by exact_mod_cast Wle)) lg.le pos.le
  have test : (n:ℝ)*(2:ℝ)^d ≤ N := by exact_mod_cast le_max_left (n*2^d) (2^d*(k+1))
  have mass := (le_div_iff₀ denV).mp (test.trans ratio)
  have upper' : (V:ℝ) ≤ (2:ℝ)^d * F t := by exact_mod_cast bound.le
  apply (le_div_iff₀ den).mpr
  apply le_of_mul_le_mul_left (a:=(2:ℝ)^d) _ (by positivity)
  have h := mul_le_mul_of_nonneg_left cheap (show 0 ≤ (n:ℝ)*2^d by positivity)
  linarith only [h.trans (mass.trans upper')]

/-- The published cube obstruction holds for every filter feasible on
cubes, even when each round may return any finite batch. -/
theorem sufficient (d : ℕ) :
    ∃ C : Set (Set (Lattice (d+1))), C.Countable ∧ (∀ L ∈ C, L.Infinite) ∧
      ∃ K ∈ C, ∀ A : List (Lattice (d+1)) → Finset (Lattice (d+1)),
        (∀ L ∈ C, ∀ s : ℕ → Lattice (d+1), Set.range s = L → Function.Injective s →
          ∃ T, ∀ t ≥ T, ∀ x ∈ A (textPrefix s t), x ∈ L ∧ x ∉ textPrefix s t) →
        ∃ s : ℕ → Lattice (d+1), Set.range s = K ∧ Function.Injective s ∧ ∀ f, feasible (d+1) f →
          filteredRectangularDensityOn IsCube f {x | ∃ j, x ∈ A (textPrefix s (j+1))} K = 0 := by
  obtain ⟨C,count,inf,K,mem,obstruction⟩ := filled_cube_holes d
  refine ⟨C,count,inf,K,mem,fun A valid => ?_⟩
  obtain ⟨s,pres,inj,holes⟩ := obstruction A valid
  refine ⟨s,pres,inj,fun f growth => le_antisymm ?_ bot_le⟩
  apply iSup_le; intro n
  obtain ⟨t,tp,big,pos,ratio⟩ := growth n
  obtain ⟨l,miss⟩ := holes t
  let u := shifted l t
  let V := (2*t)^(d+1)
  have vol : geometricVolume l u = V := by
    have each (i) : (u i-l i).toNat = 2*t := by dsimp [u,shifted]; omega
    simp only [geometricVolume,each,Finset.prod_const,Finset.card_univ,Fintype.card_fin,V]
  have full : Rectangles.box K l u = Finset.Icc l u := Finset.filter_true_of_mem (fun x hx => (miss x hx).1)
  have enough : V ≤ (Rectangles.box K l u).card := by
    rw [full,Pi.card_Icc]
    change (2*t)^(d+1) ≤ _
    rw [← show ∏ _ : Fin (d+1), 2*t = (2*t)^(d+1) by simp]
    apply Finset.prod_le_prod'
    intro i _; rw [Int.card_Icc]; dsimp [u,shifted]; omega
  have width (i) : l i < u i := by dsimp [u,shifted]; omega
  have den : 0 < f V*log V := mul_pos pos (Real.log_pos (by exact_mod_cast (show 1 < V from big)))
  have adm : admissibleBox f K n (l,u) := by
    refine ⟨width,vol ▸ big,vol ▸ pos,?_⟩
    change (n:ℝ) ≤ _/(f (geometricVolume l u)*log (geometricVolume l u))
    rw [vol]
    exact ratio.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr enough) den.le)
  have shape : IsCube (l,u) := ⟨fun i => l i+t,t,tp,fun i => by simp,fun i => by dsimp [u,shifted]; omega⟩
  apply (iInf_le _ ⟨(l,u),adm,shape⟩).trans
  have empty : Rectangles.box ({x | ∃ j, x ∈ A (textPrefix s (j+1))} ∩ K) l u = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx; obtain ⟨inside,⟨j,hit⟩,_⟩ := Rectangles.mem_box.mp hx
    exact (miss x (Finset.mem_Icc.mpr inside)).2 j hit
  change ((Rectangles.box _ l u).card:ℝ≥0∞)/_ ≤ 0
  rw [empty]; simp

end
end GenLimit.KleinbergWei.Banach.CubeObstruction
