import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RegionRectangles
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! A single filter-independent generator with a logarithmic loss in the
distance of the query from the origin. The spatial shells have radii that
square at each step, so the sum of their log populations is itself logarithmic. -/
namespace GenLimit.KleinbergWei.Banach.RadialCounts
open Finset Set Filter Real BoardPermutations RegionGame FilterShells
open scoped Classical ENNReal
noncomputable section

def outerRadius {d} (r : Lattice d × Lattice d) := max (radius r.1) (radius r.2)

private def bits (r : ℕ) := Nat.log 2 (r+1) + 1
private def level (r : ℕ) := Nat.log 2 (bits r)
private def edge (k : ℕ) : ℕ := 2^(2^(k+1))

private theorem radius_le_edge (r : ℕ) : r ≤ edge (level r) := by
  have near := Nat.lt_pow_succ_log_self (b:=2) (by decide) (r+1)
  have far := Nat.lt_pow_succ_log_self (b:=2) (by decide) (bits r)
  exact (Nat.le_succ r).trans (near.le.trans (Nat.pow_le_pow_right (by decide) far.le))

private theorem level_mono : Monotone level :=
  fun _ _ le => Nat.log_mono_right (Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right le 1)) 1)

private theorem in_cube {d} {x : Lattice d} {r : ℕ} (le : radius x ≤ r) :
    x ∈ centeredCube d r := by
  have each (i : Fin d) : (x i).natAbs ≤ r :=
    (Finset.le_sup (f:=fun j => (x j).natAbs) (Finset.mem_univ i)).trans le
  exact Finset.mem_Icc.mpr ⟨fun i => by have := each i; dsimp; omega,
    fun i => by have := each i; dsimp; omega⟩

private theorem inside {d} {l u x : Lattice d} (member : x ∈ Finset.Icc l u) :
    radius x ≤ outerRadius (l,u) := by
  obtain ⟨left,right⟩ := Finset.mem_Icc.mp member
  have a := Finset.mem_Icc.mp (in_cube (x:=l) (le_max_left (radius l) (radius u)))
  have b := Finset.mem_Icc.mp (in_cube (x:=u) (le_max_right (radius l) (radius u)))
  apply Finset.sup_le
  intro i _
  have lo : -((outerRadius (l,u):ℕ):ℤ) ≤ x i := (a.1 i).trans (left i)
  have hi : x i ≤ ((outerRadius (l,u):ℕ):ℤ) := (right i).trans (b.2 i)
  omega

private def cells {d} (e : ℕ → Lattice d) (inj : Function.Injective e) : ForestGames.Cells ℕ where
  address x := level (radius (e x))
  bin k := ((centeredCube d (edge k)).preimage e inj.injOn).filter fun x => level (radius (e x)) = k

private theorem mem_cell {d} {e : ℕ → Lattice d} (inj : Function.Injective e) {x k} :
    x ∈ (cells e inj).bin k ↔ (cells e inj).address x = k := by
  refine ⟨fun hx => (Finset.mem_filter.mp hx).2,?_⟩
  intro eq
  exact Finset.mem_filter.mpr ⟨Finset.mem_preimage.mpr (in_cube (eq ▸ radius_le_edge _)),eq⟩

private theorem population {d} {e : ℕ → Lattice d} (inj : Function.Injective e)
    {k : ℕ} {D : Finset ℕ} (sub : D ⊆ (cells e inj).bin k) :
    D.card ≤ 2^((2^(k+1)+2)*d) := by
  let t := edge k
  have contained : D ⊆ (centeredCube d t).preimage e inj.injOn :=
    sub.trans (Finset.filter_subset ..)
  have size := Finset.card_le_card contained
  rw [Finset.card_preimage] at size
  have cap : D.card ≤ (centeredCube d t).card := size.trans (Finset.card_filter_le ..)
  have cube : (centeredCube d t).card = (2*t+1)^d := by
    simp only [centeredCube,Pi.card_Icc,Int.card_Icc]
    have side : ((t:ℤ)+1-(-(t:ℤ))).toNat = 2*t+1 := by omega
    simp only [side,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [cube] at cap
  have positive : 1 ≤ t := Nat.one_le_two_pow
  have width : 2*t+1 ≤ 2^(2^(k+1)+2) := by
    rw [pow_add]
    change 2*t+1 ≤ t*4
    omega
  exact cap.trans ((Nat.pow_le_pow_left width d).trans_eq (pow_mul ..).symm)

private def coefficient (d : ℕ) (q : ℝ) := (2+8*(d:ℝ)^2)*log 2/(2*q)

private theorem loss_bound {d k : ℕ} {q : ℝ} (hq : 0 < q) (small : q ≤ 1/2)
    {n : ℕ} (size : n ≤ 2^((2^(k+1)+2)*d)) :
    log ((1+q)*(1+(n:ℝ)^(2*d)))/(2*q) ≤ coefficient d q * (2:ℝ)^k := by
  let M := ((2^(k+1)+2)*d)*(2*d)
  have p : n^(2*d) ≤ 2^M := (Nat.pow_le_pow_left size _).trans_eq (pow_mul ..).symm
  have big : (1:ℝ) ≤ 2^M := one_le_pow₀ (by norm_num)
  have nr : (n:ℝ)^(2*d) ≤ 2^M := by exact_mod_cast p
  have positive : 0 < (1+q)*(1+(n:ℝ)^(2*d)) :=
    mul_pos (by linarith) (by positivity)
  have bound : (1+q)*(1+(n:ℝ)^(2*d)) ≤ (2:ℝ)^(M+2) := by
    rw [pow_add]; norm_num
    nlinarith [mul_le_mul_of_nonneg_right (show 1+q ≤ 2 by linarith)
      (show 0 ≤ 1+(n:ℝ)^(2*d) by positivity)]
  have logs := Real.log_le_log positive bound
  rw [Real.log_pow] at logs
  have cap : ((M+2:ℕ):ℝ) ≤ (2+8*(d:ℝ)^2)*(2:ℝ)^k := by
    dsimp [M]; push_cast; rw [pow_succ]
    have one : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right one (sq_nonneg (d:ℝ))]
  unfold coefficient
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ _ := logs
    _ ≤ _ := mul_le_mul_of_nonneg_right cap (log_nonneg (by norm_num))
    _ = _ := by ring

/-- For every rectangle around any location, its deficit has a logarithmic
bound in its outer radius. The same generator and coefficient work for all
rectangles and all filters. Only the finite startup cost depends on the text. -/
theorem logarithmic_radius_error {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 < q) (small : q ≤ 1/2) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ G : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d),
      range s = e '' C z → cubeValid G s (e '' C z) ∧ ∃ H : ℕ, ∀ l u : Lattice d,
      (1/2-q)*((Rectangles.box (e '' C z) l u).card:ℝ) ≤
        (Rectangles.box (range (cubePlay G s) ∩ (e '' C z)) l u).card +
        B*(1+log (1+(outerRadius (l,u):ℝ)))+H := by
  let coeff := coefficient d q
  have lp : 0 < log 2 := log_pos (by norm_num)
  have coeffpos : 0 ≤ coeff := by dsimp [coeff,coefficient]; positivity
  let B := (R:ℝ)*coeff*2/log 2
  have Bn : 0 ≤ B := by dsimp [B]; positivity
  choose move safe win using fun D => (ClaimGame.canForce_iff_covering ..).mp (population_bound e D hq small)
  obtain ⟨G,plays⟩ := cell_counts_of_board_moves e inj hq.le (cells e inj) (fun {_ _} => mem_cell inj)
    C inf rank move safe
  refine ⟨B,Bn,G,fun z s pres => ?_⟩
  obtain ⟨valid,H,counts⟩ := plays z s pres
  refine ⟨valid,H,fun l u => ?_⟩
  let r := outerRadius (l,u)
  let j := level r
  let J := Finset.range (j+1)
  let loss (k : ℕ) := coeff * (2:ℝ)^k
  have bound := counts l u J (fun _ hx => Finset.mem_range.mpr
    (Nat.lt_succ_of_le (level_mono (inside hx)))) loss (fun _ => by dsimp [loss]; positivity) (by
    intro k _ D sub _ t n covered
    let X := boardTrace e D (l,u)
    have result := win D (textPrefix t n) covered (l,u)
    have localCap := loss_bound hq small (population inj sub)
    have eq : X.filter (· ∈ earned (move D) (textPrefix t n)) =
        X.filter (fun y => ∃ h < n, move D (textPrefix t h) (t h) = some y) := by
      ext; simp only [mem_filter,earned_prefix]
    change (1/2-q)*(X.card:ℝ)-loss k ≤
      ((X.filter (fun y => ∃ h < n, move D (textPrefix t h) (t h) = some y)).card:ℝ)
    rw [←eq]
    exact (sub_le_sub_left localCap _).trans result)
  have sumGeom (m : ℕ) : ∑ k ∈ Finset.range m, (2:ℝ)^k = 2^m-1 := by
    induction m with
    | zero => simp
    | succ _ ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  have geom : (∑ k ∈ J, (R:ℝ)*loss k) ≤ (R:ℝ)*coeff*2*(bits r:ℝ) := by
    have bitCap : (2:ℝ)^j ≤ bits r := by
      exact_mod_cast Nat.pow_log_le_self 2 (show bits r ≠ 0 by simp [bits])
    simp only [J,loss,←mul_assoc,←Finset.mul_sum,sumGeom,pow_succ]
    apply (mul_le_mul_of_nonneg_left (show 2^j*2-1 ≤ 2*(bits r:ℝ) by linarith)
      (show 0 ≤ (R:ℝ)*coeff by positivity)).trans_eq
    ring
  have bitLog : (bits r:ℝ)*log 2 ≤ 1+log (1+(r:ℝ)) := by
    have lower := Nat.pow_log_le_self 2 (show r+1 ≠ 0 by omega)
    have lower' : (2:ℝ)^(Nat.log 2 (r+1)) ≤ 1+r := by
      calc
        _ ≤ (r:ℝ)+1 := by exact_mod_cast lower
        _ = 1+r := add_comm ..
    have logBound := Real.log_le_log (by positivity) lower'
    rw [Real.log_pow] at logBound
    dsimp [bits]; push_cast
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))]
  have finalCost : (R:ℝ)*coeff*2*(bits r:ℝ) ≤ B*(1+log (1+(r:ℝ))) := by
    dsimp [B]; rw [div_mul_eq_mul_div,le_div_iff₀ lp]
    nlinarith only [mul_le_mul_of_nonneg_left bitLog (show 0 ≤ (R:ℝ)*coeff*2 by positivity)]
  exact bound.trans (add_le_add_right (add_le_add_left (geom.trans finalCost) _) _)

/-- The outer radius may grow as fast as a fixed power of V raised to f(V),
where V is the geometric volume used in the source filter. -/
def positionTest {d} (f : ℕ → ℝ) (T : ℝ) (r : Lattice d × Lattice d) : Prop :=
  let V := geometricVolume r.1 r.2
  1+log (1+(outerRadius r:ℝ)) ≤ T*(f V*log V)

/-- The same generator works for every source filter and every fixed
position allowance. Rectangles may move arbitrarily far from every fixed
point. Their permitted distance increases with their own geometric volume. -/
theorem filtered_generation_with_position_bound {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 < q) (small : q ≤ 1/2) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ∀ f : ℕ → ℝ, Tendsto f atTop atTop → ∀ T : ℝ,
        ENNReal.ofReal (1/2-q) ≤ filteredRectangularDensityOn (positionTest f T) f
          (range (cubePlay G s)) (e '' C z) := by
  obtain ⟨B,bn,G,works⟩ := logarithmic_radius_error e inj hq small C inf rank
  refine ⟨G,fun z s pres => ?_⟩
  obtain ⟨valid,H,counts⟩ := works z s pres
  refine ⟨valid,fun f grows T => ?_⟩
  let P := e '' C z
  let O := range (cubePlay G s)
  apply ENNReal.le_of_forall_nnreal_lt
  intro a ha
  have gap : (a:ℝ) < 1/2-q := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp ha
  let δ : ℝ := (1/2-q-a)/2
  have dp : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨n,hn⟩ := exists_nat_gt (B*T/δ)
  obtain ⟨h,hh⟩ := exists_nat_gt ((H:ℝ)/δ)
  obtain ⟨M,large⟩ := large_count_of_admissible (d:=d) f grows (h+1)
  apply le_trans _ (le_iSup (fun k => ⨅ r : {r // admissibleBox f P k r ∧ positionTest f T r},
    ((Rectangles.box (O ∩ P) r.val.1 r.val.2).card:ℝ≥0∞)/(Rectangles.box P r.val.1 r.val.2).card) (max n M))
  apply le_iInf
  rintro ⟨⟨l,u⟩,adm,tested⟩
  let V := geometricVolume l u
  let m : ℝ := (Rectangles.box P l u).card
  let b := f V*log V
  have den : 0 < b := mul_pos adm.2.2.1 (Real.log_pos (by exact_mod_cast (show 1 < V from adm.2.1)))
  have mass : (n:ℝ)*b ≤ m :=
    (le_div_iff₀ den).mp ((Nat.cast_le.mpr (le_max_left n M)).trans adm.2.2.2)
  have big := large P (l,u) (admissibleBox_anti (le_max_right n M) adm)
  have hm : (h:ℝ) < m := Nat.cast_lt.mpr (show h < (Rectangles.box P l u).card from big)
  have mp : 0 < m := (Nat.cast_nonneg (α:=ℝ) h).trans_lt hm
  have first : B*T*b ≤ δ*m := by
    have bound := (div_lt_iff₀ dp).mp hn
    nlinarith only [mul_le_mul_of_nonneg_right bound.le den.le,
      mul_le_mul_of_nonneg_left mass dp.le]
  have second : (H:ℝ) ≤ δ*m := by
    have bound := (div_lt_iff₀ dp).mp hh
    nlinarith only [bound,mul_lt_mul_of_pos_left hm dp]
  have count := counts l u
  change (1/2-q)*m ≤ ((Rectangles.box (O ∩ P) l u).card:ℝ)+B*(1+log (1+(outerRadius (l,u):ℝ)))+H at count
  change 1+log (1+(outerRadius (l,u):ℝ)) ≤ T*b at tested
  have ratio : (a:ℝ) ≤ ((Rectangles.box (O ∩ P) l u).card:ℝ)/m := by
    apply (le_div_iff₀ mp).mpr
    dsimp only [δ] at first second
    nlinarith only [count,first,second,mul_le_mul_of_nonneg_left tested bn]
  simpa only [m,ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_div_of_pos mp,ENNReal.ofReal_natCast]
    using ENNReal.ofReal_le_ofReal ratio

/-- Full source density on a target whose sufficiently thick rectangles
obey some position allowance. The generator is chosen before the target,
growth filter, allowance and threshold. -/
theorem filtered_generation_on_located_targets {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 < q) (small : q ≤ 1/2) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ∀ f : ℕ → ℝ, Tendsto f atTop atTop →
        (∃ (N : ℕ) (T : ℝ), ∀ r, admissibleBox f (e '' C z) N r → positionTest f T r) →
        ENNReal.ofReal (1/2-q) ≤ filteredRectangularDensity f (range (cubePlay G s)) (e '' C z) := by
  obtain ⟨G,works⟩ := filtered_generation_with_position_bound e inj hq small C inf rank
  refine ⟨G,fun z s pres => ?_⟩
  obtain ⟨valid,dense⟩ := works z s pres
  refine ⟨valid,?_⟩
  rintro f grows ⟨N,T,inside⟩
  rw [←filteredDensityOn_all]
  exact (dense f grows T).trans (filteredDensityOn_mono_eventually f _ _ _ _ N (fun r h _ => inside r h))

/-- A shortfall for the unrestricted source density would force deficient
rectangles beyond every position allowance at arbitrarily high filter
levels. The density cutoff b stays fixed as both levels increase. -/
theorem escaping_witness {d} (f : ℕ → ℝ) (O P : Set (Lattice d)) {a b : ℝ≥0∞}
    (localBound : ∀ T, a ≤ filteredRectangularDensityOn (positionTest f T) f O P)
    (shortfall : filteredRectangularDensity f O P < b) (gap : b < a) (n : ℕ) (T : ℝ) :
    ∃ r : Lattice d × Lattice d, admissibleBox f P n r ∧ ¬ positionTest f T r ∧
      ((Rectangles.box (O ∩ P) r.1 r.2).card:ℝ≥0∞)/(Rectangles.box P r.1 r.2).card < b := by
  let fraction (r : Lattice d × Lattice d) :=
    ((Rectangles.box (O ∩ P) r.1 r.2).card:ℝ≥0∞)/(Rectangles.box P r.1 r.2).card
  have high : b < ⨆ m : ℕ, ⨅ r : {r // admissibleBox f P m r ∧ positionTest f T r}, fraction r.val :=
    gap.trans_le (localBound T)
  obtain ⟨m,good⟩ := lt_iSup_iff.mp high
  have low : (⨅ r : {r // admissibleBox f P (max n m) r}, fraction r.val) < b :=
    (le_iSup (fun k => ⨅ r : {r // admissibleBox f P k r}, fraction r.val) (max n m)).trans_lt shortfall
  obtain ⟨⟨r,adm⟩,bad⟩ := iInf_lt_iff.mp low
  refine ⟨r,admissibleBox_anti (le_max_left ..) adm,fun tested => ?_,bad⟩
  exact (not_lt_of_ge (good.le.trans (iInf_le _ (⟨r,admissibleBox_anti (le_max_right ..) adm,tested⟩ :
    {r // admissibleBox f P m r ∧ positionTest f T r})))) bad

end
end GenLimit.KleinbergWei.Banach.RadialCounts
