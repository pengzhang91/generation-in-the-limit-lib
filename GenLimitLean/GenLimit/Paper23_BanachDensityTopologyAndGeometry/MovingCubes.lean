import GenLimit.Paper23_BanachDensityTopologyAndGeometry.SingletonReduction

/-! The moving-cube conclusion of P23 Corollary 5.6 suffices for the full
rectangular generation conclusion in Theorem 5.5 across dimensions.
Duplicate the coordinates of every word. The lower faces of a translated
cube on the first copy and its upper faces on the second copy cut out the
two independent endpoints of each original interval. -/
namespace GenLimit.KleinbergWei.Banach.MovingCubes
open Finset Set Real Filter
open scoped Classical ENNReal
noncomputable section

abbrev Box (d : ℕ) := Lattice d × Lattice d

/-- Cubes with integer center and positive integer radius. -/
def IsCube {d} (R : Box d) : Prop :=
  ∃ z : Lattice d, ∃ k : ℕ, 0 < k ∧ (∀ i, R.1 i = z i-k) ∧ ∀ i, R.2 i = z i+k

def diagonal {d} (x : Lattice d) : Lattice (d+d) := Fin.append x x
private def project {d} (x : Lattice (d+d)) : Lattice d := fun j => x (Fin.castAdd d j)

private theorem left {d} (x : Lattice d) : project (diagonal x) = x := by
  funext j; exact Fin.append_left ..

theorem diagonal_injective (d : ℕ) : Function.Injective (@diagonal d) :=
  Function.LeftInverse.injective left

private def center {d} (R : Box d) (V : ℕ) : Lattice (d+d) :=
  Fin.append (fun j => R.1 j+V) (fun j => R.2 j-V)

def cube {d} (R : Box d) : Box (d+d) :=
  let V := geometricVolume R.1 R.2
  (fun i => center R V i-V,fun i => center R V i+V)

private theorem width_bound {d} (R : Box d) (w : ∀ i, R.1 i < R.2 i) (i : Fin d) :
    R.2 i-R.1 i ≤ (geometricVolume R.1 R.2:ℤ) := by
  have h := Finset.single_le_prod' (s:=Finset.univ) (f:= fun j => (R.2 j-R.1 j).toNat)
    (fun j _ => by change 1 ≤ (R.2 j-R.1 j).toNat; have := w j; omega) (Finset.mem_univ i)
  change (R.2 i-R.1 i).toNat ≤ geometricVolume R.1 R.2 at h
  omega

private theorem volume_pos {d} (R : Box d) (w : ∀ i, R.1 i < R.2 i) :
    0 < geometricVolume R.1 R.2 := Finset.prod_pos (fun i _ => by
      change 0 < (R.2 i-R.1 i).toNat; have := w i; omega)

theorem cube_shape {d} (R : Box d) (w : ∀ i, R.1 i < R.2 i) : IsCube (cube R) :=
  ⟨_,_,volume_pos R w,fun _ => rfl,fun _ => rfl⟩

private def volume (d v : ℕ) := (2*v)^(d+d)

theorem cube_volume {d} (R : Box d) :
    geometricVolume (cube R).1 (cube R).2 = volume d (geometricVolume R.1 R.2) := by
  let V := geometricVolume R.1 R.2
  have each (i : Fin (d+d)) : ((cube R).2 i-(cube R).1 i).toNat = 2*V := by
    change (center R V i+V-(center R V i-V)).toNat = 2*V
    omega
  simp [geometricVolume,each,volume,V]

theorem diagonal_mem {d} (R : Box d) (w : ∀ i, R.1 i < R.2 i) (x : Lattice d) :
    diagonal x ∈ Finset.Icc (cube R).1 (cube R).2 ↔ x ∈ Finset.Icc R.1 R.2 := by
  rw [Finset.mem_Icc,Finset.mem_Icc]
  constructor
  · rintro ⟨lo,hi⟩
    exact ⟨fun i => by simpa only [cube,center,diagonal,Fin.append_left,add_sub_cancel_right] using lo (Fin.castAdd d i),
      fun i => by simpa only [cube,center,diagonal,Fin.append_right,sub_add_cancel] using hi (Fin.natAdd d i)⟩
  · rintro ⟨lo,hi⟩
    constructor <;> intro j <;> induction j using Fin.addCases with
    | left i =>
      simp only [cube,center,diagonal,Fin.append_left]
      have bound := width_bound R w i
      have low : R.1 i ≤ x i := lo i
      have high : x i ≤ R.2 i := hi i
      omega
    | right i =>
      simp only [cube,center,diagonal,Fin.append_right]
      have bound := width_bound R w i
      have low : R.1 i ≤ x i := lo i
      have high : x i ≤ R.2 i := hi i
      omega

/-- Every target and every subset of its outputs have exactly the same
point count on the lifted cube as on the original rectangle. -/
theorem card_trace {d} (P : Set (Lattice d)) (R : Box d) (w : ∀ i, R.1 i < R.2 i) :
    (Rectangles.box (diagonal '' P) (cube R).1 (cube R).2).card =
      (Rectangles.box P R.1 R.2).card := by
  have eq : Rectangles.box (diagonal '' P) (cube R).1 (cube R).2 =
      (Rectangles.box P R.1 R.2).image diagonal := by
    ext y
    constructor
    · intro hy
      obtain ⟨inside,x,hx,rfl⟩ := Rectangles.mem_box.mp hy
      exact Finset.mem_image.mpr ⟨x,Rectangles.mem_box.mpr
        ⟨Finset.mem_Icc.mp ((diagonal_mem R w x).mp (Finset.mem_Icc.mpr inside)),hx⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨inside,member⟩ := Rectangles.mem_box.mp hx
      exact Rectangles.mem_box.mpr ⟨Finset.mem_Icc.mp ((diagonal_mem R w x).mpr
        (Finset.mem_Icc.mpr inside)),x,member,rfl⟩
  rw [eq,Finset.card_image_of_injective _ (diagonal_injective d)]

private theorem vol_strict {d} (hd : 0 < d) : StrictMono (volume d) := by
  intro v w h
  exact Nat.pow_lt_pow_left (by omega) (by omega)

private def originalVolume {d} (hd : 0 < d) (n : ℕ) :=
  Nat.find (show ∃ v, n ≤ volume d v from ⟨n,(vol_strict hd).id_le _⟩)

private theorem original_spec {d} (hd : 0 < d) (n : ℕ) : n ≤ volume d (originalVolume hd n) :=
  Nat.find_spec (p := fun v => n ≤ volume d v) _

private theorem vol_inverse {d} (hd : 0 < d) (n : ℕ) : originalVolume hd (volume d n) = n := by
  apply le_antisymm
  · exact Nat.find_min' _ le_rfl
  · exact (vol_strict hd).le_iff_le.mp (original_spec hd _)

private theorem original_mono {d} (hd : 0 < d) : Monotone (originalVolume hd) := by
  intro n m h; exact Nat.find_min' _ (h.trans (original_spec hd _))

private theorem original_grows {d} (hd : 0 < d) : Tendsto (originalVolume hd) atTop atTop := by
  apply tendsto_atTop.mpr
  intro v
  exact eventually_atTop.mpr ⟨volume d v,fun n hn => (vol_inverse hd v) ▸ original_mono hd hn⟩

/-- Rescale the filter to pay for the polynomial growth in cube volume. -/
def cubeFilter {d} (hd : 0 < d) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f (originalVolume hd n)/((d+d:ℕ)*2)

private theorem denom_pos {d : ℕ} (hd : 0 < d) : 0 < ((d+d:ℕ):ℝ)*2 := by positivity

theorem cubeFilter_grows {d} (hd : 0 < d) {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    Tendsto (cubeFilter hd f) atTop atTop := (hf.comp (original_grows hd)).atTop_div_const (denom_pos hd)

theorem cubeFilter_mono {d} (hd : 0 < d) {f : ℕ → ℝ} (hf : Monotone f) : Monotone (cubeFilter hd f) :=
  fun _ _ h => div_le_div_of_nonneg_right (hf (original_mono hd h)) (denom_pos hd).le

theorem cube_admissible {d} (hd : 0 < d) (f : ℕ → ℝ) (P : Set (Lattice d)) {n : ℕ} {R : Box d}
    (adm : admissibleBox f P n R) : admissibleBox (cubeFilter hd f) (diagonal '' P) n (cube R) := by
  obtain ⟨w,big,pos,ratio⟩ := adm
  let V := geometricVolume R.1 R.2
  obtain ⟨z,k,hk,lo,hi⟩ := cube_shape R w
  have vr : 2 ≤ volume d V := big.trans ((vol_strict hd).id_le V)
  have fv : 0 < f V := pos
  have den := denom_pos hd
  have changed : cubeFilter hd f (volume d V) = f V/((d+d:ℕ)*2) := by rw [cubeFilter,vol_inverse]
  refine ⟨fun i => by rw [lo i,hi i]; omega,by rwa [cube_volume],?_,?_⟩
  · rw [cube_volume,changed]; exact div_pos fv den
  rw [card_trace _ _ w,cube_volume,changed]
  have vbig : (2:ℝ) ≤ V := by exact_mod_cast big
  have vp : 0 < (V:ℝ) := by linarith
  have lv := Real.log_le_log (by norm_num : (0:ℝ)<2) vbig
  have logvol : log (volume d V) = ((d+d:ℕ):ℝ)*(log 2+log V) := by
    simp only [volume,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Real.log_pow,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) vp.ne']
  have lower : 0 < log (volume d V) := Real.log_pos (by exact_mod_cast (show 1 < volume d V by omega))
  have le : (f V/(((d+d:ℕ):ℝ)*2))*log (volume d V) ≤ f V*log V := by
    rw [logvol,div_mul_eq_mul_div,div_le_iff₀ den]
    nlinarith only [mul_nonneg (mul_nonneg fv.le (Nat.cast_nonneg (α:=ℝ) (d+d))) (sub_nonneg.mpr lv)]
  exact ratio.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (div_pos fv den) lower) le)

/-- A lower bound on the cube density on the diagonal transfers to every
rectangle in the original lattice. -/
theorem density_le {d} (hd : 0 < d) (f : ℕ → ℝ) (P O : Set (Lattice d))
    (Y : Set (Lattice (d+d))) (captured : diagonal ⁻¹' Y ⊆ O) :
    filteredRectangularDensityOn IsCube (cubeFilter hd f) Y (diagonal '' P) ≤
      filteredRectangularDensity f O P := by
  apply iSup_le
  intro n
  apply le_trans _ (le_iSup (fun m => ⨅ R : {R // admissibleBox f P m R},
    ((Rectangles.box (O ∩ P) R.val.1 R.val.2).card:ℝ≥0∞)/(Rectangles.box P R.val.1 R.val.2).card) n)
  apply le_iInf
  rintro ⟨R,adm⟩
  let Q := (⟨cube R,cube_admissible hd f P adm,cube_shape R adm.1⟩ :
    {Q // admissibleBox (cubeFilter hd f) (diagonal '' P) n Q ∧ IsCube Q})
  apply iInf_le_of_le Q
  change ((Rectangles.box (Y ∩ diagonal '' P) (cube R).1 (cube R).2).card:ℝ≥0∞) /
    (Rectangles.box (diagonal '' P) (cube R).1 (cube R).2).card ≤ _
  rw [←Set.image_preimage_inter,card_trace _ _ adm.1,card_trace _ _ adm.1]
  have sub : Rectangles.box ((diagonal ⁻¹' Y) ∩ P) R.1 R.2 ⊆ Rectangles.box (O ∩ P) R.1 R.2 := by
    intro x hx
    obtain ⟨inR,hit,inP⟩ := Rectangles.mem_box.mp hx
    exact Rectangles.mem_box.mpr ⟨inR,captured hit,inP⟩
  gcongr

/-- Decode a diagonal reply. An off-diagonal reply returns the current
input, so it cannot consume a future fresh output on the original board. -/
def decode {d} (A : List (Lattice (d+d)) → Lattice (d+d)) (p : List (Lattice d)) :=
  let y := A (p.map diagonal)
  if diagonal (project y) = y then project y else p.getLastD 0

private theorem play_decode {d} (A : List (Lattice (d+d)) → Lattice (d+d)) (s : ℕ → Lattice d) (i : ℕ) :
    let y := cubePlay A (diagonal ∘ s) i
    cubePlay (decode A) s i = if diagonal (project y) = y then project y else s i := by
  have same : (textPrefix s (i+1)).map diagonal = textPrefix (diagonal ∘ s) (i+1) := by
    simp [textPrefix,List.map_map]
  simp only [cubePlay,decode,same]
  rw [show (textPrefix s (i+1)).getLastD 0 = s i by rw [textPrefix_succ,List.getLastD_concat]]

theorem decoded_run {d} (A : List (Lattice (d+d)) → Lattice (d+d)) (s : ℕ → Lattice d)
    (K : Set (Lattice d)) (valid : cubeValid A (diagonal ∘ s) (diagonal '' K)) :
    cubeValid (decode A) s K ∧ diagonal ⁻¹' range (cubePlay A (diagonal ∘ s)) ⊆ range (cubePlay (decode A) s) := by
  let y := cubePlay A (diagonal ∘ s)
  have decode_hit {i x} (hit : y i = diagonal x) : cubePlay (decode A) s i = x := by
    have eq := play_decode A s i
    change _ = if diagonal (project (y i)) = y i then project (y i) else s i at eq
    simpa only [hit,left,if_true] using eq
  refine ⟨?_,fun x ⟨i,eq⟩ => ⟨i,decode_hit eq⟩⟩
  obtain ⟨T,rest⟩ := valid
  refine ⟨T,fun i hi => ?_⟩
  obtain ⟨⟨x,hx,diag⟩,input,prior⟩ := rest i hi
  have at_i : y i = diagonal x := diag.symm
  rw [decode_hit at_i]
  have fresh (j) (hj : j ≤ i) : s j ≠ x := by
    intro eq; exact input j hj ((congrArg diagonal eq).trans diag)
  refine ⟨hx,fresh,fun j hj => ?_⟩
  have eq := play_decode A s j
  change _ = if diagonal (project (y j)) = y j then project (y j) else s j at eq
  rw [eq]
  split
  next diag_j =>
    intro same
    exact prior j hj (diag_j.symm.trans ((congrArg diagonal same).trans diag))
  next => exact fresh j hj.le

/-- A filter that eventually dominates a power of the logarithm retains
this property under the polynomial change of volume on the diagonal. -/
theorem cubeFilter_dominates {d} (hd : 0 < d) (f : ℕ → ℝ) {τ B : ℝ} (ht : 0 ≤ τ)
    (dom : ∀ᶠ n : ℕ in atTop, (log n)^τ ≤ B*f n) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (log n)^τ ≤ C*cubeFilter hd f n := by
  let a : ℝ := ((d+d:ℕ):ℝ)*2
  have ap : 0 < a := denom_pos hd
  refine ⟨a^τ*B*a,?_⟩
  filter_upwards [(original_grows hd).eventually dom,
    (original_grows hd).eventually (eventually_ge_atTop 2), eventually_ge_atTop 2] with n h hn nn
  let v := originalVolume hd n
  have vp : (2:ℝ) ≤ v := by exact_mod_cast hn
  have np : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have vl := log_le_log (by norm_num : (0:ℝ)<2) vp
  have nonneg : 0 ≤ log v := log_nonneg (by linarith)
  have upper : log n ≤ a*log v := by
    have bound : (n:ℝ) ≤ volume d v := by exact_mod_cast original_spec hd n
    apply (log_le_log (by linarith) bound).trans
    rw [volume,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Real.log_pow,Real.log_mul (by norm_num) (by linarith : (v:ℝ) ≠ 0)]
    dsimp [a]
    nlinarith only [mul_le_mul_of_nonneg_left vl (Nat.cast_nonneg (α:=ℝ) (d+d))]
  have pw := rpow_le_rpow (log_nonneg np) upper ht
  rw [Real.mul_rpow ap.le nonneg] at pw
  refine (pw.trans (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ap.le _))).trans_eq ?_
  change a^τ*(B*f v) = a^τ*B*a*(f v/a)
  field_simp

/-- Pull a uniform logarithmic-power guarantee on the doubled lattice
back to every rectangle of the original lattice, using the same decoded
generator for all dominated filters and all presentations. -/
theorem descend_generation_power {d} (hd : 0 < d) (K : ℕ → Set (Lattice d)) {τ a : ℝ} (ht : 0 ≤ τ)
    (A : List (Lattice (d+d)) → Lattice (d+d))
    (works : ∀ z s, Set.range s = diagonal '' K z → cubeValid A s (diagonal '' K z) ∧
      ∀ (g : ℕ → ℝ) (B : ℝ), (∀ᶠ n : ℕ in atTop, (log n)^τ ≤ B*g n) →
        ENNReal.ofReal a ≤ filteredRectangularDensity g (range (cubePlay A s)) (diagonal '' K z)) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z s, Set.range s = K z → cubeValid G s (K z) ∧
      ∀ (f : ℕ → ℝ) (B : ℝ), (∀ᶠ n : ℕ in atTop, (log n)^τ ≤ B*f n) →
        ENNReal.ofReal a ≤ filteredRectangularDensity f (range (cubePlay G s)) (K z) := by
  refine ⟨decode A,fun z s full => ?_⟩
  obtain ⟨valid,lower⟩ := works z (diagonal ∘ s) (by rw [Set.range_comp,full])
  obtain ⟨ok,captured⟩ := decoded_run A s (K z) valid
  refine ⟨ok,fun f B dom => ?_⟩
  obtain ⟨C,hC⟩ := cubeFilter_dominates hd f ht dom
  apply (lower _ C hC).trans
  apply le_trans _ (density_le hd f _ _ _ captured)
  rw [←filteredDensityOn_all]
  exact filteredDensityOn_mono_eventually _ _ _ _ _ 0 (fun _ _ _ => trivial)

/-- The moving-cube conclusion restricted even to known singleton targets,
with a positive nondecreasing growing filter as in the source. -/
def SingletonCubeGuarantee (d : ℕ) (ε : ℝ) := ∀ K : Set (Lattice d), K.Infinite →
  ∀ f : ℕ → ℝ, Monotone f → (∀ v, 0 < f v) → Tendsto f atTop atTop →
  ∃ A : List (Lattice d) → Lattice d, ∀ s : ℕ → Lattice d, Set.range s = K → Function.Injective s →
    cubeValid A s K ∧ ENNReal.ofReal (1/2-ε) ≤ filteredRectangularDensityOn IsCube f (range (cubePlay A s)) K

/-- A cube generator in doubled dimension gives a rectangle generator at
the same tolerance. Doubling is applied to the words, not to the time steps. -/
theorem singleton_of_cubes {d} (hd : 0 < d) {ε : ℝ} (cubes : SingletonCubeGuarantee (d+d) ε) :
    SingletonFilteredGuarantee d ε := by
  intro K inf f mono pos grows
  obtain ⟨A,gen⟩ := cubes (diagonal '' K) (inf.image (diagonal_injective d).injOn) (cubeFilter hd f)
    (cubeFilter_mono hd mono) (fun _ => div_pos (pos _) (denom_pos hd)) (cubeFilter_grows hd grows)
  refine ⟨decode A,fun s pres inj => ?_⟩
  obtain ⟨valid,lower⟩ := gen (diagonal ∘ s) (by rw [Set.range_comp,pres]) ((diagonal_injective d).comp inj)
  obtain ⟨ok,captured⟩ := decoded_run A s K valid
  exact ⟨ok,lower.trans (density_le hd f K _ _ captured)⟩

/-- Across dimensions, solving the translated, integer-centered cube case
on known singleton languages is equivalent to the full Theorem 5.5. -/
theorem generation_iff_singleton_cubes :
    (∀ d ε, 0 < ε → FiniteRankFilteredGuarantee d ε) ↔ ∀ d ε, 0 < ε → SingletonCubeGuarantee d ε := by
  rw [filtered_generation_iff_singletons]
  constructor
  · intro gen d ε he K inf f mono pos grows
    obtain ⟨A,ok⟩ := gen d ε he K inf f mono pos grows
    refine ⟨A,fun s pres inj => ?_⟩
    obtain ⟨valid,lower⟩ := ok s pres inj
    refine ⟨valid,lower.trans ?_⟩
    rw [←filteredDensityOn_all]
    exact filteredDensityOn_mono_eventually f _ _ _ _ 0 (fun _ _ _ => trivial)
  · intro cubes d ε he
    cases d with
    | zero =>
      intro K inf
      exact (inf (Set.Subsingleton.finite (fun _ _ _ _ => Subsingleton.elim ..))).elim
    | succ d => exact singleton_of_cubes (Nat.succ_pos d) (cubes _ _ he)

end
end GenLimit.KleinbergWei.Banach.MovingCubes
