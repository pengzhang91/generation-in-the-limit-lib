import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardScale

/-! The sequence-dependent filter in Overview equation (2) of P23.
For a fixed output and target, allowing each nondegenerate sequence to
choose its own divergent multiplier gives the pure logarithmic density. -/
namespace GenLimit.KleinbergWei.Banach.OverviewFilter
open Set Filter Real
open scoped ENNReal Classical
noncomputable section

/-- Nondecreasing positive multipliers suffice in the sequence-dependent
existence quantifier of equation (2). The volume need not be monotone. -/
theorem slow_multiplier (V : ℕ → ℕ) (a : ℕ → ℝ) (grow : Tendsto a atTop atTop) :
    ∃ f : ℕ → ℝ, Monotone f ∧ (∀ v, 0 < f v) ∧ Tendsto f atTop atTop ∧
      Tendsto (fun k => a k / f (V k)) atTop atTop := by
  choose N after using fun j : ℕ => eventually_atTop.mp
    (grow.eventually_ge_atTop (((j:ℝ)+1)^2))
  let size (j : ℕ) := (Finset.range (N j)).sup V
  let f := BoardScale.scale size
  refine ⟨f,BoardScale.monotone size,BoardScale.positive size,BoardScale.grows size,?_⟩
  have before (j k : ℕ) (small : a k < ((j:ℝ)+1)^2) : f (V k) ≤ (j:ℝ)+1 := by
    have lt : k < N j := lt_of_not_ge fun ge => small.not_ge (after j k ge)
    by_cases zero : V k = 0
    · have B := BoardScale.small size j 1 (by simp [size]) one_pos
      exact ((BoardScale.monotone size) (show V k ≤ 1 by omega)).trans B
    apply BoardScale.small size j _ _ (Nat.pos_of_ne_zero zero)
    have cap : V k ≤ size j := Finset.le_sup (Finset.mem_range.mpr lt)
    exact (Real.log_le_self (Nat.cast_nonneg _)).trans (by exact_mod_cast cap)
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨t,large⟩ := exists_nat_gt (max b 1)
  filter_upwards [grow.eventually_ge_atTop (((t:ℝ)+1)^2)] with k hk
  let j := ⌊Real.sqrt (a k)⌋₊
  have jlo : (j:ℝ) ≤ sqrt (a k) := Nat.floor_le (sqrt_nonneg _)
  have jhi : sqrt (a k) < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have ak : 0 ≤ a k := (sq_nonneg _).trans hk
  have sq := Real.sq_sqrt ak
  have lt : a k < ((j:ℝ)+1)^2 := by nlinarith [sq_lt_sq' (by linarith [sqrt_nonneg (a k),Nat.cast_nonneg (α:=ℝ) j]) jhi]
  have cap := before j k lt
  have jp : (j:ℝ) ≤ sqrt (a k) := jlo
  have lower : (t:ℝ)+1 ≤ sqrt (a k) := (Real.le_sqrt (by positivity) ak).mpr hk
  have bp : b < t := (le_max_left ..).trans_lt large
  apply le_trans bp.le
  apply (le_div_iff₀ (BoardScale.positive size (V k))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg (α:=ℝ) t),
    mul_le_mul_of_nonneg_left (add_le_add_right jp 1) (Nat.cast_nonneg (α:=ℝ) t),
    mul_nonneg (sub_nonneg.mpr lower) (sqrt_nonneg (a k)),sq,lower]

abbrev Box (d : ℕ) := Lattice d × Lattice d

/-- A sequence satisfies P23 equation (2) if it admits a divergent
multiplier. The multiplier may depend on the sequence. -/
def Nondegenerate {d} (K : Set (Lattice d)) (Q : ℕ → Box d) : Prop :=
  ∃ F : ℝ → ℝ, Tendsto F atTop atTop ∧
    Tendsto (fun k => let r := Q k; let V := geometricVolume r.1 r.2
      ((Rectangles.box K r.1 r.2).card : ℝ) / (F V * log V)) atTop atTop

theorem nondegenerate_iff {d} (K : Set (Lattice d)) (Q : ℕ → Box d) :
    Nondegenerate K Q ↔ Tendsto (fun k => let r := Q k
      ((Rectangles.box K r.1 r.2).card : ℝ) / log (geometricVolume r.1 r.2)) atTop atTop := by
  let V (k : ℕ) := geometricVolume (Q k).1 (Q k).2
  let a (k : ℕ) := ((Rectangles.box K (Q k).1 (Q k).2).card : ℝ)/log (V k)
  have same (f : ℕ → ℝ) (k : ℕ) : ((Rectangles.box K (Q k).1 (Q k).2).card : ℝ)/(f (V k)*log (V k)) =
      a k/f (V k) := by rw [div_div, mul_comm]
  constructor
  · rintro ⟨F,grows,thick⟩
    let f (v : ℕ) := F v
    have invLim : Tendsto (fun v : ℕ => (f v)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (grows.comp tendsto_natCast_atTop_atTop)
    obtain ⟨B,bound⟩ := invLim.bddAbove_range
    let M := max 1 B
    have mp : 0 < M := zero_lt_one.trans_le (le_max_left ..)
    change Tendsto a atTop atTop
    apply tendsto_atTop.mpr
    intro t
    filter_upwards [thick.eventually_ge_atTop (t*M)] with k hk
    change t*M ≤ _/(f (V k)*log (V k)) at hk
    rw [same,div_eq_mul_inv] at hk
    have nonneg : 0 ≤ a k := div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    exact le_of_mul_le_mul_right (hk.trans (mul_le_mul_of_nonneg_left
      ((bound (Set.mem_range_self (V k))).trans (le_max_right ..)) nonneg)) mp
  · intro pure
    obtain ⟨f,_,_,grows,thick⟩ := slow_multiplier V a pure
    refine ⟨fun v => f ⌊v⌋₊,grows.comp tendsto_nat_floor_atTop,?_⟩
    simpa only [Nat.floor_natCast,←same] using thick

private def frac {d} (O K : Set (Lattice d)) (r : Box d) : ℝ≥0∞ :=
  ((Rectangles.box (O ∩ K) r.1 r.2).card:ℝ≥0∞)/(Rectangles.box K r.1 r.2).card

/-- All rectangles in an eligible sequence may translate and change aspect
ratio independently at each index. -/
def SequenceBound {d} (O K : Set (Lattice d)) (b : ℝ≥0∞) : Prop :=
  ∀ Q : ℕ → Box d, (∀ k i, (Q k).1 i < (Q k).2 i) →
    (∀ k, 2 ≤ geometricVolume (Q k).1 (Q k).2) → Nondegenerate K Q →
    b ≤ Filter.liminf (fun k => frac O K (Q k)) atTop

theorem sequenceBound_iff {d} (O K : Set (Lattice d)) (b : ℝ≥0∞) :
    SequenceBound O K b ↔ b ≤ filteredRectangularDensity (fun _ => 1) O K := by
  let f : ℕ → ℝ := fun _ => 1
  let test (n : ℕ) := ⨅ r : {r // admissibleBox f K n r}, frac O K r.val
  change SequenceBound O K b ↔ b ≤ ⨆ n, test n
  constructor
  · intro all
    by_contra! bad
    obtain ⟨c,above,below⟩ := exists_between bad
    have small (n : ℕ) : ∃ r, admissibleBox f K n r ∧ frac O K r < c := by
      obtain ⟨⟨r,adm⟩,low⟩ := iInf_lt_iff.mp ((le_iSup test n).trans_lt above)
      exact ⟨r,adm,low⟩
    choose Q adm low using small
    have nd := (nondegenerate_iff K Q).mpr (by
      apply tendsto_atTop.mpr
      intro a
      obtain ⟨n,hn⟩ := exists_nat_ge a
      filter_upwards [eventually_ge_atTop n] with k hk
      exact hn.trans ((Nat.cast_le.mpr hk).trans (by simpa [f] using (adm k).2.2.2)))
    have high := all Q (fun k => (adm k).1) (fun k => (adm k).2.1) nd
    exact below.not_ge (high.trans (Filter.liminf_le_of_le (by isBoundedDefault) (fun x hx => by
      obtain ⟨k,hk⟩ := hx.exists
      exact hk.trans (low k).le)))
  · intro bound Q wide large thick
    apply bound.trans
    apply iSup_le
    intro n
    apply Filter.le_liminf_of_le (by isBoundedDefault)
    filter_upwards [((nondegenerate_iff K Q).mp thick).eventually_ge_atTop (n:ℝ)] with k score
    apply iInf_le_of_le (⟨Q k,wide k,large k,zero_lt_one,by simpa [f] using score⟩ :
      {r // admissibleBox f K n r})
    exact le_rfl

end
end GenLimit.KleinbergWei.Banach.OverviewFilter
