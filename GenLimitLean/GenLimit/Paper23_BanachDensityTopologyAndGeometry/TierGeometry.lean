import GenLimit.Paper23_BanachDensityTopologyAndGeometry.DiscrepancyBoxes
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.DiscrepancyTiers
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TierWeights

/-! Every closed integer box is indexed by its endpoints. Its longest
side is counted in lattice sites, and dense overflow is assigned tier
zero. These conventions repair the tier and capacity issues in 5.9. -/
namespace GenLimit.KleinbergWei.Banach.TierGeometry
open Set Finset Real TierWeights
open scoped Classical
noncomputable section

def span {d} (l u : Lattice d) := Finset.univ.sup (fun i => (u i-l i).toNat) + 1
def scale (d : ℕ) (α : ℝ) := 2*d/α
def eta (ε : ℝ) := 3*ε^2/(2*π^2)
def baseline (ε α : ℝ) (d : ℕ) := (2*π^2/(3*ε^2))^(α/(2*d))
def tier (a : ℝ) (m : ℕ) (positive : 0 < m) : ℕ :=
  Nat.find (show ∃ j : ℕ, a ≤ m*2^j from
    let ⟨j,h,_,_⟩ := exists_least_sparsity_tier (a := a) (by exact_mod_cast positive : (0:ℝ)<m)
    ⟨j,h⟩)

theorem tier_bound (a : ℝ) (m : ℕ) (positive : 0 < m) :
    a ≤ m*2^(tier a m positive) := by
  unfold tier; exact Nat.find_spec (p := fun j : ℕ => a ≤ (m:ℝ)*2^j) _

theorem tier_minimal (a : ℝ) (m : ℕ) (positive : 0 < m) {j : ℕ} (h : a ≤ m*2^j) :
    tier a m positive ≤ j := Nat.find_min' _ h

private theorem span_lt {d} (l u : Lattice d) (i : Fin d) : u i-l i < (span l u : ℤ) := by
  have bound := Finset.le_sup (f := fun i => (u i-l i).toNat) (Finset.mem_univ i)
  dsimp only at bound
  unfold span; omega

private theorem numeric_capacity {d k b j : ℕ} {α ε : ℝ} (hd : 0 < d) (hk : 0 < k)
    (hb : 0 < b) (ha : 0 < α) (he : 0 < ε)
    (tierSpec : baseline ε α d * (b:ℝ)^α ≤ (k:ℝ)*2^j) :
    ((b:ℝ)^(2*d)) ≤ eta ε * capacityFactor (scale d α) k j := by
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  have kp : (0:ℝ) < k := by exact_mod_cast hk
  have bp : (0:ℝ) < b := by exact_mod_cast hb
  have et : 0 < eta ε := by unfold eta; positivity
  have base : 0 < 2*π^2/(3*ε^2) := by positivity
  have inv : 2*π^2/(3*ε^2) = (eta ε)⁻¹ := by unfold eta; rw [inv_div]
  have sp : 0 < scale d α := by unfold scale; positivity
  have logrel := Real.log_le_log (show 0 < baseline ε α d * (b:ℝ)^α by unfold baseline; positivity) tierSpec
  rw [Real.log_mul (by unfold baseline; positivity) (by positivity),baseline,Real.log_rpow base,
    inv,Real.log_inv,Real.log_rpow bp,Real.log_mul kp.ne' (by positivity),Real.log_pow] at logrel
  have mul := mul_le_mul_of_nonneg_left logrel sp.le
  have cancel : scale d α * (α/(2*d)) = 1 := by unfold scale; field_simp
  have cd : scale d α * α = 2*d := by unfold scale; field_simp
  apply (Real.log_le_log_iff (by positivity) (by unfold capacityFactor; positivity)).mp
  rw [Real.log_pow,capacityFactor,Real.log_mul et.ne' (exp_pos _).ne',Real.log_exp]
  push_cast
  nlinarith only [mul,congrArg (fun r : ℝ => r*log (eta ε)) cancel,
    congrArg (fun r : ℝ => r*log (b:ℝ)) cd]

abbrev Index {d : ℕ} (P : Set (Lattice d)) :=
  {r : Lattice d × Lattice d // (Rectangles.box P r.1 r.2).Nonempty}

def trace {d P} (r : @Index d P) := Rectangles.box P r.val.1 r.val.2
def boxTier {d P} (ε α : ℝ) (r : @Index d P) :=
  tier (baseline ε α d * (span r.val.1 r.val.2 : ℝ)^α) (trace r).card r.property.card_pos

private def fullBox {d P} (r : @Index d P) := Rectangles.box univ r.val.1 r.val.2

private theorem consistent {d P} (r : @Index d P) : r.val.1 ≤ r.val.2 := by
  obtain ⟨v,h⟩ := r.property
  exact (Rectangles.mem_box.mp h).1.1.trans (Rectangles.mem_box.mp h).1.2

private theorem bounds {d P} (r : @Index d P) :
    r.val.1 ∈ fullBox r ∧ r.val.2 ∈ fullBox r :=
  ⟨Rectangles.mem_box.mpr ⟨⟨le_rfl,consistent r⟩,trivial⟩,
   Rectangles.mem_box.mpr ⟨⟨consistent r,le_rfl⟩,trivial⟩⟩

private theorem fullBox_injective {d P} : Function.Injective (@fullBox d P) := by
  intro r s eq
  have rs := bounds r
  have sr := bounds s
  rw [eq] at rs
  rw [←eq] at sr
  exact Subtype.ext (Prod.ext (le_antisymm (Rectangles.mem_box.mp sr.1).1.1 (Rectangles.mem_box.mp rs.1).1.1)
    (le_antisymm (Rectangles.mem_box.mp rs.2).1.2 (Rectangles.mem_box.mp sr.2).1.2))

/-- Uniform local capacity for every finite selection of rectangles of a
given size and tier through a fixed word. -/
theorem local_count {d : ℕ} {P : Set (Lattice d)} {ε α : ℝ} (hd : 0 < d)
    (he : 0 < ε) (ha : 0 < α) (D : Finset (Index P)) (v : Lattice d) (k j : ℕ)
    (group : ∀ r ∈ D, v ∈ trace r ∧ (trace r).card = k ∧ boxTier ε α r = j) :
    (D.card : ℝ) ≤ eta ε * capacityFactor (scale d α) k j := by
  rcases D.eq_empty_or_nonempty with rfl | ne
  · simp only [Finset.card_empty,Nat.cast_zero]; unfold eta capacityFactor; positivity
  let b := D.sup fun r => span r.val.1 r.val.2
  obtain ⟨r,hr,eq⟩ := Finset.sup_mem_of_nonempty (f := fun r : Index P => span r.val.1 r.val.2) ne
  have eqb : span r.val.1 r.val.2 = b := eq
  have big := group r hr
  have ht := tier_bound (baseline ε α d * (span r.val.1 r.val.2 : ℝ)^α) _ r.property.card_pos
  change _ ≤ ((trace r).card : ℝ)*2^(boxTier ε α r) at ht
  rw [eqb,big.2.1,big.2.2] at ht
  have num := numeric_capacity hd (big.2.1 ▸ r.property.card_pos)
    (show 0 < b by rw [←eqb]; exact Nat.succ_pos _) ha he ht
  have cap := DiscrepancyBoxes.local_capacity univ v (D.image fullBox) (b := b) (by
    rintro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    have inside := (Rectangles.mem_box.mp (group s hs).1).1
    refine ⟨s.val.1,s.val.2,rfl,inside.1,inside.2,fun i => ?_⟩
    exact (span_lt _ _ i).trans_le (by exact_mod_cast (Finset.le_sup (f := fun s : Index P => span s.val.1 s.val.2) hs)))
  rw [Finset.card_image_of_injective _ fullBox_injective] at cap
  exact (show (D.card : ℝ) ≤ (b:ℝ)^(2*d) by exact_mod_cast cap).trans num

end
end GenLimit.KleinbergWei.Banach.TierGeometry
