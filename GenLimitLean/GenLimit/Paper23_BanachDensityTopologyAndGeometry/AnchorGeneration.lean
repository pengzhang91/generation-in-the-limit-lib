import GenLimit.Paper23_BanachDensityTopologyAndGeometry.AnchorPackets

/-! A generator for P23's rectangular density filter with localized tests.
One finite-history rule handles every fixed anchor simultaneously. -/
namespace GenLimit.KleinbergWei.Banach.AnchorPackets
open Finset Set Filter Real LogPowerCriterion BoardPermutations
open scoped Classical ENNReal
noncomputable section

/-- Pass from finite packets in a prescribed class to P23's density on that
class, using the source filter and one generator for the entire family. -/
theorem generation_of_logarithmic_packets {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (test : (Lattice d × Lattice d) → Prop) {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c)
    (packets : ∀ (D : Finset ℕ) (S : Finset (Lattice d × Lattice d)), (∀ r ∈ S, test r) →
      ClaimGame.CanForce D (PacketQuota e q c 0 D S))
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ENNReal.ofReal (1/2-q) ≤
        filteredRectangularDensityOn test f (range (cubePlay G s)) (e '' C z) := by
  choose move safe win using fun D => (ClaimGame.canForce_iff_covering ..).mp
    (all_boxes_on D test (packets D))
  obtain ⟨G,plays⟩ := shell_counts_of_board_moves e inj hq f grows C inf rank move safe
  let b := c * factor d
  have bn : 0 ≤ b := by
    apply mul_nonneg hc
    unfold factor
    linarith [log_nonneg (show 1 ≤ 2+(2:ℝ)^d by linarith [show (0:ℝ) ≤ 2^d by positivity])]
  refine ⟨G,fun z s pres => ?_⟩
  obtain ⟨valid,H,counts⟩ := plays z s pres
  refine ⟨valid,?_⟩
  apply FilterShells.density_of_shell_counts_on test _ _ f grows _ ((R:ℝ)*b) H (by positivity) (by positivity)
  intro l u tested J cover wide
  let V := geometricVolume l u
  have vp : 0 < V := Finset.prod_pos fun i _ => by have := wide i; omega
  have ln : 0 ≤ log V := Real.log_nonneg (by exact_mod_cast vp)
  let loss := b*(1+log V)
  have nn : 0 ≤ loss := mul_nonneg bn (by linarith)
  have bound := counts l u J cover loss nn (by
    intro D _ t n covered
    let X := D.filter (fun x => e x ∈ Finset.Icc l u)
    let h := textPrefix t n
    have eq : X.filter (· ∈ earned (move D) h) =
        X.filter (fun y => ∃ j < n, move D (textPrefix t j) (t j) = some y) := by
      ext y; simp only [mem_filter,earned_prefix,h]
    change (1/2-q)*(X.card:ℝ)-loss ≤
      ((X.filter (fun y => ∃ j < n, move D (textPrefix t j) (t j) = some y)).card:ℝ)
    rw [← eq]
    by_cases large : c*logSites (l,u) ≤ X.card
    · have hit := win D h covered (l,u) tested wide (by simpa only [add_zero,rpow_one] using large)
      exact (sub_le_self _ nn).trans hit
    · have cap := mul_le_mul_of_nonneg_left (log_comparison (l,u) wide).2.2 hc
      change c*logSites (l,u) ≤ c*(factor d*(1+log V)) at cap
      have small : (X.card:ℝ) ≤ loss := (le_of_not_ge large).trans (by simpa only [loss,b,mul_assoc] using cap)
      exact (show (1/2-q)*(X.card:ℝ)-loss ≤ 0 by
        nlinarith [mul_nonneg hq (Nat.cast_nonneg (α:=ℝ) X.card)]).trans (Nat.cast_nonneg _))
  dsimp only [loss,V] at bound
  linarith only [bound,show (J.card:ℝ)*(R*(b*(1+log (geometricVolume l u)))) =
    J.card*(R*b)*(1+log (geometricVolume l u)) by ring]

/-- Rectangles containing enough of a prescribed reference distribution. -/
def massTest {d} (μ : Lattice d → ℝ) (p : ℕ) (r : Lattice d × Lattice d) : Prop :=
  1 ≤ (2+((Finset.Icc r.1 r.2).card:ℝ))^p * ∑ a ∈ Finset.Icc r.1 r.2, μ a

/-- The reference mass can be spread over an infinite lattice. For finite
packets only the weights in the union of their rectangles are needed. -/
theorem filtered_generation_of_anchor_mass {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (μ : Lattice d → ℝ) (nonneg : ∀ a, 0 ≤ μ a)
    (budget : ∀ A : Finset (Lattice d), ∑ a ∈ A, μ a ≤ 1) (p : ℕ)
    {q : ℝ} (hq : 0 < q) (small : q ≤ 1/2) (f : ℕ → ℝ) (grows : Tendsto f atTop atTop)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ENNReal.ofReal (1/2-q) ≤
        filteredRectangularDensityOn (massTest μ p) f (range (cubePlay G s)) (e '' C z) := by
  obtain ⟨c,hc,works⟩ := logarithmic_of_anchor_mass e hq small p
  apply generation_of_logarithmic_packets e inj _ hq.le (zero_le_one.trans hc) _ f grows C inf rank
  intro D S tested
  let A := S.biUnion (fun r => Finset.Icc r.1 r.2)
  apply works D S A μ (fun a _ => nonneg a) (budget A)
  intro r mem
  have eq : A.filter (· ∈ Finset.Icc r.1 r.2) = Finset.Icc r.1 r.2 := by
    ext a
    exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨r,mem,h⟩,h⟩⟩
  simpa only [anchorMass,←Finset.sum_filter,eq] using (show
    1 ≤ (2+((Finset.Icc r.1 r.2).card:ℝ))^p * (∑ a ∈ Finset.Icc r.1 r.2, μ a) from tested r mem)

private def reference {d} (a : Lattice d) : ℝ := (1/2:ℝ)^(Encodable.encode a + 1)

private theorem reference_budget {d} (A : Finset (Lattice d)) : ∑ a ∈ A, reference a ≤ 1 := by
  let w (i : ℕ) := (1/2:ℝ)^(i+1)
  have geom (n : ℕ) : ∑ i ∈ Finset.range n, w i = 1-(1/2:ℝ)^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [w,pow_succ]; ring
  let E := A.image Encodable.encode
  have eq : ∑ a ∈ A, reference a = ∑ i ∈ E, w i := by
    rw [Finset.sum_image (fun _ _ _ _ h => Encodable.encode_injective h)]; rfl
  have sub : E ⊆ Finset.range (E.sup id + 1) := fun x mem =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f:=id) mem))
  rw [eq]
  apply (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by dsimp [w]; positivity)).trans
  rw [geom]; exact sub_le_self _ (by positivity)

/-- One generator handles rectangles through every fixed lattice point,
with all aspect ratios allowed and no lower bound on target occupancy.
The anchor is chosen after the generator and its presentation. -/
theorem filtered_generation_at_every_anchor {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 < q) (small : q ≤ 1/2) (f : ℕ → ℝ) (grows : Tendsto f atTop atTop)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ∀ a : Lattice d, ENNReal.ofReal (1/2-q) ≤
        filteredRectangularDensityOn (fun r => a ∈ Finset.Icc r.1 r.2) f
          (range (cubePlay G s)) (e '' C z) := by
  have pos (a : Lattice d) : 0 < reference a := by unfold reference; positivity
  obtain ⟨G,works⟩ := filtered_generation_of_anchor_mass e inj reference
    (fun a => (pos a).le) reference_budget 1 hq small f grows C inf rank
  refine ⟨G,fun z s pres => ?_⟩
  obtain ⟨valid,dense⟩ := works z s pres
  refine ⟨valid,fun a => ?_⟩
  obtain ⟨K,large⟩ := exists_nat_ge (1/reference a)
  obtain ⟨N,_,forces⟩ := large_volume_of_admissible (d:=d) f K
  apply dense.trans (filteredDensityOn_mono_eventually f _ _ _ _ N ?_)
  intro r adm through
  have scale := forces _ r adm
  have sites : geometricVolume r.1 r.2 ≤ (Finset.Icc r.1 r.2).card := by
    rw [← LatticeTiles.unitVolume_eq adm.1]
    exact LatticeTiles.unitVolume_le_card (fun i => (adm.1 i).le)
  have cap : 1/reference a ≤ 2+((Finset.Icc r.1 r.2).card:ℝ) := by
    have h : (K:ℝ) ≤ (Finset.Icc r.1 r.2).card := by exact_mod_cast scale.trans sites
    linarith
  have mass := Finset.single_le_sum (f:=reference) (fun b _ => (pos b).le) through
  unfold massTest
  rw [pow_one]
  exact ((div_le_iff₀ (pos a)).mp cap).trans (mul_le_mul_of_nonneg_left mass (by positivity))

end
end GenLimit.KleinbergWei.Banach.AnchorPackets
