import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RegionRectangles

/-! The alternating game at the logarithmic threshold of P23 Theorem 5.5.
One strategy can protect rectangles of arbitrarily different sizes when a
finite distribution of points puts enough mass in each tested rectangle.
In particular a packet of rectangles containing a common point qualifies. -/
namespace GenLimit.KleinbergWei.Banach.AnchorPackets
open Finset Real BoardPermutations LogPowerCriterion RegionGame
open scoped Classical
noncomputable section

private abbrev Box (d : ℕ) := Lattice d × Lattice d
private def sites {d} (r : Box d) := (Finset.Icc r.1 r.2).card

/-- Total anchor weight in the inclusive lattice rectangle. -/
def anchorMass {d} (A : Finset (Lattice d)) (μ : Lattice d → ℝ) (r : Lattice d × Lattice d) : ℝ :=
  ∑ a ∈ A, if a ∈ Finset.Icc r.1 r.2 then μ a else 0

/-- Count the boxes of a given size through a single lattice point.
Each lower and upper corner has at most (k+1)^d possible locations. -/
private theorem count_through {d} (a : Lattice d) (S : Finset (Box d)) (k : ℕ)
    (through : ∀ r ∈ S, a ∈ Finset.Icc r.1 r.2) (size : ∀ r ∈ S, sites r = k) :
    S.card ≤ (k+1)^(2*d) := by
  let L := Finset.Icc (fun i => a i - (k:ℤ)) a
  let U := Finset.Icc a (fun i => a i + (k:ℤ))
  have sub : S ⊆ L ×ˢ U := by
    intro r mem
    obtain ⟨left,right⟩ := Finset.mem_Icc.mp (through r mem)
    have span (i : Fin d) : r.2 i - r.1 i ≤ (k:ℤ) := by
      have ordered (j : Fin d) : r.1 j ≤ r.2 j := (left j).trans (right j)
      have pos (j : Fin d) : 1 ≤ (Finset.Icc (r.1 j) (r.2 j)).card := by
        rw [Int.card_Icc]; have := ordered j; omega
      have side := Finset.single_le_prod' (f := fun j => (Finset.Icc (r.1 j) (r.2 j)).card)
        (fun j _ => pos j) (Finset.mem_univ i)
      have eq := size r mem
      rw [sites,Pi.card_Icc] at eq
      rw [eq] at side
      change (Finset.Icc (r.1 i) (r.2 i)).card ≤ k at side
      rw [Int.card_Icc] at side
      omega
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨fun i => by
      have hs := span i; have hr : a i ≤ r.2 i := right i; dsimp; omega,left⟩,Finset.mem_Icc.mpr ⟨right,fun i => by
      have hs := span i; have hl : r.1 i ≤ a i := left i; dsimp; omega⟩⟩
  have lo : L.card = (k+1)^d := by
    dsimp only [L]
    rw [Pi.card_Icc]
    simp [Int.card_Icc,show ∀ i, a i + 1 - (a i - (k:ℤ)) = (k:ℤ)+1 by intro i; ring]
  have hi : U.card = (k+1)^d := by
    dsimp only [U]
    rw [Pi.card_Icc]
    simp [Int.card_Icc,show ∀ i, a i + k + 1 - a i = (k:ℤ)+1 by intro i; ring]
  simpa only [Finset.card_product,lo,hi,two_mul,pow_add] using Finset.card_le_card sub

private def price (d k : ℕ) : ℝ := 1 / (2 + (k:ℝ))^(2*d+2)

private theorem price_pos (d k : ℕ) : 0 < price d k := by unfold price; positivity

private theorem total_through {d} (a : Lattice d) (S : Finset (Box d)) :
    ∑ r ∈ S, (if a ∈ Finset.Icc r.1 r.2 then price d (sites r) else 0) ≤ 1 := by
  let T := S.filter (fun r => a ∈ Finset.Icc r.1 r.2)
  let n := T.sup sites + 1
  have upto : ∀ r ∈ T, sites r ∈ Finset.range n := fun r hr =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hr))
  have layer (k : ℕ) : (((T.filter (fun r => sites r = k)).card:ℝ) * price d k) ≤
      1 / ((k:ℝ)+1) - 1 / ((k:ℝ)+2) := by
    have card := count_through a (T.filter (fun r => sites r = k)) k
      (fun _ hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2)
      (fun _ hr => (Finset.mem_filter.mp hr).2)
    have bound : ((T.filter (fun r => sites r = k)).card:ℝ) ≤ (2+(k:ℝ))^(2*d) := by
      calc
        _ ≤ ((k:ℝ)+1)^(2*d) := by exact_mod_cast card
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) _
    apply (mul_le_mul_of_nonneg_right bound (price_pos d k).le).trans
    unfold price
    rw [pow_add]
    have pos : 0 < (2+(k:ℝ))^(2*d) := by positivity
    rw [show (2+(k:ℝ))^(2*d) * (1 / ((2+k)^(2*d)*(2+k)^2)) = 1 / (2+k)^2 by
      field_simp]
    have kp : 0 < (k:ℝ)+1 := by positivity
    have kp' : 0 < (k:ℝ)+2 := by positivity
    rw [add_comm 2 (k:ℝ)]
    field_simp
    nlinarith
  have telescopes (m : ℕ) :
      ∑ k ∈ Finset.range m, (1/((k:ℝ)+1) - 1/((k:ℝ)+2)) = 1-1/((m:ℝ)+1) := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [Finset.sum_range_succ,ih,Nat.cast_succ]; ring
  rw [← Finset.sum_filter]
  change ∑ r ∈ T, price d (sites r) ≤ 1
  rw [← Finset.sum_fiberwise_of_maps_to' upto]
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact (Finset.sum_le_sum (fun k _ => layer k)).trans (by rw [telescopes]; exact sub_le_self _ (by positivity))

private theorem total_weight {d} (A : Finset (Lattice d)) (μ : Lattice d → ℝ)
    (nonneg : ∀ a ∈ A, 0 ≤ μ a) (total : ∑ a ∈ A, μ a ≤ 1) (S : Finset (Box d)) :
    ∑ r ∈ S, anchorMass A μ r * price d (sites r) ≤ 1 := by
  simp only [anchorMass,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply le_trans (Finset.sum_le_sum ?_) total
  intro a ha
  have cap := mul_le_mul_of_nonneg_left (total_through a S) (nonneg a ha)
  rw [Finset.mul_sum,mul_one] at cap
  apply le_trans (le_of_eq (Finset.sum_congr rfl ?_)) cap
  intro r _
  split_ifs <;> ring

/-- A single strategy attains the P23 threshold on a whole packet if a
distribution of total weight at most one assigns each rectangle of N sites
mass at least (2+N)^(-p). Its constant depends only on d, q and p. -/
theorem logarithmic_of_anchor_mass {d} (e : ℕ → Lattice d) {q : ℝ} (hq : 0 < q)
    (small : q ≤ 1/2) (p : ℕ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (D : Finset ℕ) (S : Finset (Lattice d × Lattice d))
      (A : Finset (Lattice d)) (μ : Lattice d → ℝ),
      (∀ a ∈ A, 0 ≤ μ a) → ∑ a ∈ A, μ a ≤ 1 →
      (∀ r ∈ S, 1 ≤ (2 + ((Finset.Icc r.1 r.2).card:ℝ))^p * anchorMass A μ r) →
      ClaimGame.CanForce D (PacketQuota e q c 0 D S) := by
  let J := 2*d+3+p
  let c := max 1 (2*(J:ℝ)/q^2)
  refine ⟨c,le_max_left ..,?_⟩
  intro D S A μ nonneg total heavy
  let I := ↥S
  let E (i : I) := boardTrace e D i.val
  let w (i : I) := anchorMass A μ i.val * price d (sites i.val)
  have wp (i : I) : 0 < w i := by
    have mass := heavy i.val i.property
    have bpos : 0 < (2+((Finset.Icc i.val.1 i.val.2).card:ℝ))^p := by positivity
    have mp : 0 < anchorMass A μ i.val := by by_contra! hm; nlinarith [mul_nonpos_of_nonneg_of_nonpos bpos.le hm]
    exact mul_pos mp (price_pos ..)
  have wt : ∑ i, w i ≤ 1 := by
    change ∑ i : S, (fun r => anchorMass A μ r * price d (sites r)) i.val ≤ 1
    rw [Finset.sum_coe_sort S (fun r => anchorMass A μ r * price d (sites r))]
    exact total_weight A μ nonneg total S
  obtain ⟨move,safe,win⟩ := ClaimGame.weighted_tests D E (fun _ => Finset.filter_subset ..)
    w wp (half_pos hq) (show q/2 ≤ 1/2 by linarith)
  refine ⟨move,safe,fun h legal done r mem _ enough => ?_⟩
  let i : I := ⟨r,mem⟩
  let b := 2+(sites r:ℝ)
  have bp : 1 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α:=ℝ) (sites r)]
  have bpos : 0 < b := by linarith
  have weight : 1 ≤ b^(2*d+2+p)*w i := by
    have m := heavy r mem
    change 1 ≤ b^p * anchorMass A μ r at m
    change 1 ≤ b^(2*d+2+p) * (anchorMass A μ r * (1/b^(2*d+2)))
    convert m using 1
    rw [pow_add]
    field_simp
  have numerator : (1+q/2)*(∑ j, w j) ≤ b := by
    have bound := mul_le_mul_of_nonneg_left wt (show 0 ≤ 1+q/2 by linarith)
    dsimp [b]; linarith [Nat.cast_nonneg (α:=ℝ) (sites r)]
  have ratio : (1+q/2)*(∑ j, w j)/w i ≤ b^J := by
    apply (div_le_iff₀ (wp i)).mpr
    apply numerator.trans
    calc
      b = b*1 := (mul_one _).symm
      _ ≤ b*(b^(2*d+2+p)*w i) := mul_le_mul_of_nonneg_left weight bpos.le
      _ = b^J*w i := by rw [show J = (2*d+2+p)+1 by dsimp [J]; omega,pow_succ]; ring
  have sumpos : 0 < ∑ j, w j := (wp i).trans_le
    (Finset.single_le_sum (fun j _ => (wp j).le) (Finset.mem_univ i))
  have cost := Real.log_le_log (div_pos (mul_pos (by linarith) sumpos) (wp i)) ratio
  rw [Real.log_pow] at cost
  have hits := win h legal done i
  let m : ℝ := (E i).card
  change c * (log b)^(1+(0:ℝ)) ≤ m at enough
  simp only [add_zero,Real.rpow_one] at enough
  have pay : (J:ℝ)*log b ≤ (q/2*m)*q := by
    have low := (mul_le_mul_of_nonneg_right (le_max_right 1 (2*(J:ℝ)/q^2)) (Real.log_nonneg bp)).trans enough
    rw [div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hq)] at low
    nlinarith only [low]
  have charge : Real.log ((1+q/2)*(∑ j, w j)/w i)/(2*(q/2)) ≤ q/2*m := by
    rw [show 2*(q/2) = q by ring,div_le_iff₀ hq]
    exact cost.trans pay
  change (1/2-q/2)*m-_ ≤ _ at hits
  change (1/2-q)*m ≤ (((E i).filter (· ∈ earned move h)).card:ℝ)
  linarith only [charge,hits]

/-- The threshold is independent of the common point, the number of boxes,
their eccentricities, the number of scales and the population of the board. -/
theorem logarithmic_through_point {d} (e : ℕ → Lattice d) {q : ℝ} (hq : 0 < q)
    (small : q ≤ 1/2) : ∃ c : ℝ, 1 ≤ c ∧ ∀ (D : Finset ℕ)
      (S : Finset (Lattice d × Lattice d)) (a : Lattice d),
      (∀ r ∈ S, a ∈ Finset.Icc r.1 r.2) → ClaimGame.CanForce D (PacketQuota e q c 0 D S) := by
  obtain ⟨c,hc,works⟩ := logarithmic_of_anchor_mass e hq small 0
  refine ⟨c,hc,fun D S a through => works D S {a} (fun _ => 1) (by simp) (by simp) ?_⟩
  intro r mem
  simp only [pow_zero,one_mul,anchorMass,Finset.sum_singleton,if_pos (through r mem),le_refl]

/-- Independent groups of boxes may use different anchors. Only the traces
on the board have to stay in their assigned parts. The threshold does not
depend on the number of groups, their separation or their populations. -/
theorem logarithmic_on_separate_parts {d} {ι : Type*} (e : ℕ → Lattice d) {q : ℝ}
    (hq : 0 < q) (small : q ≤ 1/2) (p : ℕ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (D : Finset ℕ) (S : Finset (Lattice d × Lattice d))
      (part : ℕ → ι) (group : (Lattice d × Lattice d) → ι)
      (A : ι → Finset (Lattice d)) (μ : ι → Lattice d → ℝ),
      (∀ r ∈ S, ∀ x ∈ boardTrace e D r, part x = group r) →
      (∀ i a, a ∈ A i → 0 ≤ μ i a) → (∀ i, ∑ a ∈ A i, μ i a ≤ 1) →
      (∀ r ∈ S, 1 ≤ (2 + ((Finset.Icc r.1 r.2).card:ℝ))^p *
        anchorMass (A (group r)) (μ (group r)) r) →
      ClaimGame.CanForce D (PacketQuota e q c 0 D S) := by
  obtain ⟨c,hc,perGame⟩ := logarithmic_of_anchor_mass e hq small p
  refine ⟨c,hc,?_⟩
  intro D S part group A μ inside nonneg total heavy
  let boards (i : ι) := D.filter (fun x => part x = i)
  let tests (i : ι) := S.filter (fun r => group r = i)
  have games (i : ι) : ClaimGame.CanForce (boards i) (PacketQuota e q c 0 (boards i) (tests i)) := by
    apply perGame _ _ (A i) (μ i) (nonneg i) (total i)
    intro r hr
    obtain ⟨mem,eq⟩ := Finset.mem_filter.mp hr
    simpa only [← eq] using heavy r mem
  obtain ⟨move,safe,win⟩ := ClaimGame.canForce_partition D part _ games
  refine ⟨move,safe,fun h legal done r mem wide enough => ?_⟩
  let i := group r
  have same : boardTrace e (boards i) r = boardTrace e D r := by
    ext x
    simp only [boardTrace,boards,Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,inside r mem x (Finset.mem_filter.mpr h)⟩,h.2⟩⟩
  have localWin := win h legal done i r (Finset.mem_filter.mpr ⟨mem,rfl⟩) wide
  have sameTrace : LogPowerCriterion.trace e (boards i) r = LogPowerCriterion.trace e D r := same
  dsimp only at localWin
  rw [sameTrace] at localWin
  apply (localWin enough).trans
  have mono (X : Finset ℕ) (U W : Set ℕ) (sub : U ⊆ W) :
      ((X.filter (· ∈ U)).card:ℝ) ≤ (X.filter (· ∈ W)).card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.monotone_filter_right _ fun _ => @sub _))
  exact mono _ _ _ Set.inter_subset_left

end
end GenLimit.KleinbergWei.Banach.AnchorPackets
