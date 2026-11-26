import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleLanguage
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Prod

/-! Interpolating rectangular counts. When every coordinate projection is
injective on a target, expanding all sides of a rectangle by one lattice
unit adds at most two points per dimension. An empty rectangle with many
target words can therefore be enlarged to contain an arbitrarily large but
controlled number of outputs. This accounts for the numerator-growth filter
in the detailed display of P23 Theorem 5.1. -/
namespace GenLimit.KleinbergWei.Banach.Rectangles
open Set
open scoped Classical ENNReal
noncomputable section

private def low {d} (l : Lattice d) (r : ℕ) : Lattice d := fun i => l i-r
private def high {d} (u : Lattice d) (r : ℕ) : Lattice d := fun i => u i+r
private def grow {d} (S : Set (Lattice d)) (l u : Lattice d) (r : ℕ) :=
  box S (low l r) (high u r)

private theorem grow_mono {d} (S : Set (Lattice d)) (l u : Lattice d) :
    Monotone (grow S l u) := by
  intro a b le x hx
  obtain ⟨⟨lb,ub⟩,mem⟩ := mem_box.mp hx
  refine mem_box.mpr ⟨⟨fun i => ?_,fun i => ?_⟩,mem⟩
  · have h := lb i; simp only [low] at *; omega
  · have h := ub i; simp only [high] at *; omega

@[simp] private theorem grow_zero {d} (S : Set (Lattice d)) (l u : Lattice d) :
    grow S l u 0 = box S l u := by
  have hl : low l 0 = l := by funext i; simp [low]
  have hu : high u 0 = u := by funext i; simp [high]
  rw [grow,hl,hu]

private theorem eventually_many {d} (S : Set (Lattice d)) (inf : S.Infinite) (l u : Lattice d) (n : ℕ) :
    ∃ r, n ≤ (grow S l u r).card := by
  obtain ⟨T,inS,card⟩ := inf.exists_subset_card_eq n
  let dist (x : Lattice d) (i : Fin d) := max (l i-x i).toNat (x i-u i).toNat
  let rad (x : Lattice d) := Finset.univ.sup (dist x)
  refine ⟨T.sup rad,card ▸ Finset.card_le_card ?_⟩
  intro x hx
  have bound (i : Fin d) : dist x i ≤ T.sup rad :=
    (Finset.le_sup (s:=Finset.univ) (f:=dist x) (Finset.mem_univ i)).trans (Finset.le_sup (f:=rad) hx)
  refine mem_box.mpr ⟨⟨fun i => ?_,fun i => ?_⟩,inS hx⟩
  · have h := (le_max_left ..).trans (bound i); dsimp [low]; omega
  · have h := (le_max_right ..).trans (bound i); dsimp [high]; omega

private theorem step_size {d} (S : Set (Lattice d)) (thinS : ∀ i : Fin d, InjOn (fun x => x i) S)
    (l u : Lattice d) (r : ℕ) : (grow S l u (r+1)).card ≤ (grow S l u r).card + 2*d := by
  let fresh := grow S l u (r+1) \ grow S l u r
  let edge (p : Fin d × Bool) : ℤ := if p.2 then high u (r+1) p.1 else low l (r+1) p.1
  have onEdge (x : fresh) : ∃ p : Fin d × Bool, x.val p.1 = edge p := by
    obtain ⟨new,old⟩ := Finset.mem_sdiff.mp x.property
    obtain ⟨⟨lb,ub⟩,mem⟩ := mem_box.mp new
    by_contra! none
    apply old; apply mem_box.mpr
    refine ⟨⟨fun i => ?_,fun i => ?_⟩,mem⟩
    · have ne := none (i,false); have h := lb i
      simp only [edge,Bool.false_eq_true,if_false,low,Nat.cast_add,Nat.cast_one] at *
      omega
    · have ne := none (i,true); have h := ub i
      simp only [edge,if_true,high,Nat.cast_add,Nat.cast_one] at *
      omega
  let label (x : fresh) := (onEdge x).choose
  have inj : Function.Injective label := by
    intro x y eq
    apply Subtype.ext
    have Hx := (onEdge x).choose_spec
    have Hy := (onEdge y).choose_spec
    change x.val (label x).1 = edge (label x) at Hx
    change y.val (label y).1 = edge (label y) at Hy
    rw [←eq] at Hy
    exact thinS (label x).1 (mem_box.mp (Finset.mem_sdiff.mp x.property).1).2
      (mem_box.mp (Finset.mem_sdiff.mp y.property).1).2 (Hx.trans Hy.symm)
  have card : fresh.card ≤ d*2 := by simpa using Fintype.card_le_of_injective label inj
  have count := Finset.card_sdiff_add_card_eq_card (grow_mono S l u (Nat.le_succ r))
  change fresh.card + (grow S l u r).card = (grow S l u (r+1)).card at count
  omega

/-- Same ratio as Definition 1.1 with the threshold imposed on the
number of generated target words, as printed in Section 5. -/
def outputThresholdDensity {d} (O K : Set (Lattice d)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ r : {r : Lattice d × Lattice d // n ≤ (box (O ∩ K) r.1 r.2).card},
    ((box (O ∩ K) r.val.1 r.val.2).card : ℝ≥0∞) / (box K r.val.1 r.val.2).card

theorem interpolate {d} (O K : Set (Lattice d)) (inf : (O ∩ K).Infinite)
    (thinK : ∀ i : Fin d, InjOn (fun x => x i) K)
    (holes : ∀ n, ∃ l u, n ≤ (box K l u).card ∧ ∀ x ∈ box K l u, x ∉ O) :
    outputThresholdDensity O K = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le; intro n
  by_contra! positive
  let V : ℝ≥0∞ := ⨅ r : {r : Lattice d × Lattice d // n ≤ (box (O ∩ K) r.1 r.2).card},
    ((box (O ∩ K) r.val.1 r.val.2).card : ℝ≥0∞) / (box K r.val.1 r.val.2).card
  change 0 < V at positive
  let cap := n+1+2*d
  obtain ⟨m,_,small⟩ := ENNReal.exists_nat_pos_inv_mul_lt (a:=(cap:ℝ≥0∞)) (by simp) positive.ne'
  obtain ⟨l,u,large,empty⟩ := holes m
  let S := O ∩ K
  have zero : grow S l u 0 = ∅ := by
    rw [grow_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨bd,mem,inside⟩ := mem_box.mp hx
    exact empty _ (mem_box.mpr ⟨bd,inside⟩) mem
  obtain any := eventually_many S inf l u (n+1)
  let r := Nat.find any
  have reached : n+1 ≤ (grow S l u r).card := Nat.find_spec any
  have upper : (grow S l u r).card ≤ cap := by
    cases hr : r with
    | zero => rw [hr,zero] at reached; simp at reached
    | succ t =>
      have before := Nat.find_min any (show t < r by omega)
      have step := step_size S (fun i => (thinK i).mono inter_subset_right) l u t
      dsimp only [cap]; omega
  have coverage := Finset.card_le_card (grow_mono K l u (Nat.zero_le r))
  rw [grow_zero] at coverage
  have minD : m ≤ (grow K l u r).card := large.trans coverage
  let R : {r : Lattice d × Lattice d // n ≤ (box (O ∩ K) r.1 r.2).card} :=
    ⟨(low l r,high u r),(Nat.le_succ n).trans reached⟩
  have bound : V ≤ (↑(grow S l u r).card : ℝ≥0∞) / (grow K l u r).card := iInf_le _ R
  have estimate : (↑(grow S l u r).card : ℝ≥0∞) / (grow K l u r).card ≤
      (m : ℝ≥0∞)⁻¹ * (cap : ℝ≥0∞) := by
    rw [ENNReal.div_eq_inv_mul]
    exact mul_le_mul' (ENNReal.inv_le_inv.mpr (by exact_mod_cast minD)) (by exact_mod_cast upper)
  exact (lt_irrefl V) ((bound.trans estimate).trans_lt small)

end
end GenLimit.KleinbergWei.Banach.Rectangles
