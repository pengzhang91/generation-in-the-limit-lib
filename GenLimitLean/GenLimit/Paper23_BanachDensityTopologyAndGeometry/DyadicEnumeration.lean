import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LatticeTiles
import Mathlib.Algebra.BigOperators.Fin

/-! Interleave binary digits of the nonnegative lattice coordinates. Aligned
blocks of codes map onto whole lattice cubes, independently of the block
position and its scale. -/
namespace GenLimit.KleinbergWei.Banach.DyadicEnumeration
open Finset
open scoped Classical
noncomputable section

private abbrev base (d : ℕ) := 2^(d+1)
private theorem large (d : ℕ) : 1 < base d := by
  unfold base
  rw [pow_succ]
  have h : 0 < 2^d := by positivity
  omega

private def bits (d n : ℕ) : Fin (d+1) → Fin 2 :=
  finFunctionFinEquiv.symm ⟨n % base d,Nat.mod_lt _ (by positivity : 0 < 2^(d+1))⟩

private theorem zero_bits (d : ℕ) : bits d 0 = 0 := by
  have eq : finFunctionFinEquiv (0 : Fin (d+1) → Fin 2) = 0 := by
    apply Fin.ext; simp
  apply finFunctionFinEquiv.injective
  simp [bits,eq]

private def coordinate (d n : ℕ) : Fin (d+1) → ℕ :=
  if h : n = 0 then 0 else fun i => 2*coordinate d (n/base d) i+(bits d n i).val
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (large d)

private theorem step (d n : ℕ) (i : Fin (d+1)) :
    coordinate d n i = 2*coordinate d (n/base d) i+(bits d n i).val := by
  by_cases h : n = 0
  · subst n; simp [coordinate,zero_bits]
  · conv_lhs => rw [coordinate]
    simp [h]

private theorem quotient (d n : ℕ) (i : Fin (d+1)) : coordinate d n i/2 = coordinate d (n/base d) i := by
  rw [step d n i]; have := (bits d n i).isLt; omega

private theorem residue (d n : ℕ) (i : Fin (d+1)) : coordinate d n i%2 = (bits d n i).val := by
  rw [step d n i]; have := (bits d n i).isLt; omega

private theorem coord_inj (d n m : ℕ) (eq : coordinate d n = coordinate d m) : n = m := by
  by_cases zero : n = 0 ∧ m = 0
  · omega
  have next : coordinate d (n/base d) = coordinate d (m/base d) := by
    funext i; rw [←quotient,←quotient,eq]
  have same_bits : bits d n = bits d m := by
    funext i; apply Fin.ext; rw [←residue,←residue,eq]
  have remainders : n%base d = m%base d := by
    exact congrArg Fin.val (finFunctionFinEquiv.symm.injective same_bits)
  have earlier := coord_inj d (n/base d) (m/base d) next
  have a := Nat.div_add_mod n (base d)
  have b := Nat.div_add_mod m (base d)
  rw [earlier,remainders] at a
  exact a.symm.trans b
termination_by n+m
decreasing_by
  have hn := Nat.div_le_self n (base d)
  have hm := Nat.div_le_self m (base d)
  by_cases h : n = 0
  · have := Nat.div_lt_self (by omega : 0 < m) (large d); omega
  · have := Nat.div_lt_self (by omega : 0 < n) (large d); omega

def point (d n : ℕ) : Lattice (d+1) := fun i => (coordinate d n i : ℤ)

theorem point_injective (d : ℕ) : Function.Injective (point d) := by
  intro n m h
  apply coord_inj d n m
  funext i
  have hh : (coordinate d n i:ℤ) = (coordinate d m i:ℤ) := congrFun h i
  exact_mod_cast hh

private theorem high_bits (d n k : ℕ) (i : Fin (d+1)) :
    coordinate d n i/2^k = coordinate d (n/(base d)^k) i := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,pow_succ,mul_comm (2^k),mul_comm ((base d)^k),←Nat.div_div_eq_div_mul,
      ←Nat.div_div_eq_div_mul,quotient,ih]

def lower (d b k : ℕ) : Lattice (d+1) := fun i => ((2^k*coordinate d b i:ℕ):ℤ)
def upper (d b k : ℕ) : Lattice (d+1) := fun i => lower d b k i + (2^k:ℕ) - 1

/-- Every code block at scale k enumerates an entire cube of 2ᵏ sites
on each side. No assumption on the starting tile is required. -/
theorem block_image (d b k : ℕ) :
    (Finset.Ico (b*(2^(d+1))^k) ((b+1)*(2^(d+1))^k)).image (point d) =
    Finset.Icc (lower d b k) (upper d b k) := by
  let B := (base d)^k
  let L := 2^k
  have bp : 0 < B := by dsimp [B,base]; positivity
  have lp : 0 < L := by dsimp [L]; positivity
  have sub : (Finset.Ico (b*B) ((b+1)*B)).image (point d) ⊆
      Finset.Icc (lower d b k) (upper d b k) := by
    intro x hx
    obtain ⟨n,inBlock,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨low,high⟩ := Finset.mem_Ico.mp inBlock
    have group : n/B = b := le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul bp).mpr high))
      ((Nat.le_div_iff_mul_le bp).mpr low)
    have bounds (i : Fin (d+1)) : L*coordinate d b i ≤ coordinate d n i ∧
        coordinate d n i < L*coordinate d b i+L := by
      have h : coordinate d n i/L = coordinate d b i := (high_bits d n k i).trans (congrArg (fun t => coordinate d t i) group)
      have lb := (Nat.le_div_iff_mul_le lp).mp h.ge
      have ub := (Nat.div_lt_iff_lt_mul lp).mp (h.trans_lt (Nat.lt_succ_self _))
      simpa [mul_comm,Nat.succ_mul] using And.intro lb ub
    apply Finset.mem_Icc.mpr
    constructor <;> intro i
    · change ((L*coordinate d b i:ℕ):ℤ) ≤ (coordinate d n i:ℤ)
      exact_mod_cast (bounds i).1
    · have h := (bounds i).2
      change (coordinate d n i:ℤ) ≤ ((L*coordinate d b i:ℕ):ℤ) + (L:ℤ)-1
      omega
  apply Finset.eq_of_subset_of_card_le sub
  rw [Finset.card_image_of_injective _ (point_injective d),Nat.card_Ico,Pi.card_Icc]
  have axis (i : Fin (d+1)) : (Finset.Icc (lower d b k i) (upper d b k i)).card = L := by
    rw [Int.card_Icc]; dsimp only [upper]; change (_ + (L:ℤ) - 1 + 1 - _).toNat = L; omega
  simp only [axis,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Nat.succ_mul,Nat.add_sub_cancel_left]
  exact le_of_eq (by dsimp [L,B,base]; rw [←pow_mul,←pow_mul,Nat.mul_comm k])

end
end GenLimit.KleinbergWei.Banach.DyadicEnumeration
