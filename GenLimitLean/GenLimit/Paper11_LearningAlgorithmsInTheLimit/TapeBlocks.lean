import Mathlib.Computability.TMToPartrec
import Mathlib.Computability.TuringMachine
import Mathlib.Data.Fintype.EquivFin

/-! # Fixed-width binary blocks for the single-tape universal machine

The leading bit distinguishes a nonblank logical cell from blank space.
Thus a finite-state postprocessor can turn the final logical word into
one contiguous unary word on any alphabet with a nonblank symbol. -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open Turing PartrecToTM2

instance : Fintype K' := Fintype.ofList [.main,.rev,.aux,.stack] (by intro k; cases k <;> simp)

abbrev Cell := TM2to1.Γ' K' (fun _ ↦ Γ')
noncomputable instance : DecidableEq Cell := Classical.decEq _

noncomputable def block {A : Type} [Fintype A] [Inhabited A] [DecidableEq A] (a : A) :
    List.Vector Bool (Fintype.card A + 1) :=
  List.Vector.ofFn fun i ↦ decide (a ≠ default ∧ (i.val = 0 ∨ i.val = (Fintype.equivFin A a).val + 1))

theorem blank_block {A : Type} [Fintype A] [Inhabited A] [DecidableEq A] :
    block (default : A) = List.Vector.replicate _ false := by
  apply List.Vector.ext
  intro i
  rw [List.Vector.get_replicate]
  simp [block]

theorem block_head {A : Type} [Fintype A] [Inhabited A] [DecidableEq A] {a : A} (ha : a ≠ default) :
    (block a).head = true := by simp [block,ha]

theorem block_injective {A : Type} [Fintype A] [Inhabited A] [DecidableEq A] :
    Function.Injective (block (A := A)) := by
  intro a b he
  by_cases ha : a = default
  · subst a
    by_contra hb
    have ht := congrArg List.Vector.head he
    simp [block,Ne.symm hb] at ht
  · let i := Fintype.equivFin A a
    let j : Fin (Fintype.card A+1) := ⟨i.val+1,by have := i.isLt; omega⟩
    have h := congrArg (fun v : List.Vector Bool (Fintype.card A+1) ↦ v.get j) he
    simp [block,j,i,ha] at h
    exact (Fintype.equivFin A).injective (Fin.ext h.2)

noncomputable def unblock {A : Type} [Fintype A] [Inhabited A] [DecidableEq A]
    (v : List.Vector Bool (Fintype.card A + 1)) : A := Function.invFun block v

theorem unblock_block {A : Type} [Fintype A] [Inhabited A] [DecidableEq A] (a : A) :
    unblock (block a) = a := Function.leftInverse_invFun block_injective _

def logical (n : ℕ) : List Cell := TM2to1.trInit K'.main (trList [n])

private theorem logical_mem {n} {a : Cell} (ha : a ∈ logical n) : a ≠ default := by
  let values := (trList [n]).reverse
  let cell (x : Γ') : Cell := (false,Function.update (fun _ ↦ none) K'.main (some x))
  change a ∈ (true,((values.map cell).headI).2) :: (values.map cell).tail at ha
  rcases List.mem_cons.mp ha with rfl | ht
  · exact fun e ↦ Bool.noConfusion (congrArg Prod.fst e)
  · have hm := List.mem_of_mem_tail ht
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hm
    intro h
    have he := congrArg (fun c : Cell ↦ c.2 K'.main) h
    simpa [cell] using he

theorem logical_length (n : ℕ) : (logical n).length = (trNat n).length + 1 := by
  simp [logical,TM2to1.trInit]

private theorem pos_length (p : PosNum) : (trPosNum p).length ≤ (p : ℕ) := by
  induction p with
  | one => decide
  | bit0 p ih =>
    simp only [trPosNum,List.length_cons,PosNum.cast_bit0]
    have := PosNum.to_nat_pos p
    omega
  | bit1 p ih =>
    simp only [trPosNum,List.length_cons,PosNum.cast_bit1]
    omega

theorem logical_length_le (n : ℕ) : (logical n).length ≤ n + 1 := by
  rw [logical_length]
  apply Nat.add_le_add_right
  have h (m : Num) : (trNum m).length ≤ (m : ℕ) := by
    cases m with
    | zero => decide
    | pos p => exact pos_length p
  simpa [trNat] using h (n : Num)

private def doubleBits : ℕ → PosNum
  | 0 => .one
  | n+1 => .bit0 (doubleBits n)

private theorem doubleBits_value (n : ℕ) : (doubleBits n : ℕ) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [doubleBits,PosNum.cast_bit0,ih,pow_succ,Nat.mul_two]

theorem logical_length_pow (n : ℕ) : n ≤ (logical (2^n)).length := by
  have he : ((2^n : ℕ) : Num) = Num.pos (doubleBits n) := by
    apply Num.toNat_injective
    change (((2^n : ℕ) : Num) : ℕ) = (doubleBits n : ℕ)
    rw [Num.to_of_nat,doubleBits_value]
  have h : (trPosNum (doubleBits n)).length = n + 1 := by
    clear he
    induction n with
    | zero => rfl
    | succ n ih => simp [doubleBits,trPosNum,ih]
  rw [logical_length,trNat,he]
  change n ≤ (trPosNum (doubleBits n)).length + 1
  omega

noncomputable def chunks (n : ℕ) : List (List Bool) := (logical n).map (fun a ↦ (block a).toList)

private theorem vec_head (v : List.Vector Bool (m+1)) : v.toList.head? = some v.head := by
  rw [← v.cons_head_tail]
  rfl

theorem chunks_spec {n : ℕ} {b : List Bool} (hb : b ∈ chunks n) :
    b.length = Fintype.card Cell + 1 ∧ b.head? = some true := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  refine ⟨List.Vector.toList_length _,?_⟩
  exact (vec_head _).trans (congrArg some (block_head (logical_mem ha)))

end GenLimit.LearningAlgorithmsLimit.NativeTape
