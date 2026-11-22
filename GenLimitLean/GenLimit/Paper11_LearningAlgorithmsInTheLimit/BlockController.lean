import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TapeController
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.UniversalTape

/-! # Erasing the input, loading a fixed binary word, and printing unary output -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open Turing
open scoped Classical

inductive Phase (Q : Type) (m w : ℕ)
  | erase
  | load (remaining : Fin (m+1))
  | simulate (state : Q)
  | inspect
  | fill (remaining : Fin (w+1))
  deriving Fintype

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ]

def bitSymbol (o : Γ) : Bool → Γ | false => default | true => o
def bitMap (o : Γ) : PointedMap Bool Γ := ⟨bitSymbol o,rfl⟩
def bitRead (v : Γ) : Bool := decide (v ≠ default)

private theorem read_bit {o : Γ} (ho : o ≠ default) (b : Bool) : bitRead (bitSymbol o b) = b := by
  cases b <;> simp [bitRead,bitSymbol,ho]

abbrev Control (U : BinaryMachine) (word : List Bool) (w : ℕ) := Phase ↥U.states word.length w

def rule (o : Γ) (U : BinaryMachine) (word : List Bool) (w : ℕ) : Rule Γ (Control U word w)
  | .erase, a => if a = default then (some (.load ⟨word.length,by omega⟩),default,.stay)
                 else (some .erase,default,.right)
  | .load j, a => if h : j.val = 0 then (some (.simulate ⟨_,U.supports.1⟩),a,.right)
                   else (some (.load ⟨j.val-1,by have := j.isLt; omega⟩),
                     bitSymbol o (word[j.val-1]'(by have := j.isLt; omega)),.left)
  | .simulate q, a =>
    match h : U.program q.val (bitRead a) with
    | none => (some .inspect,a,.stay)
    | some (q',v) =>
      let nq : ↥U.states := ⟨q',U.supports.2 h q.property⟩
      match v with
      | .move .left => (some (.simulate nq),a,.left)
      | .move .right => (some (.simulate nq),a,.right)
      | .write b => (some (.simulate nq),bitSymbol o b,.stay)
  | .inspect,a => if a = default then (none,default,.stay)
                  else (some (.fill ⟨w,by omega⟩),o,.right)
  | .fill j,a => if j.val = 0 then (some .inspect,a,.stay)
                 else (some (.fill ⟨j.val-1,by have := j.isLt; omega⟩),o,.right)

theorem control_card (U : BinaryMachine) (l : List Bool) (w : ℕ) :
    Fintype.card (Control U l w) = U.states.card + l.length + w + 4 := by
  change Fintype.card (Phase ↥U.states l.length w) = _
  let e : Phase ↥U.states l.length w ≃ Unit ⊕ Fin (l.length+1) ⊕ ↥U.states ⊕ Unit ⊕ Fin (w+1) :=
    ⟨fun q ↦ match q with
      | .erase => .inl ()
      | .load j => .inr (.inl j)
      | .simulate q => .inr (.inr (.inl q))
      | .inspect => .inr (.inr (.inr (.inl ())))
      | .fill j => .inr (.inr (.inr (.inr j))),
     fun v ↦ match v with
      | .inl _ => .erase
      | .inr (.inl j) => .load j
      | .inr (.inr (.inl q)) => .simulate q
      | .inr (.inr (.inr (.inl _))) => .inspect
      | .inr (.inr (.inr (.inr j))) => .fill j,
     by intro q; cases q <;> rfl,by rintro (⟨⟩ | j | q | ⟨⟩ | j) <;> rfl⟩
  rw [Fintype.card_congr e]
  simp
  omega

private theorem mk_blank : ListBlank.mk [(default : Γ)] = ListBlank.mk [] := by
  apply Quotient.sound
  exact Or.inr ⟨1,rfl⟩

private theorem erase_cell {a : Γ} (r : List Γ) :
    perform (Tape.mk₁ (a::r)) default .right = Tape.mk₁ r := by
  change Tape.mk₂ [default] r = Tape.mk₂ [] r
  unfold Tape.mk₂
  rw [mk_blank]

variable (o : Γ) (U : BinaryMachine) (word : List Bool) (w : ℕ)
local notation "δ" => rule o U word w

theorem erase_run (input : List Γ) (hi : ∀ a ∈ input, a ≠ default) :
    (tick δ)^[input.length+1] (some .erase,Tape.mk₁ input) =
      (some (.load ⟨word.length,by omega⟩),Tape.mk₁ []) := by
  induction input with
  | nil =>
    change tick δ (some .erase,Tape.mk₁ []) = _
    have hh : (Tape.mk₁ ([] : List Γ)).head = default := rfl
    simp [tick,rule,hh,perform,Tape.write]
    rfl
  | cons a l ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have ha := hi a List.mem_cons_self
    have hstep : tick δ (some .erase,Tape.mk₁ (a::l)) = (some .erase,Tape.mk₁ l) := by
      have hh : (Tape.mk₁ (a::l)).head = a := rfl
      simp only [tick,rule,hh,if_neg ha,erase_cell]
    apply Eq.trans (congrArg ((tick δ)^[l.length+1]) hstep)
    exact ih (fun a ha ↦ hi a (List.mem_cons_of_mem _ ha))

private theorem load_again (b : Γ) (r : List Γ) :
    perform (Tape.mk₁ (default::r)) b .left = Tape.mk₁ (default::b::r) := rfl

private theorem enter (r : List Γ) :
    perform (Tape.mk₁ (default::r)) default .right = Tape.mk₁ r := erase_cell r

private theorem load_run (j : ℕ) (hj : j ≤ word.length) :
    (tick δ)^[j+1] (some (.load ⟨j,by omega⟩),Tape.mk₁ (default :: (word.drop j).map (bitSymbol o))) =
      (some (.simulate ⟨_,U.supports.1⟩),Tape.mk₁ (word.map (bitSymbol o))) := by
  induction j with
  | zero =>
    rw [Function.iterate_one]
    have hh (r : List Γ) : (Tape.mk₁ (default::r)).head = default := rfl
    simp [tick,rule,hh,enter]
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    have h := ih (by omega)
    apply Eq.trans _ h
    apply congrArg ((tick δ)^[j+1])
    simp only [tick,rule,Fin.val_mk,Nat.succ_ne_zero,↓reduceDIte,Nat.add_sub_cancel]
    rw [load_again,← List.getElem_cons_drop (l := word) (i := j) (by omega)]
    rfl

theorem preload :
    ∃ n, (tick δ)^[n] (some (.load ⟨word.length,by omega⟩),Tape.mk₁ []) =
      (some (.simulate ⟨_,U.supports.1⟩),Tape.mk₁ (word.map (bitSymbol o))) := by
  refine ⟨word.length+1,?_⟩
  have hn : Tape.mk₁ ([] : List Γ) = Tape.mk₁ [default] := by
    unfold Tape.mk₁ Tape.mk₂
    rw [mk_blank]
  simpa [hn] using load_run o U word w word.length le_rfl

end GenLimit.LearningAlgorithmsLimit.NativeTape
