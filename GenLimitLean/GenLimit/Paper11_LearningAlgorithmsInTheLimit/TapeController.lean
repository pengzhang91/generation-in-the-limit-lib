import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TuringMachines
import Mathlib.Computability.Tape
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Fold

/-! # Compiling finite controllers with an integer-indexed tape

Quotienting the two finite side lists by trailing blanks gives the usual
two-sided tape. Each controller transition compiles to one paper-machine
transition, including the time spent writing, moving and halting. -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open Turing
open scoped Classical

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Encodable Γ]
variable {Q : Type} [Fintype Q]

abbrev Rule (Γ Q : Type) := Q → Γ → Option Q × Γ × TuringHeadMove
abbrev Config (Γ Q : Type) [Inhabited Γ] := Option Q × Tape Γ

def view (t : TuringTape Γ) : Tape Γ := ⟨t.scanned,ListBlank.mk t.left,ListBlank.mk t.right⟩

def perform (t : Tape Γ) (w : Γ) (d : TuringHeadMove) : Tape Γ :=
  match d with
  | .stay => t.write w
  | .left => (t.write w).move .left
  | .right => (t.write w).move .right

theorem view_move (t : TuringTape Γ) (w : Γ) (d : TuringHeadMove) :
    view (t.writeAndMove default w d) = perform (view t) w d := by
  rcases t with ⟨l,a,r⟩
  cases d <;> cases l <;> cases r <;> rfl

def tick (δ : Rule Γ Q) : Config Γ Q → Config Γ Q
  | (none,t) => (none,t)
  | (some q,t) => let a := δ q t.head; (a.1,perform t a.2.1 a.2.2)

noncomputable def tag (start : Q) : Option Q → ℕ
  | none => 0
  | some q => if q = start then 1 else (Fintype.equivFin Q q).val + 2

private theorem tag_ne_zero (start q : Q) : tag start (some q) ≠ 0 := by
  classical
  simp only [tag]
  split <;> omega

theorem tag_le (start : Q) (q : Option Q) : tag start q ≤ Fintype.card Q + 1 := by
  cases q with
  | none => exact Nat.zero_le _
  | some q =>
    have := (Fintype.equivFin Q q).isLt
    simp only [tag]
    split <;> omega

private theorem tag_inj (start : Q) : Function.Injective (fun q ↦ tag start (some q)) := by
  classical
  intro x y he
  by_cases hx : x = start <;> by_cases hy : y = start
  · exact hx.trans hy.symm
  · simp [tag,hx,hy] at he
  · simp [tag,hx,hy] at he
  · exact (Fintype.equivFin Q).injective (Fin.ext (by simpa [tag,hx,hy] using he))

def maxSymbol (Γ : Type) [Fintype Γ] [Encodable Γ] := Finset.univ.sup (@Encodable.encode Γ _)

def tableSize (Γ : Type) [Fintype Γ] [Encodable Γ] (k : ℕ) := Nat.pair (k+1) (maxSymbol Γ) + 1

theorem pair_mono {p q a b : ℕ} (hp : p ≤ q) (ha : a ≤ b) : Nat.pair p a ≤ Nat.pair q b :=
  ((strictMono_nat_of_lt_succ (fun x ↦ Nat.pair_lt_pair_left a (Nat.lt_succ_self x))).monotone hp).trans
    ((strictMono_nat_of_lt_succ (fun x ↦ Nat.pair_lt_pair_right q (Nat.lt_succ_self x))).monotone ha)

private noncomputable def row (δ : Rule Γ Q) (start : Q) (key : ℕ) : TuringInstruction Γ :=
  letI : Nonempty Q := ⟨start⟩
  let q := Function.invFun (fun q ↦ tag start (some q)) key.unpair.1
  let a := (Encodable.decode key.unpair.2).getD (default : Γ)
  let v := δ q a
  (tag start v.1,v.2)

noncomputable def program (δ : Rule Γ Q) (start : Q) : TuringProgram Γ :=
  (List.range (tableSize Γ (Fintype.card Q))).map (row δ start)

theorem program_length (δ : Rule Γ Q) (start : Q) :
    (program δ start).length = tableSize Γ (Fintype.card Q) := by simp [program]

theorem program_state_bound (δ : Rule Γ Q) (start : Q) {act} (h : act ∈ program δ start) :
    act.1 ≤ Fintype.card Q + 1 := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
  exact tag_le _ _

theorem program_step (δ : Rule Γ Q) (start q : Q) (a : Γ) :
    (program δ start).instruction (tag start (some q)) a = (tag start (δ q a).1,(δ q a).2) := by
  classical
  letI : Nonempty Q := ⟨start⟩
  let k := Nat.pair (tag start (some q)) (Encodable.encode a)
  have hk : k < tableSize Γ (Fintype.card Q) := Nat.lt_succ_of_le
    (pair_mono (tag_le ..) (Finset.le_sup (f := @Encodable.encode Γ _) (Finset.mem_univ a)))
  have hr : (List.range (tableSize Γ (Fintype.card Q)))[k]? = some k := by
    rw [List.getElem?_eq_getElem (by simpa using hk)]; simp
  unfold TuringProgram.instruction program
  change (((List.range _).map (row δ start))[k]?).getD _ = _
  rw [List.getElem?_map,hr]
  have inv : Function.invFun (fun v ↦ tag start (some v)) (tag start (some q)) = q :=
    Function.leftInverse_invFun (tag_inj start) q
  simp [row,k,Nat.unpair_pair,inv]

def represents (start : Q) (c : TuringConfiguration Γ) (z : Config Γ Q) :=
  c.state = tag start z.1 ∧ view c.tape = z.2

theorem run_represents (δ : Rule Γ Q) (start : Q) (n : ℕ) {c z} (h : represents start c z) :
    represents start ((program δ start).runConfiguration default n c) ((tick δ)^[n] z) := by
  induction n generalizing c z with
  | zero => exact h
  | succ n ih =>
    rcases z with ⟨q,t⟩
    rcases h with ⟨hc,ht⟩
    cases q with
    | none =>
      have hz : c.state = 0 := hc
      have hfixed : (tick δ)^[n+1] (none,t) = (none,t) :=
        Function.iterate_fixed (show tick δ (none,t) = (none,t) from rfl) _
      simpa [TuringProgram.runConfiguration,TuringProgram.step,hz,hfixed,represents,tag] using ht
    | some q =>
      rw [Function.iterate_succ_apply]
      simp only [TuringProgram.runConfiguration,TuringProgram.step,hc,if_neg (tag_ne_zero start q)]
      apply ih
      have ha : c.tape.scanned = t.head := congrArg Tape.head ht
      simp [represents,tick,program_step,view_move,ht,ha]

end GenLimit.LearningAlgorithmsLimit.NativeTape
