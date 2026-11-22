import GenLimit.Paper11_LearningAlgorithmsInTheLimit.WordTape
import Mathlib.Computability.Partrec

/-! # Effective transition-table syntax and bounded execution on word inputs

An optional bit encodes exactly the three possible head moves. The recursive
interpreter below agrees step for step with the native finite transition table. -/
namespace GenLimit.LearningAlgorithmsLimit.EffectiveTable
open NativeTape

abbrev Table (Γ : Type) := List (ℕ × Γ × Option Bool)
abbrev Conf (Γ : Type) := ℕ × List Γ × Γ × List Γ

def direction : TuringHeadMove → Option Bool
  | .left => some false | .right => some true | .stay => none

def movement : Option Bool → TuringHeadMove
  | some false => .left | some true => .right | none => .stay

def pack (P : TuringProgram Γ) : Table Γ := P.map fun v ↦ (v.1,v.2.1,direction v.2.2)
def unpack (T : Table Γ) : TuringProgram Γ := T.map fun v ↦ (v.1,v.2.1,movement v.2.2)

@[simp] theorem unpack_pack (P : TuringProgram Γ) : unpack (pack P) = P := by
  induction P with
  | nil => rfl
  | cons v t ih => obtain ⟨q,a,d⟩ := v; cases d <;> simp [pack,unpack,movement,direction] at ih ⊢ <;> exact ih

@[simp] theorem pack_unpack (T : Table Γ) : pack (unpack T) = T := by
  induction T with
  | nil => rfl
  | cons v t ih =>
    obtain ⟨q,a,d⟩ := v
    cases d with
    | none => simp [pack,unpack,movement,direction] at ih ⊢; exact ih
    | some b => cases b <;> simp [pack,unpack,movement,direction] at ih ⊢ <;> exact ih

theorem pack_le [Encodable Γ] (P : TuringProgram Γ) : Encodable.encode (pack P) ≤ Encodable.encode P := by
  induction P with
  | nil => exact le_rfl
  | cons v t ih =>
    obtain ⟨q,a,d⟩ := v
    have hd : Encodable.encode (direction d) ≤ Encodable.encode d := by cases d <;> decide
    exact Nat.succ_le_succ (pair_mono (pair_mono le_rfl (pair_mono le_rfl hd)) ih)

variable {Γ α : Type} [Inhabited Γ] [Primcodable Γ] [Primcodable α]
variable (ι : α ↪ Γ)

def initial (x : List α) : Conf Γ := (1,[],(x.map ι).headI,(x.map ι).tail)

def step (T : Table Γ) (c : Conf Γ) : Conf Γ :=
  let q := c.1
  let l := c.2.1
  let a := c.2.2.1
  let r := c.2.2.2
  let v := (T[Nat.pair q (Encodable.encode a)]?).getD (0,a,none)
  if q = 0 then c else
  if v.2.2 = some false then (v.1,l.tail,l.headI,v.2.1::r) else
  if v.2.2 = some true then (v.1,v.2.1::l,r.headI,r.tail) else (v.1,l,v.2.1,r)

def run (T : Table Γ) (x : List α) (n : ℕ) : Conf Γ := (step T)^[n] (initial ι x)

def physical (c : Conf Γ) : TuringConfiguration Γ := ⟨c.1,⟨c.2.1,c.2.2.1,c.2.2.2⟩⟩

private theorem step_eq (T : Table Γ) (c : Conf Γ) :
    physical (step T c) = ((unpack T).step default (physical c)).getD (physical c) := by
  obtain ⟨q,l,a,r⟩ := c
  by_cases hq : q = 0
  · simp [step,physical,TuringProgram.step,hq]
  · simp only [step,physical,TuringProgram.step,TuringProgram.instruction,unpack,if_neg hq,List.getElem?_map]
    cases h : T[Nat.pair q (Encodable.encode a)]? with
    | none => rfl
    | some v =>
      obtain ⟨s,b,d⟩ := v
      cases d with
      | none => rfl
      | some dir => cases dir <;> cases l <;> cases r <;> rfl

theorem run_eq (T : Table Γ) (x : List α) (n : ℕ) :
    physical (run ι T x n) = (unpack T).runConfiguration default n ⟨1,initialWord ι x⟩ := by
  have gen (c : Conf Γ) (m : ℕ) :
      physical ((step T)^[m] c) = (unpack T).runConfiguration default m (physical c) := by
    induction m generalizing c with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply,ih,step_eq,TuringProgram.runConfiguration]
      cases h : (unpack T).step default (physical c) with
      | none =>
        have hz : c.1 = 0 := by by_contra hn; simp [TuringProgram.step,physical,hn] at h
        cases m <;> simp [TuringProgram.runConfiguration,TuringProgram.step,physical,hz]
      | some v => rfl
  exact gen _ _

theorem step_prim : Primrec₂ (step (Γ := Γ)) := by
  let q : Table Γ × Conf Γ → ℕ := fun p ↦ p.2.1
  let l : Table Γ × Conf Γ → List Γ := fun p ↦ p.2.2.1
  let a : Table Γ × Conf Γ → Γ := fun p ↦ p.2.2.2.1
  let r : Table Γ × Conf Γ → List Γ := fun p ↦ p.2.2.2.2
  have hq : Primrec q := Primrec.fst.comp Primrec.snd
  have hl : Primrec l := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec a := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr : Primrec r := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  let row := fun p : Table Γ × Conf Γ ↦ (p.1[Nat.pair (q p) (Encodable.encode (a p))]?).getD (0,a p,none)
  have hv : Primrec row := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.fst (Primrec₂.natPair.comp hq (Primrec.encode.comp ha)))
    ((Primrec.const 0).pair (ha.pair (Primrec.const none)))
  have ns := Primrec.fst.comp hv
  have wr := Primrec.fst.comp (Primrec.snd.comp hv)
  have dir := Primrec.snd.comp (Primrec.snd.comp hv)
  exact (Primrec.ite (Primrec.eq.comp hq (Primrec.const 0)) Primrec.snd
    (Primrec.ite (Primrec.eq.comp dir (Primrec.const (some false)))
      (ns.pair ((Primrec.list_tail.comp hl).pair ((Primrec.list_headI.comp hl).pair (Primrec.list_cons.comp wr hr))))
    (Primrec.ite (Primrec.eq.comp dir (Primrec.const (some true)))
      (ns.pair ((Primrec.list_cons.comp wr hl).pair ((Primrec.list_headI.comp hr).pair (Primrec.list_tail.comp hr))))
      (ns.pair (hl.pair (wr.pair hr)))))).to₂

theorem run_prim [Finite α] : Primrec (fun p : (Table Γ × List α) × ℕ ↦ run ι p.1.1 p.1.2 p.2) := by
  have word : Primrec (fun p : Table Γ × List α ↦ p.2.map ι) :=
    Primrec.list_map Primrec.snd (((Primrec.dom_finite ι).comp Primrec.snd).to₂)
  have start : Primrec (fun p : Table Γ × List α ↦ initial ι p.2) :=
    (Primrec.const 1).pair ((Primrec.const []).pair ((Primrec.list_headI.comp word).pair (Primrec.list_tail.comp word)))
  have h := Primrec.nat_rec start ((step_prim.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂)
  exact Primrec.of_eq h (fun p ↦ by
    obtain ⟨⟨T,x⟩,n⟩ := p
    induction n with
    | zero => rfl
    | succ n ih =>
      change step T _ = (step T)^[n+1] _
      rw [Function.iterate_succ_apply']
      exact congrArg (step T) ih)

end GenLimit.LearningAlgorithmsLimit.EffectiveTable
