import GenLimit.Paper16_ComplexityBarriers.JointGrammar
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.ConstantTape

/-! # Checking a single-tape computation with two context-free grammars

Each side of the head is one stack with an explicit bottom. Two labelled
rewrites implement one Turing transition. The first transfers the control
to the right stack, so the next rewrite can access both neighboring cells.
After a halt the remaining cells are popped and counted in the trace. -/
namespace GenLimit.ComplexityBarriers.CFG.TapeCheck
open List Turing
open GenLimit.LearningAlgorithmsLimit
open GenLimit.LearningAlgorithmsLimit.NativeTape (BinaryMachine view)
open scoped Classical
noncomputable section

abbrev Marker := Option Bool
abbrev Left (Q : Type) := (Q × Bool) ⊕ Option Marker
abbrev Right (Q : Type) := (Q × Bool × Marker) ⊕ (Bool × Marker)
abbrev Controller (Q : Type) := Q → Bool → Option (Q × TM0.Stmt Bool)

private def head (q : Q) (a : Bool) : Left Q := .inl (q,a)
private def cellL (a : Marker) : Left Q := .inr (some a)
private def finishL : Left Q := .inr none
private def cellR (a : Marker) : Right Q := .inr (false,a)
private def finishR (a : Marker) : Right Q := .inr (true,a)
private def marked (q : Q) (a : Bool) (r : Marker) : Right Q := .inl (q,a,r)

private def keepBottom (f : Marker → S) : Marker → List S
  | none => [f none]
  | some _ => []

def joint (δ : Controller Q) : Joint (Left Q) (Right Q)
  | .inl (q,a),.inr (false,r) => some ([],[marked q a r])
  | .inr (some l),.inl (q,a,r) =>
    match δ q a with
    | none => some ([cellL l],[finishR r])
    | some (p,.write b) => some ([head p b,cellL l],[cellR r])
    | some (p,.move .left) => some (head p (l.getD false) :: keepBottom cellL l,[cellR (some a),cellR r])
    | some (p,.move .right) => some ([head p (r.getD false),cellL (some a),cellL l],keepBottom cellR r)
  | .inr (some (some _)),.inr (true,r) => some ([],[finishR r])
  | .inr (some none),.inr (true,none) => some ([],[])
  | .inr (some none),.inr (true,some _) => some ([finishL],[])
  | .inr none,.inr (false,some _) => some ([finishL],[])
  | .inr none,.inr (false,none) => some ([],[])
  | _,_ => none

private def stack (f : Marker → S) (xs : List Bool) := (xs.map (fun a ↦ f (some a))) ++ [f none]

def left (q : Q) (t : TuringTape Bool) : List (Left Q) := head q t.scanned :: stack cellL t.left
def right (t : TuringTape Bool) : List (Right Q) := stack cellR t.right

private def Extends (J : Joint A B) (l : List A) (r : List B) (l' : List A) (r' : List B) : Prop :=
  ∀ tr, Run J l' r' tr → ∃ tr', Run J l r tr' ∧ tr.length ≤ tr'.length

private theorem ext_refl (J : Joint A B) (l r) : Extends J l r l r :=
  fun tr hr ↦ ⟨tr,hr,le_rfl⟩

private theorem ext_trans {J : Joint A B} {l r l' r' l'' r''}
    (h : Extends J l r l' r') (k : Extends J l' r' l'' r'') : Extends J l r l'' r'' := by
  intro tr hr
  obtain ⟨u,hu,hs⟩ := k tr hr
  obtain ⟨v,hv,ht⟩ := h u hu
  exact ⟨v,hv,hs.trans ht⟩

private def move (t : TuringTape Bool) : TM0.Stmt Bool → TuringTape Bool
  | .write b => t.writeAndMove false b .stay
  | .move .left => t.writeAndMove false t.scanned .left
  | .move .right => t.writeAndMove false t.scanned .right

private theorem two_steps (δ : Controller Q) (q p : Q) (t : TuringTape Bool) (s : TM0.Stmt Bool)
    (hh : δ q t.scanned = some (p,s)) :
    Extends (joint δ) (left q t) (right t) (left p (move t s)) (right (move t s)) := by
  intro tr hr
  obtain ⟨ls,a,rs⟩ := t
  change δ q a = _ at hh
  cases ls <;> cases rs <;> cases s with
  | write b =>
    exact ⟨_::_::tr,Run.step rfl (Run.step (by simp [joint,marked,cellL,hh]; exact ⟨rfl,rfl⟩) hr),by simp only [List.length_cons]; omega⟩
  | move dir =>
    cases dir <;> exact ⟨_::_::tr,Run.step rfl (Run.step (by simp [joint,marked,cellL,hh]; exact ⟨rfl,rfl⟩) hr),by simp only [List.length_cons]; omega⟩

private theorem clear_right (δ : Controller Q) (rs : List Bool) :
    ∃ tr, Run (joint δ) [finishL] (stack cellR rs) tr ∧ rs.length+1 ≤ tr.length := by
  induction rs with
  | nil => exact ⟨_,Run.step rfl Run.done,le_rfl⟩
  | cons a rs ih =>
    obtain ⟨tr,ht,hl⟩ := ih
    exact ⟨_,Run.step rfl ht,Nat.succ_le_succ hl⟩

private theorem clear_left (δ : Controller Q) (ls : List Bool) (r : Marker) (rs : List (Right Q))
    (k : ℕ) (h :
      ∃ tr, Run (joint δ) [cellL none] (finishR r :: rs) tr ∧ k ≤ tr.length) :
    ∃ tr, Run (joint δ) (stack cellL ls) (finishR r :: rs) tr ∧ ls.length+k ≤ tr.length := by
  induction ls with
  | nil => simpa [stack] using h
  | cons a ls ih =>
    obtain ⟨tr,ht,hl⟩ := ih
    exact ⟨_,Run.step rfl ht,by simpa only [List.length_cons,Nat.succ_add] using Nat.succ_le_succ hl⟩

private theorem halt_trace (δ : Controller Q) (q : Q) (t : TuringTape Bool) (hh : δ q t.scanned=none) :
    ∃ tr, Run (joint δ) (left q t) (right t) tr ∧ t.left.length+1+t.right.length ≤ tr.length := by
  obtain ⟨ls,a,rs⟩ := t
  change δ q a = none at hh
  let r := rs.head?
  let rt := (stack (cellR (Q := Q)) rs).tail
  have hrt : stack (cellR (Q := Q)) rs = cellR r::rt := by cases rs <;> rfl
  have base : ∃ tr, Run (joint δ) [cellL none] (finishR r :: rt) tr ∧ rs.length+1 ≤ tr.length := by
    cases rs with
    | nil => exact ⟨_,Run.step rfl Run.done,le_rfl⟩
    | cons b rs =>
      obtain ⟨tr,ht,hl⟩ := clear_right δ rs
      exact ⟨_,Run.step rfl ht,Nat.succ_le_succ hl⟩
  obtain ⟨tr,ht,hl⟩ := clear_left δ ls r rt _ base
  change ∃ _, Run _ (head q a :: stack cellL ls) (stack cellR rs) _ ∧ ls.length+1+rs.length ≤ _
  rw [hrt]
  cases ls <;> exact ⟨_::_::tr,Run.step rfl (Run.step (by simp [joint,marked,cellL,hh]; exact ⟨rfl,rfl⟩) ht),by simp only [List.length_cons] at hl ⊢; omega⟩

abbrev States (U : BinaryMachine) := ↥U.states

def control (U : BinaryMachine) (q : States U) (a : Bool) : Option (States U × TM0.Stmt Bool) :=
  (U.program q.val a).pbind fun p hp ↦ some (⟨p.1,U.supports.2 hp q.property⟩,p.2)

private theorem control_some (U : BinaryMachine) (q : States U) (a : Bool) {p s}
    (hp : U.program q.val a = some (p,s)) :
    control U q a = some (⟨p,U.supports.2 hp q.property⟩,s) := by simp [control,hp]

private theorem control_none (U : BinaryMachine) (q : States U) (a : Bool) (hp : U.program q.val a = none) :
    control U q a = none := by simp [control,hp]

private def trueSide (l : ListBlank Bool) : ℕ :=
  l.liftOn (List.count true) (by rintro a _ ⟨n,rfl⟩; simp [List.count_replicate])

private def mass (t : Tape Bool) := trueSide t.left + (if t.head then 1 else 0) + trueSide t.right

private theorem mass_view (t : TuringTape Bool) : mass (view t) ≤ t.left.length+1+t.right.length := by
  have hl := List.count_le_length (a := true) (l := t.left)
  have hr := List.count_le_length (a := true) (l := t.right)
  change t.left.count true + (if t.scanned then 1 else 0) + t.right.count true ≤ _
  split <;> omega

private theorem mass_input (w : List Bool) : mass (Tape.mk₁ w) = w.count true := by
  cases w with
  | nil => rfl
  | cons a w =>
    change 0 + (if a then 1 else 0) + w.count true = (a::w).count true
    cases a <;> simp [Nat.add_comm]

def start (U : BinaryMachine) : States U := ⟨_,U.supports.1⟩
def input (w : List Bool) : TuringTape Bool := ⟨[],w.headI,w.tail⟩

theorem input_lengths (q : Q) (w : List Bool) :
    (left q (input w)).length ≤ w.length+2 ∧ (right (Q := Q) (input w)).length ≤ w.length+2 := by
  simp [left,right,input,stack]
  omega

private theorem view_move (t : TuringTape Bool) (s : TM0.Stmt Bool) :
    view (move t s) = match s with | .write b => (view t).write b | .move d => (view t).move d := by
  obtain ⟨l,a,r⟩ := t
  cases s with
  | write b => rfl
  | move d => cases d <;> cases l <;> cases r <;> rfl

theorem run_of_eval (U : BinaryMachine) (w out : List Bool) (q : U.State)
    (h : (⟨q,Tape.mk₁ out⟩ : TM0.Cfg Bool U.State) ∈
      Turing.eval (TM0.step U.program) ⟨U.initial.default,Tape.mk₁ w⟩) :
    ∃ tr, Run (joint (control U)) (left (start U) (input w)) (right (input w)) tr ∧ out.count true ≤ tr.length := by
  obtain ⟨reach,halt⟩ := Turing.mem_eval.mp h
  let J := joint (control U)
  have lift {a b : TM0.Cfg Bool U.State} (r : Turing.Reaches (TM0.step U.program) a b)
      (ha : a.q ∈ U.states) (t : TuringTape Bool) (ht : view t=a.Tape) :
      ∃ (v : TuringTape Bool) (hb : b.q ∈ U.states), view v=b.Tape ∧
        Extends J (left ⟨a.q,ha⟩ t) (right t) (left ⟨b.q,hb⟩ v) (right v) := by
    induction r with
    | refl => exact ⟨t,ha,ht,ext_refl J _ _⟩
    | @tail b c _ he ih =>
      obtain ⟨v,hb,hv,hx⟩ := ih
      obtain ⟨⟨p,s⟩,hp,rfl⟩ := Option.map_eq_some_iff.mp he
      have hvh : v.scanned=b.Tape.head := congrArg Tape.head hv
      have hh : U.program b.q v.scanned=some (p,s) := hvh ▸ hp
      refine ⟨move v s,U.supports.2 hp hb,?_,ext_trans hx (two_steps _ _ _ _ _ (control_some U ⟨b.q,hb⟩ _ hh))⟩
      rw [view_move,hv]; cases s <;> rfl
  obtain ⟨v,hq,hv,hx⟩ := lift reach U.supports.1 (input w) rfl
  have hp : U.program q (Tape.mk₁ out).head=none := by simpa [TM0.step] using halt
  have hvh : v.scanned=(Tape.mk₁ out).head := congrArg Tape.head hv
  obtain ⟨tr,ht,hl⟩ := halt_trace (control U) ⟨q,hq⟩ v (control_none U _ _ (hvh ▸ hp))
  obtain ⟨tr',ht',hl'⟩ := hx tr ht
  refine ⟨tr',ht',?_⟩
  change view v = Tape.mk₁ out at hv
  rw [←mass_input,←hv]
  exact (mass_view v).trans (hl.trans hl')

end
end GenLimit.ComplexityBarriers.CFG.TapeCheck
