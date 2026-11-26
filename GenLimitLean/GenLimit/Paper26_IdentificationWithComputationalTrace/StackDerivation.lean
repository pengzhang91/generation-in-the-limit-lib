import GenLimit.Paper26_IdentificationWithComputationalTrace.Pushdown
import GenLimit.Paper26_IdentificationWithComputationalTrace.ControlPath
import GenLimit.Paper26_IdentificationWithComputationalTrace.MarkedTree

namespace GenLimit.ComputationalTrace.PDA
open Control

/-- Remembering the next input symbol at each endpoint permits both reading
and silent transitions, including the end-of-input cleanup. -/
structure Vertex where
  state : ℕ
  look : Option Bool
  deriving DecidableEq

structure Label where
  start : Vertex
  top : Bool
  stop : Vertex
  next : Vertex
  consume : Bool
  op : Op
  selected : Bool
  deriving DecidableEq

def Label.key (a : Label) := (a.start,a.top,a.stop)
def Label.word (a : Label) : List Bool := if a.consume then a.start.look.toList else []

def Label.Legal (P : Program ℕ) (a : Label) : Prop :=
  P.rule a.start.state a.top a.start.look = some (a.next.state,a.consume,a.op) ∧
  (if a.consume then a.start.look.isSome = true else a.next.look = a.start.look) ∧
  (a.selected = true → a.consume = true)

/-- A derivation removes exactly one stack symbol without consulting the
stack below it. Its preorder lists the instructions in execution order. -/
inductive Parse (P : Program ℕ) : Tree Label → Vertex → Bool → Vertex → Prop
  | pop {a} (legal : a.Legal P) (op : a.op = .pop) (endAt : a.next = a.stop) :
      Parse P (.node a .nil .nil) a.start a.top a.stop
  | keep {a l} (legal : a.Legal P) (op : a.op = .keep)
      (tail : Parse P l a.next a.top a.stop) :
      Parse P (.node a l .nil) a.start a.top a.stop
  | push {a l r bit mid} (legal : a.Legal P) (op : a.op = .push bit)
      (left : Parse P l a.next bit mid) (right : Parse P r mid a.top a.stop) :
      Parse P (.node a l r) a.start a.top a.stop

inductive Forest (P : Program ℕ) : List (Tree Label) → Vertex → List Bool → Vertex → Prop
  | nil (p) : Forest P [] p [] p
  | cons {t ts p b q bs z} (one : Parse P t p b q) (rest : Forest P ts q bs z) :
      Forest P (t :: ts) p (b :: bs) z

def tokens (fs : List (Tree Label)) := fs.flatMap Tree.items

def letters (xs : List Label) := xs.flatMap Label.word

def vtx (c : Frame ℕ Memory) : Vertex := ⟨c.1,c.2.input.head?⟩

theorem edge_info {P : Program ℕ} {c d : Frame ℕ Memory}
    (hm : move device P.machine c = some d) :
    ∃ b bs eat op, c.2.stack = b :: bs ∧
      P.rule c.1 b c.2.input.head? = some (d.1,eat,op) ∧
      (eat = true → c.2.input ≠ []) ∧ d.2.input = (if eat then c.2.input.tail else c.2.input) ∧
      d.2.stack = op.apply (b :: bs) := by
  cases hs : c.2.stack with
  | nil => simp [move,Program.machine,device,hs] at hm
  | cons b bs =>
    cases he : P.rule c.1 b c.2.input.head? with
    | none => simp [move,Program.machine,device,hs,he] at hm
    | some z =>
      rcases z with ⟨q,eat,op⟩
      have ht : P.machine.table c.1 (device.read c.2) =
          (if eat && c.2.input.head?.isNone then none else some (q,eat,op)) := by
        simp only [device,Program.machine,hs,List.head?_cons]
        change (P.rule c.1 b c.2.input.head?).bind _ = _
        rw [he]
        rfl
      unfold move at hm
      rw [ht] at hm
      split at hm
      · contradiction
      next good =>
        obtain rfl := Option.some.inj hm
        refine ⟨b,bs,eat,op,rfl,he,?_,rfl,?_⟩
        · intro h hh
          simp [h,hh] at good
        · simp [device,hs]

private theorem start_word (a : Label) (P : Program ℕ) (h : a.Legal P) {u : List Bool}
    (hu : u.head? = a.next.look) : (a.word ++ u).head? = a.start.look := by
  obtain ⟨_,hc,_⟩ := h
  cases he : a.consume <;> cases ha : a.start.look <;> simp_all [Label.word]

private theorem execute_edge {P : Program ℕ} {a : Label} (h : a.Legal P)
    (u stack : List Bool) (hu : u.head? = a.next.look) :
    move device P.machine (a.start.state,⟨a.word ++ u,a.top :: stack⟩) =
      some (a.next.state,⟨u,a.op.apply (a.top :: stack)⟩) := by
  have hh := start_word a P h hu
  obtain ⟨rule,hc,_⟩ := h
  cases he : a.consume <;> cases ha : a.start.look <;>
    simp_all [move,device,Program.machine,Label.word]

/-- Rebuild full configurations from a derivation with an arbitrary untouched
stack suffix and unread input suffix. -/
theorem Parse.execute {P : Program ℕ} {t p b z} (h : Parse P t p b z)
    (u stack : List Bool) (hu : u.head? = z.look) :
    (letters t.items ++ u).head? = p.look ∧
    ∃ cs, cs.map Prod.fst = t.items.map (fun a => a.start.state) ∧
      Path device P.machine (p.state,⟨letters t.items ++ u,b :: stack⟩) cs (z.state,⟨u,stack⟩) := by
  induction h generalizing u stack with
  | @pop a h hop he =>
    simp only [Tree.items,letters,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.map_cons,List.map_nil]
    have hl := hu.trans (congrArg Vertex.look he.symm)
    refine ⟨start_word a P h hl,[(a.start.state,_)],rfl,.single (by simp) ?_⟩
    simpa only [he,hop,Op.apply,List.tail_cons] using execute_edge h u stack hl
  | @keep a l h hop tail ih =>
    obtain ⟨hh,cs,hs,hp⟩ := ih u stack hu
    simp only [Tree.items,List.append_nil,letters,List.flatMap_cons,List.map_cons,List.append_assoc]
    refine ⟨start_word a P h hh,(_,_) :: cs,by simp [hs],.cons (by simp) ?_ hp⟩
    simpa only [hop,Op.apply] using execute_edge h (letters l.items ++ u) stack hh
  | @push a l r bit mid h hop left right il ir =>
    obtain ⟨hr,rs,hsr,pr⟩ := ir u stack hu
    obtain ⟨hl,ls,hsl,pl⟩ := il (letters r.items ++ u) (a.top :: stack) hr
    simp only [Tree.items,letters,List.flatMap_cons,List.flatMap_append,List.map_cons,List.map_append,
      List.append_assoc]
    refine ⟨start_word a P h hl,(_,_) :: (ls ++ rs),by simp [hsl,hsr],.cons (by simp) ?_ (pl.append pr)⟩
    simpa only [hop,Op.apply] using execute_edge h _ stack hl

theorem Parse.root {P : Program ℕ} {a l r p b z} (h : Parse P (.node a l r) p b z) :
    (p,b,z) = a.key := by cases h <;> rfl

theorem Parse.nonempty {P : Program ℕ} {t p b z} (h : Parse P t p b z) :
    ∃ a l r, t = .node a l r := by cases h <;> exact ⟨_,_,_,rfl⟩

end GenLimit.ComputationalTrace.PDA
