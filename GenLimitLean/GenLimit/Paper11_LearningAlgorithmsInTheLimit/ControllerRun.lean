import GenLimit.Paper11_LearningAlgorithmsInTheLimit.BlockController

namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open Turing

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ]

def Moves {Q : Type} (δ : Rule Γ Q) (x y : Config Γ Q) := ∃ n : ℕ, (tick δ)^[n] x = y

theorem Moves.one {Q : Type} {δ : Rule Γ Q} {x y} (h : tick δ x = y) : Moves δ x y := ⟨1,h⟩

theorem Moves.trans {Q : Type} {δ : Rule Γ Q} {x y z} (h : Moves δ x y) (g : Moves δ y z) :
    Moves δ x z := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := g
  exact ⟨b+a,by rw [Function.iterate_add_apply,ha,hb]⟩

variable (o : Γ) (U : BinaryMachine) (word : List Bool) (w : ℕ)
local notation "δ" => rule o U word w

private theorem read_mapped (ho : o ≠ default) (t : Tape Bool) :
    bitRead ((t.map (bitMap o)).head) = t.head := by
  change bitRead (bitSymbol o t.head) = t.head
  cases t.head <;> simp [bitRead,bitSymbol,ho]

private def sim (c : TM0.Cfg Bool U.State) (h : c.q ∈ U.states) : Config Γ (Control U word w) :=
  (some (.simulate ⟨c.q,h⟩),c.Tape.map (bitMap o))

private def action (o a : Γ) : TM0.Stmt Bool → Γ × TuringHeadMove
  | .move .left => (a,.left)
  | .move .right => (a,.right)
  | .write b => (bitSymbol o b,.stay)

private theorem rule_some (q : ↥U.states) (a : Γ) {r v} (h : U.program q.val (bitRead a) = some (r,v)) :
    δ (.simulate q) a = (some (.simulate ⟨r,U.supports.2 h q.property⟩),action o a v) := by
  simp only [rule]
  split
  · rename_i he
    rw [he] at h
    contradiction
  · rename_i r' v' he
    have eq := Option.some.inj (he.symm.trans h)
    cases eq
    cases v with
    | move d => cases d <;> rfl
    | write => rfl

private theorem rule_stop (q : ↥U.states) (a : Γ) (h : U.program q.val (bitRead a) = none) :
    δ (.simulate q) a = (some .inspect,a,.stay) := by
  simp only [rule]
  split
  · rfl
  · rename_i he
    rw [he] at h
    contradiction

private theorem sim_step (ho : o ≠ default) {x y : TM0.Cfg Bool U.State}
    (hx : x.q ∈ U.states) (h : y ∈ TM0.step U.program x) :
    tick δ (sim o U word w x hx) = sim o U word w y (TM0.step_supports _ U.supports h hx) := by
  rcases x with ⟨q,t⟩
  unfold TM0.step at h
  obtain ⟨⟨r,act⟩,hr,rfl⟩ := Option.map_eq_some_iff.mp h
  have hprog : U.program q t.head = some (r,act) := hr
  have hs : U.program q (bitRead (t.map (bitMap o)).head) = some (r,act) := by rw [read_mapped o ho,hprog]
  have hval := rule_some o U word w ⟨q,hx⟩ _ hs
  cases act with
  | move d =>
    cases d <;> simp only [sim,tick,hval,action,perform,Tape.write_self,Tape.map_move]
  | write b =>
    simp only [sim,tick,hval,action,perform,Tape.map_write]
    rfl

theorem simulate_halt (ho : o ≠ default) {q : U.State} {out : List Bool}
    (h : (⟨q,Tape.mk₁ out⟩ : TM0.Cfg Bool U.State) ∈
      Turing.eval (TM0.step U.program) ⟨U.initial.default,Tape.mk₁ word⟩) :
    Moves δ (some (.simulate ⟨_,U.supports.1⟩),Tape.mk₁ (word.map (bitSymbol o)))
      (some .inspect,Tape.mk₁ (out.map (bitSymbol o))) := by
  obtain ⟨reach,halt⟩ := Turing.mem_eval.mp h
  have lift {a b : TM0.Cfg Bool U.State} (ha : a.q ∈ U.states) (r : Turing.Reaches (TM0.step U.program) a b) :
      ∃ hb, Moves δ (sim o U word w a ha) (sim o U word w b hb) := by
    induction r with
    | refl => exact ⟨_,0,rfl⟩
    | tail _ he ih =>
      obtain ⟨hb,hp⟩ := ih
      exact ⟨_,hp.trans (Moves.one (sim_step o U word w ho hb he))⟩
  obtain ⟨hq,hpath⟩ := lift (a := ⟨U.initial.default,Tape.mk₁ word⟩) U.supports.1 reach
  have hnone : U.program q (Tape.mk₁ out).head = none := by simpa [TM0.step] using halt
  have last : tick δ (sim o U word w ⟨q,Tape.mk₁ out⟩ hq) =
      (some .inspect,Tape.mk₁ (out.map (bitSymbol o))) := by
    have hm : U.program q (bitRead (((Tape.mk₁ out).map (bitMap o)).head)) = none := by
      rw [read_mapped o ho,hnone]
    have hr := rule_stop o U word w ⟨q,hq⟩ _ hm
    simp only [sim,tick,hr,perform,Tape.write_self]
    rw [Tape.map_mk₁]
    rfl
  simpa only [sim,Tape.map_mk₁] using hpath.trans (Moves.one last)

private theorem fill_run (xs L R : List Γ) (hlen : xs.length ≤ w) :
    Moves δ (some (.fill ⟨xs.length,by omega⟩),Tape.mk₂ L (xs++R))
      (some .inspect,Tape.mk₂ (List.replicate xs.length o ++ L) R) := by
  induction xs generalizing L with
  | nil =>
    apply Moves.one
    simp [tick,rule,perform,Tape.write_self]
  | cons a xs ih =>
    have one : tick δ (some (.fill ⟨(a::xs).length,by omega⟩),Tape.mk₂ L ((a::xs)++R)) =
        (some (.fill ⟨xs.length,by simp at hlen; omega⟩),Tape.mk₂ (o::L) (xs++R)) := by
      simp only [tick,rule,List.length_cons,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel]
      rfl
    have h := (Moves.one one).trans (ih (o::L) (by simp at hlen; omega))
    simpa [List.replicate_succ',List.append_assoc] using h

theorem print_run (ho : o ≠ default) (bs : List (List Bool)) (L : List Γ)
    (hb : ∀ b ∈ bs, b.length = w+1 ∧ b.head? = some true) :
    Moves δ (some .inspect,Tape.mk₂ L (bs.flatten.map (bitSymbol o)))
      (none,Tape.mk₂ (List.replicate bs.flatten.length o ++ L) []) := by
  induction bs generalizing L with
  | nil =>
    apply Moves.one
    have hh : (Tape.mk₂ L ([] : List Γ)).head = default := rfl
    simp only [List.flatten_nil,List.map_nil,List.length_nil,List.replicate_zero,List.nil_append,tick,rule,hh,if_pos rfl,perform]
    rfl
  | cons b bs ih =>
    obtain ⟨hlen,hhead⟩ := hb b List.mem_cons_self
    cases b with
    | nil => simp at hhead
    | cons a xs =>
      have he : a = true := Option.some.inj hhead
      subst a
      have hw : xs.length = w := by simpa using hlen
      let R := bs.flatten.map (bitSymbol o)
      let buf := xs.map (bitSymbol o)
      have hfirst : tick δ (some .inspect,Tape.mk₂ L (o::(buf++R))) =
          (some (.fill ⟨buf.length,by simp [buf,hw]⟩),Tape.mk₂ (o::L) (buf++R)) := by
        have hh : (Tape.mk₂ L (o::(buf++R))).head = o := rfl
        simp only [tick,rule,hh,if_neg ho]
        have hlen' : buf.length = w := by simp [buf,hw]
        simp only [hlen']
        rfl
      have hfill := fill_run o U word w buf (o::L) R (by simp [buf,hw])
      have htail := ih (List.replicate buf.length o ++ o::L) (fun b h ↦ hb b (List.mem_cons_of_mem _ h))
      have h := ((Moves.one hfirst).trans hfill).trans htail
      have left : List.replicate bs.flatten.length o ++ (List.replicate buf.length o ++ o::L) =
          List.replicate (((true::xs)::bs).flatten.length) o ++ L := by
        simp only [List.flatten_cons,List.length_append,List.length_cons]
        rw [Nat.add_comm (xs.length+1),List.replicate_add,List.replicate_succ']
        simp [buf,List.append_assoc]
      rw [left] at h
      simpa only [List.flatten_cons,List.map_append,List.map_cons,bitSymbol,buf,R] using h

end GenLimit.LearningAlgorithmsLimit.NativeTape
