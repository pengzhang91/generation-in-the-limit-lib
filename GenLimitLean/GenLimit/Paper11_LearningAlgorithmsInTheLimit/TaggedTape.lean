import GenLimit.Paper11_LearningAlgorithmsInTheLimit.PolicyTrajectories
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.ObservedTree

/-! # A tagged single-tape teacher for maximum-similarity merging

Each original instruction executes as two physical tape steps. The first
writes a fresh marker encoding its source, scanned symbol, and destination.
The second reads that marker, restores the intended write, and moves.
All second steps can share a single dummy control state because the marker
already distinguishes the original transitions. -/
namespace GenLimit.LearningAlgorithmsLimit.TaggedTape
open Policy Rational
variable {σ : Type*} [Fintype σ] [Encodable σ]

def bound (P : TuringProgram σ) := (states P).sup id + 1
abbrev Symbol (σ : Type*) (n : ℕ) := Sum σ (Fin n × σ × Fin n)

def name (q : ℕ) := if q ≤ 1 then q else q+1
private def original (q : ℕ) := if q ≤ 1 then q else q-1
private theorem original_name (q : ℕ) : original (name q) = q := by
  unfold name original
  split <;> (try split) <;> omega

def index (P : TuringProgram σ) (q : ℕ) (h : q ∈ states P) : Fin (bound P) :=
  ⟨q,Nat.lt_succ_of_le (Finset.le_sup (f := id) h)⟩

def mark (P : TuringProgram σ) (q : ℕ) (a : σ) (h : q ∈ states P) : Symbol σ (bound P) :=
  .inr (index P q h,a,index P (P.instruction q a).1 (state_closed ..))

def firstEvent (P : TuringProgram σ) (v : ↥(states P) × σ) : Event (Symbol σ (bound P)) :=
  (.inl v.2,mark P v.1 v.2 v.1.property,.stay)

def secondEvent (P : TuringProgram σ) (v : ↥(states P) × σ) : Event (Symbol σ (bound P)) :=
  let act := (P.instruction v.1 v.2).2
  (mark P v.1 v.2 v.1.property,.inl act.1,act.2)

noncomputable def allowed (P : TuringProgram σ) : Finset (Event (Symbol σ (bound P))) := by
  classical
  exact Finset.univ.image (firstEvent P) ∪ Finset.univ.image (secondEvent P)

theorem allowed_card (P : TuringProgram σ) :
    (allowed P).card ≤ 2 * (states P).card * Fintype.card σ := by
  classical
  apply (Finset.card_union_le ..).trans
  have h (f : ↥(states P) × σ → Event (Symbol σ (bound P))) :
      (Finset.univ.image f).card ≤ (states P).card * Fintype.card σ := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := f))
  have hsum := Nat.add_le_add (h (firstEvent P)) (h (secondEvent P))
  simpa [two_mul,Nat.add_mul] using hsum

def tape (n : ℕ) (t : TuringTape σ) : TuringTape (Symbol σ n) :=
  ⟨t.left.map Sum.inl,.inl t.scanned,t.right.map Sum.inl⟩

private def transition (P : TuringProgram σ) (q : ℕ) (a : Symbol σ (bound P)) :
    TuringInstruction (Symbol σ (bound P)) :=
  match a with
  | .inl x => if h : original q ∈ states P then (2,mark P (original q) x h,.stay) else (0,a,.stay)
  | .inr (i,x,j) =>
    let act := (P.instruction i x).2
    (name j,.inl act.1,act.2)

def machine (P : TuringProgram σ) (blank : σ) : TuringProgram (Symbol σ (bound P)) :=
  (tabulate 1 (insert 2 ((states P).image name)) (Sum.inl blank,TuringHeadMove.stay)
    (transition P)).rows

theorem start_step (P : TuringProgram σ) (q : ℕ) (a blank : σ) (h : q ∈ states P) :
    (machine P blank).instruction (name q) (.inl a) = (2,mark P q a h,.stay) := by
  have hm : name q ∈ insert 2 ((states P).image name) := Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ h)
  unfold TuringProgram.instruction machine
  rw [tabulate_row _ _ _ _ hm]
  simp [transition,original_name,h]

theorem finish_step (P : TuringProgram σ) (q : ℕ) (a blank : σ) (h : q ∈ states P) :
    (machine P blank).instruction 2 (mark P q a h) =
      (name (P.instruction q a).1,.inl (P.instruction q a).2.1,(P.instruction q a).2.2) := by
  unfold TuringProgram.instruction machine
  rw [tabulate_row _ _ _ _ (Finset.mem_insert_self ..)]
  rfl

theorem original_states_le (P : TuringProgram σ) (blank : σ) :
    (states P).card ≤ (states (machine P blank)).card := by
  classical
  have sub : (states P).image name ⊆ states (machine P blank) := by
    intro v hv
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    let tag : Symbol σ (bound P) := .inr (index P q hq,blank,index P q hq)
    have h : ((machine P blank).instruction 2 tag).1 = name q := by
      unfold TuringProgram.instruction machine
      rw [tabulate_row _ _ _ _ (Finset.mem_insert_self ..)]
      rfl
    exact h ▸ state_closed (machine P blank) 2 tag
  have inj : Function.Injective name := Function.LeftInverse.injective original_name
  simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card sub

private theorem restore (blank v : σ) (m : TuringHeadMove) (n : ℕ)
    (t : TuringTape σ) (tag : Symbol σ n) :
    (((tape n t).writeAndMove (.inl blank) tag .stay).writeAndMove (.inl blank) (.inl v) m) =
      tape n (t.writeAndMove blank v m) := by
  rcases t with ⟨l,a,r⟩
  cases m <;> cases l <;> cases r <;> rfl

/-- Both endpoints of a transition in an observed tagged execution can be
read from its input and output labels, including the halting endpoint. -/
def endpoints {n} (e : Event (Symbol σ n)) : ℕ × ℕ :=
  match e.1, e.2.1 with
  | .inl _, .inr (i,_,_) => (name i,2)
  | .inr (_,_,j), .inl _ => (2,name j)
  | _,_ => (0,0)

/-- The observed path includes exactly the source and target labels of
each physical transition, in execution order. -/
abbrev Path {n : ℕ} := MSM.ObservedTree.Path (endpoints (σ := σ) (n := n))

theorem simulate {P : TuringProgram σ} {blank q t es out} (h : Execution P blank q t es out)
    (hq : q ∈ states P) :
    ∃ ds, Execution (machine P blank) (.inl blank) (name q) (tape _ t) ds (tape _ out) ∧
      Path (name q) ds 0 ∧ ds.length = 2 * es.length ∧
      ∀ e ∈ ds, (machine P blank).instruction (endpoints e).1 e.1 = ((endpoints e).2,e.2) ∧ e ∈ allowed P := by
  classical
  induction h with
  | halt => exact ⟨[],.halt _,.nil _,rfl,by simp⟩
  | @step q t es out hn ht ih =>
    let m := mark P q t.scanned hq
    let act := P.instruction q t.scanned
    let e : Event (Symbol σ (bound P)) := (.inl t.scanned,m,.stay)
    let f : Event (Symbol σ (bound P)) := (m,.inl act.2.1,act.2.2)
    obtain ⟨ds,hds,hpath,hlen,hlabels⟩ := ih (state_closed ..)
    have h₁ := start_step P q t.scanned blank hq
    have h₂ := finish_step P q t.scanned blank hq
    refine ⟨e::f::ds,?_,.cons e (.cons f hpath),by simp [hlen]; omega,?_⟩
    case refine_2 =>
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨h₁,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(⟨q,hq⟩,t.scanned),Finset.mem_univ _,rfl⟩)⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨h₂,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(⟨q,hq⟩,t.scanned),Finset.mem_univ _,rfl⟩)⟩
      exact hlabels _ hg
    have hn' : name q ≠ 0 := by unfold name; split <;> omega
    let t₁ := (tape (bound P) t).writeAndMove (.inl blank) m .stay
    have hr : t₁.writeAndMove (.inl blank) (.inl act.2.1) act.2.2 = tape _ (t.writeAndMove blank act.2.1 act.2.2) :=
      restore ..
    have child : Execution (machine P blank) (.inl blank) 2 t₁ (f::ds) (tape _ out) := by
      have hval : (machine P blank).instruction 2 t₁.scanned = (name act.1,.inl act.2.1,act.2.2) := h₂
      have hrest : Execution (machine P blank) (.inl blank) ((machine P blank).instruction 2 t₁.scanned).1
          (t₁.writeAndMove (.inl blank) ((machine P blank).instruction 2 t₁.scanned).2.1
            ((machine P blank).instruction 2 t₁.scanned).2.2) ds (tape _ out) := by
        rw [hval,hr]; exact hds
      simpa only [hval] using Execution.step (by decide : 2 ≠ 0) hrest
    have hval : (machine P blank).instruction (name q) (tape (bound P) t).scanned = (2,m,.stay) := h₁
    have hrest : Execution (machine P blank) (.inl blank) ((machine P blank).instruction (name q) (tape (bound P) t).scanned).1
        ((tape (bound P) t).writeAndMove (.inl blank) ((machine P blank).instruction (name q) (tape (bound P) t).scanned).2.1
          ((machine P blank).instruction (name q) (tape (bound P) t).scanned).2.2) (f::ds) (tape _ out) := by
      rw [hval]; exact child
    simpa only [hval] using Execution.step hn' hrest

end GenLimit.LearningAlgorithmsLimit.TaggedTape
