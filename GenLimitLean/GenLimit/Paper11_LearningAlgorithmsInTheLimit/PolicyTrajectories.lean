import GenLimit.Paper11_LearningAlgorithmsInTheLimit.FiniteTransducers

/-! # Finite tape trajectories and the rational reduction

Every observed step supplies its scanned symbol, write symbol and head move.
The end of the finite observation also identifies the terminating step.
Two rational functions on the same alphabet recover the action and this
termination bit on every scanned prefix. Their product executes on a tape. -/
namespace GenLimit.LearningAlgorithmsLimit.Policy
open Rational
variable {σ : Type*} [Encodable σ]

abbrev Action (σ : Type*) := σ × TuringHeadMove
abbrev Event (σ : Type*) := σ × Action σ

/-- The complete observed tape manipulations, from an arbitrary configuration. -/
inductive Execution (P : TuringProgram σ) (blank : σ) :
    ℕ → TuringTape σ → List (Event σ) → TuringTape σ → Prop
  | halt (t : TuringTape σ) : Execution P blank 0 t [] t
  | step {q t es out} (hq : q ≠ 0)
      (tail : Execution P blank (P.instruction q t.scanned).1
        (t.writeAndMove blank (P.instruction q t.scanned).2.1 (P.instruction q t.scanned).2.2)
        es out) :
      Execution P blank q t ((t.scanned,(P.instruction q t.scanned).2) :: es) out

theorem Execution.halt_iff {P : TuringProgram σ} {blank q t es out}
    (h : Execution P blank q t es out) : q = 0 ↔ es = [] := by
  cases h with
  | halt => simp
  | step hn _ => simp [hn]

theorem Execution.run {P : TuringProgram σ} {blank q t es out}
    (h : Execution P blank q t es out) :
    P.runConfiguration blank es.length ⟨q,t⟩ = ⟨0,out⟩ := by
  induction h with
  | halt => rfl
  | step hn _ ih => simpa [TuringProgram.runConfiguration,TuringProgram.step,hn] using ih

/-- Every halting computation of the evaluator gives a completed PTO.
The witness is its actual sequence of read/write/move triples. -/
theorem execution_of_run (P : TuringProgram σ) (blank : σ) (n q : ℕ) (t : TuringTape σ)
    (h : (P.runConfiguration blank n ⟨q,t⟩).state = 0) :
    ∃ es, Execution P blank q t es (P.runConfiguration blank n ⟨q,t⟩).tape := by
  induction n generalizing q t with
  | zero =>
    change q = 0 at h
    subst q
    exact ⟨[],.halt _⟩
  | succ n ih =>
    by_cases hq : q = 0
    · subst q
      exact ⟨[],by simpa [TuringProgram.runConfiguration,TuringProgram.step] using Execution.halt (P := P) (blank := blank) t⟩
    · simp only [TuringProgram.runConfiguration,TuringProgram.step,if_neg hq] at h ⊢
      obtain ⟨es,hh⟩ := ih _ _ h
      exact ⟨_,.step hq hh⟩

def states (P : TuringProgram σ) := insert 1 (insert 0 (P.map Prod.fst).toFinset)

theorem state_closed (P : TuringProgram σ) (q : ℕ) (a : σ) : (P.instruction q a).1 ∈ states P := by
  simp only [states,Finset.mem_insert,List.mem_toFinset]
  unfold TuringProgram.instruction
  cases h : P[Nat.pair q (Encodable.encode a)]? with
  | none => exact Or.inr (Or.inl rfl)
  | some v => exact Or.inr (Or.inr (List.mem_map.mpr ⟨v,List.mem_of_getElem? h,rfl⟩))

/-- A marker can be conveyed using two symbols of the prescribed action
alphabet even for a one-symbol tape alphabet. -/
def marker (blank : σ) (done : Bool) : Action σ := (blank,if done then .stay else .right)

abbrev Label (σ : Type*) := Action σ → Bool → Action σ

def policyTable [Fintype σ] (P : TuringProgram σ) (blank : σ) (label : Label σ) :
    Table (Action σ) := tabulate 1 (states P) (blank,.stay) (fun q a ↦
      let tr := P.instruction q a
      (tr.1,label tr.2 (tr.1 == 0)))

/-- One labeled rational input for each nonempty scanned prefix. -/
def queries (label : Label σ) : List (Event σ) → List (List σ × Action σ)
  | [] => []
  | (a,v) :: es => ([a],label v es.isEmpty) ::
      (queries label es).map (fun z ↦ (a :: z.1,z.2))

theorem queries_length (label : Label σ) (es : List (Event σ)) :
    (queries label es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [queries,ih]

theorem query_nonempty {label : Label σ} {es : List (Event σ)} {w v}
    (h : (w,v) ∈ queries label es) : w ≠ [] := by
  cases es with
  | nil => simp [queries] at h
  | cons e es =>
    rcases List.mem_cons.mp h with he | hm
    · exact fun hn ↦ by simpa [hn] using congrArg Prod.fst he
    · obtain ⟨z,_,hz⟩ := List.mem_map.mp hm
      exact fun hn ↦ by simpa [hn] using congrArg Prod.fst hz

def CorrectAt (T : Table (Action σ)) (q : ℕ) (b : Action σ) (label : Label σ)
    (es : List (Event σ)) :=
  ∀ w v, (w,v) ∈ queries label es → T.lastFrom q b w = v

theorem policy_correct [Fintype σ] {P : TuringProgram σ} {blank q t es out}
    (h : Execution P blank q t es out) (hq : q ∈ states P) (b : Action σ) (label : Label σ) :
    CorrectAt (policyTable P blank label) q b label es := by
  induction h generalizing b with
  | halt => simp [CorrectAt,queries]
  | @step q t es out hn tail ih =>
    have ht : (policyTable P blank label).step q t.scanned =
        ((P.instruction q t.scanned).1,label (P.instruction q t.scanned).2
          ((P.instruction q t.scanned).1 == 0)) :=
      tabulate_step _ _ _ _ hq _
    have he : ((P.instruction q t.scanned).1 == 0) = es.isEmpty := by
      cases es <;> simp_all [tail.halt_iff]
    intro w v hv
    rcases List.mem_cons.mp hv with hfirst | hrest
    · cases hfirst
      simp [Table.lastFrom,ht,he]
    · obtain ⟨⟨w',v'⟩,hm,hh⟩ := List.mem_map.mp hrest
      cases hh
      rw [Table.lastFrom_append,ht]
      exact ih (state_closed _ _ _) _ _ _ hm

/-- Encode the initial pair as the distinguished TM start state. All
product states are positive; zero remains reserved for halting. -/
def pack (start p : ℕ × ℕ) : ℕ := if p = start then 1 else Nat.pair p.1 p.2 + 2

def unpack (start : ℕ × ℕ) (n : ℕ) := if n = 1 then start else (n-2).unpair

theorem unpack_pack (start p : ℕ × ℕ) : unpack start (pack start p) = p := by
  by_cases h : p = start
  · simp [pack,unpack,h]
  · simp [pack,unpack,h]

theorem pack_ne_zero (start p : ℕ × ℕ) : pack start p ≠ 0 := by simp [pack]; split <;> omega

def product [Fintype σ] (U V : Table (Action σ)) (blank : σ) : TuringProgram σ :=
  let start := (U.start,V.start)
  let scope := (U.states ×ˢ V.states).image (pack start)
  (tabulate 1 scope (blank,TuringHeadMove.stay) (fun n (a : σ) ↦
    let p := unpack start n
    let u := U.step p.1 a
    let v := V.step p.2 a
    (if v.2.2 = .stay then 0 else pack start (u.1,v.1),u.2))).rows

theorem product_step [Fintype σ] (U V : Table (Action σ)) (blank a : σ) (p : ℕ × ℕ)
    (hu : p.1 ∈ U.states) (hv : p.2 ∈ V.states) :
    (product U V blank).instruction (pack (U.start,V.start) p) a =
      (if (V.step p.2 a).2.2 = .stay then 0 else
        pack (U.start,V.start) ((U.step p.1 a).1,(V.step p.2 a).1),(U.step p.1 a).2) := by
  have hp : pack (U.start,V.start) p ∈ (U.states ×ˢ V.states).image (pack (U.start,V.start)) :=
    Finset.mem_image.mpr ⟨p,Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩
  unfold TuringProgram.instruction product
  rw [tabulate_row _ _ _ _ hp]
  simp [unpack_pack]

theorem CorrectAt.head {T : Table (Action σ)} {q b label a v es}
    (h : CorrectAt T q b label ((a,v)::es)) : (T.step q a).2 = label v es.isEmpty :=
  h [a] _ (List.mem_cons_self ..)

theorem CorrectAt.tail {T : Table (Action σ)} {q b label a v es}
    (h : CorrectAt T q b label ((a,v)::es)) :
    CorrectAt T (T.step q a).1 (T.step q a).2 label es := by
  intro w v' hv
  exact h (a::w) v' (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(w,v'),hv,rfl⟩))

/-- Agreement of both policies on every observed prefix forces the product to
make exactly the recorded moves and halt on the original final tape. -/
theorem replay [Fintype σ] {P : TuringProgram σ} {blank q t es out}
    (h : Execution P blank q t es out) (U V : Table (Action σ)) (u v : ℕ)
    (hu : u ∈ U.states) (hv : v ∈ V.states) (bu bv : Action σ)
    (ha : CorrectAt U u bu (fun a _ ↦ a) es)
    (hm : CorrectAt V v bv (fun _ done ↦ marker blank done) es) :
    Execution (product U V blank) blank
      (if q = 0 then 0 else pack (U.start,V.start) (u,v)) t es out := by
  induction h generalizing u v bu bv with
  | halt => simp; exact .halt _
  | @step q t es out hn tail ih =>
    rw [if_neg hn]
    let a := t.scanned
    let tr := P.instruction q a
    let u' := (U.step u a).1
    let v' := (V.step v a).1
    have hbit : (V.step v a).2.2 = .stay ↔ tr.1 = 0 := by
      rw [hm.head]
      cases es <;> simp_all [marker,tr,a,tail.halt_iff]
    have hstep : (product U V blank).instruction (pack (U.start,V.start) (u,v)) a =
        (if tr.1 = 0 then 0 else pack (U.start,V.start) (u',v'),tr.2) := by
      rw [product_step U V blank a (u,v) hu hv]
      simp only [hbit]
      exact congrArg (fun b ↦ (_,b)) ha.head
    have recu := ih u' v' (U.step_closed u a) (V.step_closed v a) _ _ ha.tail hm.tail
    have step := @Execution.step σ _ (product U V blank) blank (pack (U.start,V.start) (u,v))
      t es out (pack_ne_zero _ _)
    simp only [show t.scanned = a from rfl,hstep] at step
    exact step recu

end GenLimit.LearningAlgorithmsLimit.Policy
