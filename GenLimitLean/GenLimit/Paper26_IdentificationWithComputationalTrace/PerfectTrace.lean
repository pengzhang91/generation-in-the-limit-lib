import Mathlib.Computability.Tape
import GenLimit.Paper26_IdentificationWithComputationalTrace.Edits

/-! # Identification of finite-control Turing recognizers from accepting traces

States and tape symbols are named by natural numbers, with zero as blank.
An instruction both writes and moves, as in Definition 2. The head position
in a full configuration lets the learner read the direction of movement.
Looking back at the old head cell then recovers the written symbol.
-/
namespace GenLimit.ComputationalTrace
open Turing

structure Config where
  state : ℕ
  pos : ℤ
  tape : Tape ℕ

structure Instruction where
  source : ℕ
  read : ℕ
  dest : ℕ
  write : ℕ
  dir : Dir
  deriving DecidableEq

def Instruction.advance (r : Instruction) (c : Config) : Config :=
  ⟨r.dest, if r.dir = .left then c.pos - 1 else c.pos + 1,
    ({c.tape with head := r.write} : Tape ℕ).move r.dir⟩

def readInstruction (c d : Config) : Instruction :=
  let left := d.pos < c.pos
  ⟨c.state,c.tape.head,d.state,
    (d.tape.move (if left then .right else .left)).head, if left then .left else .right⟩

theorem read_advance (r : Instruction) (c : Config)
    (hs : r.source = c.state) (ha : r.read = c.tape.head) :
    readInstruction c (r.advance c) = r := by
  cases r with
  | mk q a p b dir =>
    change q = c.state at hs
    change a = c.tape.head at ha
    subst q
    subst a
    cases dir <;> simp [readInstruction,Instruction.advance, show c.pos - 1 < c.pos by omega,
      show ¬ c.pos + 1 < c.pos by omega, Tape.move_left_right, Tape.move_right_left]

inductive Fact where
  | rule (r : Instruction)
  | final (q : ℕ)
  deriving DecidableEq

structure Recognizer where
  initial : ℕ
  table : Finset Fact

def Recognizer.Deterministic (M : Recognizer) : Prop :=
  ∀ r s, Fact.rule r ∈ M.table → Fact.rule s ∈ M.table →
    r.source = s.source → r.read = s.read → r = s

structure Trace where
  first : Config
  rest : List Config

def pathFacts (c : Config) : List Config → Finset Fact
  | [] => {.final c.state}
  | d :: ds => insert (.rule (readInstruction c d)) (pathFacts d ds)

def Trace.facts (tr : Trace) := pathFacts tr.first tr.rest

/-- The local checks ensure that a purported full configuration sequence
really performs each inferred instruction, including its effect on the tape. -/
def LegalMoves (c : Config) : List Config → Prop
  | [] => True
  | d :: ds => (readInstruction c d).advance c = d ∧ LegalMoves d ds

variable {ι : Type*}

/-- Input symbols are assigned distinct nonblank tape codes. This covers
every fixed finite alphabet; the transition table may use auxiliary symbols. -/
def inputTape (code : ι ↪ ℕ) (x : List ι) : Tape ℕ :=
  Tape.mk₁ (x.map fun a => code a + 1)

def Recognizer.AcceptsTrace (M : Recognizer) (code : ι ↪ ℕ) (x : List ι) (tr : Trace) : Prop :=
  tr.first = ⟨M.initial,0,inputTape code x⟩ ∧ LegalMoves tr.first tr.rest ∧ tr.facts ⊆ M.table

def Recognizer.language (M : Recognizer) (code : ι ↪ ℕ) : Set (List ι) :=
  {x | ∃ tr, M.AcceptsTrace code x tr}

/-- Direct finite-table operational semantics, independent of trace extraction. -/
inductive AcceptingRun (M : Recognizer) : Config → Prop
  | stop (c) (hf : Fact.final c.state ∈ M.table) : AcceptingRun M c
  | step (c) (r : Instruction) (hr : Fact.rule r ∈ M.table)
      (hs : r.source = c.state) (ha : r.read = c.tape.head)
      (tail : AcceptingRun M (r.advance c)) : AcceptingRun M c

private theorem run_iff_tail (M : Recognizer) (c : Config) :
    AcceptingRun M c ↔ ∃ ds, LegalMoves c ds ∧ pathFacts c ds ⊆ M.table := by
  constructor
  · intro h
    induction h with
    | stop c hf => exact ⟨[], trivial,Finset.singleton_subset_iff.mpr hf⟩
    | step c r hr hs ha _ ih =>
      obtain ⟨ds,hlegal,hsub⟩ := ih
      rw [← read_advance r c hs ha] at hr
      refine ⟨r.advance c :: ds, ⟨by rw [read_advance r c hs ha],hlegal⟩,
        Finset.insert_subset hr hsub⟩
  · rintro ⟨ds,hlegal,hsub⟩
    induction ds generalizing c with
    | nil => exact .stop c (hsub (Finset.mem_singleton_self _))
    | cons d ds ih =>
      obtain ⟨heq,hm⟩ := hlegal
      apply AcceptingRun.step c (readInstruction c d) (hsub (Finset.mem_insert_self ..)) rfl rfl
      rw [heq]
      exact ih d hm (fun _ hx => hsub (Finset.mem_insert_of_mem hx))

theorem accepts_iff_run (M : Recognizer) (code : ι ↪ ℕ) (x : List ι) :
    x ∈ M.language code ↔ AcceptingRun M ⟨M.initial,0,inputTape code x⟩ := by
  rw [run_iff_tail]
  constructor
  · rintro ⟨⟨c,ds⟩,rfl,hm,hsub⟩
    exact ⟨ds,hm,hsub⟩
  · rintro ⟨ds,hm,hsub⟩
    exact ⟨⟨_,ds⟩,rfl,hm,hsub⟩

abbrev Example (ι : Type*) := List ι × Trace

def traceLearner (xs : List (Example ι)) : Recognizer :=
  ⟨(xs.head?.map (fun e => e.2.first.state)).getD 0,
    (xs.map (fun e => e.2.facts)).foldr (· ∪ ·) ∅⟩

private theorem mem_learned (xs : List (Example ι)) (a : Fact) :
    a ∈ (traceLearner xs).table ↔ ∃ e ∈ xs, a ∈ e.2.facts := by
  induction xs with
  | nil => simp [traceLearner]
  | cons e xs ih =>
    change a ∈ e.2.facts ∪ (traceLearner xs).table ↔ _
    simp [Finset.mem_union,ih]

/-- A presentation covers every accepted input and supplies an actual
accepting computation of the same target machine at every time. -/
def PerfectPresentation (M : Recognizer) (code : ι ↪ ℕ) (s : ℕ → Example ι) : Prop :=
  (∀ t, M.AcceptsTrace code (s t).1 (s t).2) ∧ Set.range (fun t => (s t).1) = M.language code

theorem identifies_perfect (M : Recognizer) (hM : M.Deterministic) (code : ι ↪ ℕ) (s : ℕ → Example ι)
    (hs : PerfectPresentation M code s) :
    ∃ H : Recognizer, H.Deterministic ∧ H.language code = M.language code ∧
      ∃ N, ∀ t ≥ N, traceLearner (textPrefix s t) = H := by
  classical
  obtain ⟨U,memU,N,stable⟩ := finite_observations_stabilize (fun n => (s n).2.facts) M.table
    (fun n => (hs.1 n).2.2)
  let H : Recognizer := ⟨M.initial,U⟩
  have sub : U ⊆ M.table := by
    intro a ha
    obtain ⟨n,hn⟩ := (memU a).mp ha
    exact (hs.1 n).2.2 hn
  refine ⟨H,fun r p hr hp => hM r p (sub hr) (sub hp),?_,?_⟩
  · ext x
    constructor
    · rintro ⟨tr,hi,hm,hf⟩
      exact ⟨tr,hi,hm,hf.trans sub⟩
    · intro hx
      obtain ⟨n,rfl⟩ := hs.2.symm ▸ hx
      obtain ⟨hi,hm,hf⟩ := hs.1 n
      exact ⟨_,hi,hm,fun a ha => (memU a).mpr ⟨n,ha⟩⟩
  · refine ⟨N+1, fun t ht => ?_⟩
    change Recognizer.mk _ _ = Recognizer.mk _ _
    rw [Recognizer.mk.injEq]
    constructor
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
      have first := congrArg Config.state (hs.1 0).1
      simpa [traceLearner,textPrefix,List.range_succ_eq_map] using first
    · ext a
      change a ∈ (traceLearner (textPrefix s t)).table ↔ a ∈ U
      rw [mem_learned,← stable t (by omega),Finset.mem_biUnion]
      constructor
      · rintro ⟨e,he,ha⟩
        obtain ⟨n,hn,rfl⟩ := mem_textPrefix_iff.mp he
        exact ⟨n,Finset.mem_range.mpr hn,ha⟩
      · rintro ⟨n,hn,ha⟩
        exact ⟨s n,mem_textPrefix_iff.mpr ⟨n,Finset.mem_range.mp hn,rfl⟩,ha⟩

end GenLimit.ComputationalTrace
