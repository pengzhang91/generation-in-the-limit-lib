import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TuringMachines
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.Enumeration
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold

/-! # Effective representation of all finite Mealy transducers

The paper's rational function returns the final transition label on each
nonempty input word. Enumeration uses finite tables with a specified start
state. A finite abstract transducer is encoded by tabulating its transitions
on a finite set of natural keys. Every decoded table has a finite set of
reachable states, including its default state. -/
namespace GenLimit.LearningAlgorithmsLimit.Rational

structure Table (B : Type*) where
  start : ℕ
  rows : List (ℕ × B)
  fallback : B
  deriving Encodable

def Table.step [Encodable A] (T : Table B) (q : ℕ) (a : A) : ℕ × B :=
  (T.rows[Nat.pair q (Encodable.encode a)]?).getD (0,T.fallback)

/-- Evaluate a final-symbol rational function on a nonempty word; the empty
word is totalized by the table's fallback. -/
def Table.lastFrom [Encodable A] (T : Table B) (q : ℕ) (b : B) : List A → B
  | [] => b
  | a :: w => T.lastFrom (T.step q a).1 (T.step q a).2 w

def Table.output [Encodable A] (T : Table B) (w : List A) := T.lastFrom T.start T.fallback w

theorem Table.lastFrom_append [Encodable A] (T : Table B) (q : ℕ) (a : A)
    (b : B) (as : List A) :
    T.lastFrom q b (a::as) = T.lastFrom (T.step q a).1 (T.step q a).2 as := rfl

def Table.states (T : Table B) : Finset ℕ := insert T.start (insert 0 (T.rows.map Prod.fst).toFinset)

theorem Table.step_closed [Encodable A] (T : Table B) (q : ℕ) (a : A) :
    (T.step q a).1 ∈ T.states := by
  simp only [Table.states,Finset.mem_insert, List.mem_toFinset]
  unfold Table.step
  cases h : T.rows[Nat.pair q (Encodable.encode a)]? with
  | none => exact Or.inr (Or.inl rfl)
  | some v => exact Or.inr (Or.inr (List.mem_map.mpr ⟨v,List.mem_of_getElem? h,rfl⟩))

/-- Tabulate any transition function on a named finite set of states and
a finite input alphabet. Keys are decoded only in constructing the table. -/
def tabulate [Fintype A] [Encodable A] (start : ℕ) (states : Finset ℕ)
    (fallback : B) (step : ℕ → A → ℕ × B) : Table B :=
  let keys := (states ×ˢ (Finset.univ : Finset A)).image (fun p ↦ Nat.pair p.1 (Encodable.encode p.2))
  let row (key : ℕ) := match Encodable.decode key.unpair.2 with
    | some a => step key.unpair.1 a
    | none => (0,fallback)
  ⟨start,(List.range (keys.sup id + 1)).map row,fallback⟩

theorem tabulate_row [Fintype A] [Encodable A] (start : ℕ) (states : Finset ℕ)
    (fallback : B) (step : ℕ → A → ℕ × B) {q : ℕ} (hq : q ∈ states) (a : A) :
    (tabulate start states fallback step).rows[Nat.pair q (Encodable.encode a)]? = some (step q a) := by
  let keys := (states ×ˢ (Finset.univ : Finset A)).image (fun p ↦ Nat.pair p.1 (Encodable.encode p.2))
  have hk : Nat.pair q (Encodable.encode a) ∈ keys :=
    Finset.mem_image.mpr ⟨(q,a),Finset.mem_product.mpr ⟨hq,Finset.mem_univ _⟩,rfl⟩
  have hlt : Nat.pair q (Encodable.encode a) < keys.sup id + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  have hr : (List.range (keys.sup id + 1))[Nat.pair q (Encodable.encode a)]? =
      some (Nat.pair q (Encodable.encode a)) := by
    rw [List.getElem?_eq_getElem (by simpa using hlt)]; simp
  simp only [tabulate,List.getElem?_map]
  rw [hr]
  simp

theorem tabulate_step [Fintype A] [Encodable A] (start : ℕ) (states : Finset ℕ)
    (fallback : B) (step : ℕ → A → ℕ × B) {q : ℕ} (hq : q ∈ states) (a : A) :
    (tabulate start states fallback step).step q a = step q a := by
  rw [Table.step,tabulate_row _ _ _ _ hq]
  rfl

/-- Encoding of any finite-state transition diagram. -/
noncomputable def ofFinite [Fintype Q] [Fintype A] [Encodable A] (start : Q)
    (b : B) (step : Q → A → Q × B) : Table B := by
  classical
  let e := Fintype.equivFin Q
  exact tabulate (e start).val (Finset.range (Fintype.card Q)) b (fun q a ↦
    if h : q < Fintype.card Q then
      let v := step (e.symm ⟨q,h⟩) a
      ((e v.1).val,v.2)
    else (0,b))

theorem ofFinite_step [Fintype Q] [Fintype A] [Encodable A] (start : Q)
    (b : B) (step : Q → A → Q × B) (q : Q) (a : A) :
    (ofFinite start b step).step ((Fintype.equivFin Q) q).val a =
      (((Fintype.equivFin Q) (step q a).1).val,(step q a).2) := by
  classical
  unfold ofFinite
  rw [tabulate_step _ _ _ _ (Finset.mem_range.mpr ((Fintype.equivFin Q) q).isLt)]
  simp

def decode [Encodable B] [Inhabited B] (n : ℕ) : Table B :=
  (Encodable.decode n).getD ⟨0,[],default⟩

def IOAlgorithm (A B : Type*) := GenLimit.Learner (LabeledObservation (List A) B) (Table B)

def Solves [Encodable A] (R : IOAlgorithm A B) : Prop :=
  ∀ (T : Table B) (s : ℕ → List A), (∀ n, s n ≠ []) →
    LearnsByCriterion R (labeledStream (fun w ↦ some (T.output w)) s)
      (fun E ↦ ∀ w ∈ Set.range s, E.output w = T.output w)

/-- No unknown target table or source is used by the algorithm. -/
def enumeration [Encodable A] [Encodable B] [Inhabited B] [DecidableEq B] :
    IOAlgorithm A B := fun h ↦ decode (labeledEnumerationLearner
      (fun n w ↦ some ((decode n : Table B).output w)) h)

theorem enumeration_solves [Encodable A] [Encodable B] [Inhabited B] [DecidableEq B] :
    Solves (enumeration : IOAlgorithm A B) := by
  intro T s _
  let sem := fun n (w : List A) ↦ some ((decode n : Table B).output w)
  have hw : CorrectOn sem (fun w ↦ some (T.output w)) (Set.range s) (Encodable.encode T) := by
    intro w _
    simp [sem,decode]
  obtain ⟨n,hc,N,hN⟩ := enumeration_learnsInLimit sem _ s (Set.range s) rfl ⟨_,hw⟩
  exact ⟨decode n,fun w hw ↦ Option.some.inj (hc w hw),N,fun t ht ↦ congrArg decode (hN t ht)⟩

end GenLimit.LearningAlgorithmsLimit.Rational
