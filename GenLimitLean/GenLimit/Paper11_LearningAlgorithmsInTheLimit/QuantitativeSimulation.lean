import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TimeBounds

/-! # Quantitative simulation and the IOO/TBO theorems

The quantitative Extended Church–Turing thesis is an explicit assumption
about physical teachers on their defined inputs. It bounds the run of one
finite Turing program per teacher under the fixed input/output encoding.
The learner enumerates program codes and numerical overhead parameters
together. A hypothesis cannot change its budget after a rejected example.
-/
namespace GenLimit.LearningAlgorithmsLimit
namespace TuringProgram

private theorem run_halted [Encodable σ] (P : TuringProgram σ) (blank : σ)
    {c : TuringConfiguration σ} (hc : c.state = 0) (n : ℕ) :
    P.runConfiguration blank n c = c := by
  cases n <;> simp [runConfiguration,step,hc]

theorem run_add [Encodable σ] (P : TuringProgram σ) (blank : σ)
    (m n : ℕ) (c : TuringConfiguration σ) :
    P.runConfiguration blank (m+n) c =
      P.runConfiguration blank n (P.runConfiguration blank m c) := by
  induction m generalizing c with
  | zero => simp [runConfiguration]
  | succ m ih =>
    rw [Nat.succ_add,runConfiguration,runConfiguration]
    cases h : P.step blank c with
    | none =>
      have hc : c.state = 0 := by by_contra hn; simp [step,hn] at h
      simp [run_halted P blank hc n]
    | some c' => simpa using ih c'

theorem runWithin_mono [Encodable σ] (P : TuringProgram σ) (io : TuringIO σ X Y)
    {a b : ℕ} (hab : a ≤ b) {x : X} {y : Y}
    (h : P.runWithin a io x = some y) : P.runWithin b io x = some y := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hab
  let c : TuringConfiguration σ := ⟨1,io.initTape x⟩
  have hc : (P.runConfiguration io.blank a c).state = 0 := by
    by_contra hn
    change (if (P.runConfiguration io.blank a c).state = 0 then _ else none) = _ at h
    simp [hn] at h
  unfold runWithin at *
  rw [run_add,run_halted P io.blank hc]
  exact h

end TuringProgram
namespace Quantitative

/-- The clock is measured only where the teacher halts. Values assigned off
the domain have no influence on the assumptions, data or correctness. -/
structure Teacher (X Y : Type*) where
  domain : Set X
  value : X → Y
  steps : X → ℕ

/-- Quantitative ECTT for a collection and a fixed encoding, as in equation
(4). One overhead constant and one finite transition table cover every
halting input of the teacher. -/
def QECTT [Encodable σ] (io : TuringIO σ X Y) (q : ℕ → ℕ → ℕ)
    (M : Set (Teacher X Y)) : Prop :=
  ∀ m ∈ M, ∃ (c : ℕ) (P : TuringProgram σ), ∀ x ∈ m.domain,
    P.runWithin (q c (m.steps x)) io x = some (m.value x)

/-- Definition 11 for a fixed witness teacher and size encoding. -/
def TimeRestricted (size : X → ℕ) (Q : ℕ → ℕ → ℕ) (m : Teacher X Y) : Prop :=
  ∃ c C : ℕ, ∀ x ∈ m.domain, m.steps x ≤ C * Q c (size x)

/-- Joint effective enumeration of scale, bound parameter, overhead, and
finite program. Every finite tuple is included. -/
def prog [Encodable σ] (n : ℕ) : TuringProgram σ := decodeTuringProgram n.unpair.2

def encode [Encodable σ] (a b c : ℕ) (P : TuringProgram σ) : ℕ :=
  Nat.pair (Nat.pair a (Nat.pair b c)) (Encodable.encode P)

def ioRun [Encodable σ] (io : TuringIO σ X Y) (q Q : ℕ → ℕ → ℕ)
    (size : X → ℕ) (n : ℕ) (x : X) : Option Y :=
  let params := n.unpair.1.unpair
  (prog n).runWithin (q params.1 (params.2.unpair.1 * Q params.2.unpair.2 (size x))) io x

def tbRun [Encodable σ] (io : TuringIO σ X Y) (q : ℕ → ℕ → ℕ)
    (n : ℕ) (x : X) (bound : ℕ) : Option Y :=
  let params := n.unpair.1.unpair
  (prog n).runWithin (q params.1 (params.2.unpair.1 * bound)) io x

/-- Uniform IOO learner for concrete bounded Turing simulations. The theorem
returns a stable, decoded machine computing every source label. -/
theorem learns_io [Encodable σ] [DecidableEq Y] (io : TuringIO σ X Y)
    (q Q : ℕ → ℕ → ℕ) (size : X → ℕ) (m : Teacher X Y)
    (P : TuringProgram σ) (a b c : ℕ) (I : Set X) (s : ℕ → X) (hs : Covers s I)
    (hr : ∀ x ∈ I, P.runWithin (q a (b * Q c (size x))) io x = some (m.value x)) :
    LearnsByCriterion (labeledEnumerationLearner (ioRun io q Q size))
      (labeledStream (fun x ↦ some (m.value x)) s)
      (fun n ↦ TuringComputesOn io (prog n) m.value I) := by
  have witness : CorrectOn (ioRun io q Q size) (fun x ↦ some (m.value x)) I (encode a b c P) := by
    intro x hx
    simpa [ioRun,prog,encode] using hr x hx
  obtain ⟨n,hn,stable⟩ := enumeration_learnsInLimit (ioRun io q Q size)
    (fun x ↦ some (m.value x)) s I hs ⟨_,witness⟩
  exact ⟨n,fun x hx ↦ ⟨_,hn x hx⟩,stable⟩

/-- Theorem 12: one IOO learner works simultaneously for all restricted
models, input sources and presentations. Only the simulation thesis is
assumed; bounded-representative existence is derived from Definition 11. -/
theorem theorem_12 [Encodable σ] [DecidableEq Y] (io : TuringIO σ X Y)
    (q Q : ℕ → ℕ → ℕ) (size : X → ℕ) (hq : ∀ a, Monotone (q a))
    (M : Set (Teacher X Y)) (thesis : QECTT io q M) :
    ∀ m ∈ M, TimeRestricted size Q m → ∀ (I : Set X), I ⊆ m.domain → ∀ s, Covers s I →
      LearnsByCriterion (labeledEnumerationLearner (ioRun io q Q size))
        (labeledStream (fun x ↦ some (m.value x)) s)
        (fun n ↦ TuringComputesOn io (prog n) m.value I) := by
  rintro m hm ⟨c,b,hb⟩ I hI s hs
  obtain ⟨a,P,hP⟩ := thesis m hm
  exact learns_io io q Q size m P a b c I s hs (fun x hx ↦ P.runWithin_mono io
    (hq a (hb x (hI hx))) (hP x (hI hx)))

/-- Corollary 13 uses actual finite Turing programs at the identity overhead.
No simulation thesis is required for this specialization. -/
theorem corollary_13 [Encodable σ] [DecidableEq Y] (io : TuringIO σ X Y)
    (Q : ℕ → ℕ → ℕ) (size : X → ℕ) (P : TuringProgram σ)
    (domain : Set X) (value : X → Y)
    (timeBound : ∃ b c : ℕ, ∀ x ∈ domain, P.runWithin (b * Q c (size x)) io x = some (value x)) :
    ∀ (I : Set X), I ⊆ domain → ∀ s, Covers s I →
      LearnsByCriterion (labeledEnumerationLearner (ioRun io (fun _ t ↦ t) Q size))
        (labeledStream (fun x ↦ some (value x)) s)
        (fun n ↦ TuringComputesOn io (prog n) value I) := by
  obtain ⟨b,c,h⟩ := timeBound
  intro I hI s hs
  exact learns_io io (fun _ t ↦ t) Q size ⟨domain,value,fun _ ↦ 0⟩ P 0 b c I s hs
    (fun x hx ↦ h x (hI hx))

/-- Theorem 14: the clock observation may overestimate or underestimate
runtime within the printed one-sided multiplicative bound. The single
learner uses only the observed triples and the common simulation overhead. -/
theorem theorem_14 [Encodable σ] [DecidableEq Y] (io : TuringIO σ X Y) (q : ℕ → ℕ → ℕ)
    (hq : ∀ a, Monotone (q a)) (M : Set (Teacher X Y)) (thesis : QECTT io q M) :
    ∀ m ∈ M, ∀ (I : Set X), I ⊆ m.domain → ∀ (obs : X → TimeBoundObservation X Y),
      (∀ x ∈ I, (obs x).input = x ∧ (obs x).value = m.value x) →
      (∃ b : ℕ, ∀ x ∈ I, m.steps x ≤ b * (obs x).timeBound) → ∀ s, Covers s I →
        LearnsByCriterion (timeObservedLearner (tbRun io q)) (fun n ↦ obs (s n))
          (fun n ↦ TuringComputesOn io (prog n) m.value I) := by
  rintro m hm I hI obs hv ⟨b,hb⟩ s hs
  obtain ⟨a,P,hP⟩ := thesis m hm
  have witness : TimeObservedCorrectOn (tbRun io q) obs I (encode a b 0 P) := by
    intro x hx
    rw [(hv x hx).2]
    simpa [tbRun,prog,encode] using P.runWithin_mono io (hq a (hb x hx)) (hP x (hI hx))
  obtain ⟨n,hn,stable⟩ := theorem_14_universalTBO_core (tbRun io q) obs s I hs
    (fun x hx ↦ (hv x hx).1) ⟨_,witness⟩
  refine ⟨n,fun x hx ↦ ⟨q n.unpair.1.unpair.1 (n.unpair.1.unpair.2.unpair.1 * (obs x).timeBound),?_⟩,stable⟩
  exact (hn x hx).trans (congrArg some (hv x hx).2)

end Quantitative
end GenLimit.LearningAlgorithmsLimit
