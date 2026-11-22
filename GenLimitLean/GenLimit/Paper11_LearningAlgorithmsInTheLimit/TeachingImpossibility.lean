import GenLimit.Paper11_LearningAlgorithmsInTheLimit.SelectorBound
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.PolicyTrajectories

/-! # Theorem 17 and Corollary 18 on finite single-tape Turing machines -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open EffectiveTable
variable {Γ α : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] [Primcodable Γ] [Primcodable α] [Finite α]

/-- Definition 8 on the full source, intersected with the teacher's domain. -/
def Characteristic (ι : α ↪ Γ) (A : Set (List α × O) → R) (rep : R → List α → Option (List α))
    (obs : TuringProgram Γ → List α → O) (P : TuringProgram Γ) (S : Set (List α)) : Prop :=
  IsCharacteristicSet A obs (wordSem ι) rep (wordDomain ι P) P S

/-- Effective selection uses the finite transition list, with three head
moves encoded by an optional bit. Packing and unpacking are mutually inverse. -/
def HasSelector (ι : α ↪ Γ) (A : Set (List α × O) → R) (rep : R → List α → Option (List α))
    (obs : TuringProgram Γ → List α → O) : Prop :=
  ∃ C : EffectiveTable.Table Γ → List (List α), Computable C ∧ ∀ T,
    Characteristic ι A rep obs (unpack T) {x | x ∈ C T}

theorem no_selector (ι : α ↪ Γ) (noBlank : ∀ a, ι a ≠ default) (a : α)
    (A : Set (List α × O) → R) (rep : R → List α → Option (List α))
    (obs : TuringProgram Γ → List α → O) : ¬ HasSelector ι A rep obs := by
  classical
  rintro ⟨C,hC,cert⟩
  obtain ⟨f,hf,cap⟩ := selector_capacity ι C hC (fun T _ hx ↦ (cert T).1 hx)
  let numeric := fun n : ℕ ↦ f ((Encodable.decode (α := EffectiveTable.Table Γ) n).getD [])
  have hc : Computable numeric := hf.comp (Computable.option_getD Computable.decode (Computable.const []))
  obtain ⟨g,hg,bound⟩ := bounded_indices (ι a) numeric hc
  let β := fun P : TuringProgram Γ ↦ f (pack P)
  have ub c : β (constantTeacher (ι a) c) ≤ g c := by
    simpa [β,numeric] using bound c _ (pack_le (constantTeacher (ι a) c))
  apply no_output_bound ι noBlank a A rep obs β g hg ub
  intro P _
  refine ⟨(C (pack P)).toFinset,?_,?_⟩
  · simpa [Characteristic] using cert (pack P)
  · intro x hx y hy
    exact cap (pack P) x (by simpa using hx) y (by simpa using hy)

inductive Mode | inputOutput | timeBound | policyTrajectory

abbrev WordObservation (α Γ : Type) := Option (List α) × (Unit ⊕ ℕ ⊕ List (Policy.Event Γ))

noncomputable def trajectory (ι : α ↪ Γ) (P : TuringProgram Γ) (x : List α) : List (Policy.Event Γ) := by
  classical
  exact if h : ∃ es out, Policy.Execution P default 1 (initialWord ι x) es out then h.choose else []

theorem trajectory_correct (ι : α ↪ Γ) {P x y} (hy : wordSem ι P x = some y) :
    ∃ out, Policy.Execution P default 1 (initialWord ι x) (trajectory ι P x) out := by
  classical
  obtain ⟨n,hn⟩ := run_of_wordSem ι hy
  simp only [TuringProgram.runWithin,wordIO] at hn
  split at hn
  · rename_i hs
    obtain ⟨es,he⟩ := Policy.execution_of_run P default n 1 (initialWord ι x) hs
    have ex : ∃ es out, Policy.Execution P default 1 (initialWord ι x) es out := ⟨es,_,he⟩
    simpa [trajectory,dif_pos ex] using ex.choose_spec
  · contradiction

/-- The input is carried by the example-set interface. The other fields
supply the output and the side information available in the chosen mode.
The time-bound case allows any upper-bound convention. -/
noncomputable def observed (m : Mode) (ι : α ↪ Γ) (clock : TuringProgram Γ → List α → ℕ)
    (P : TuringProgram Γ) (x : List α) : WordObservation α Γ :=
  (wordSem ι P x,match m with
    | .inputOutput => .inl ()
    | .timeBound => .inr (.inl (clock P x))
    | .policyTrajectory => .inr (.inr (trajectory ι P x)))

/-- Definition 8 charges both words and the chosen encoding of the side
information. Costs away from the teacher's domain never enter a sample. -/
noncomputable def exampleLength (m : Mode) (ι : α ↪ Γ) (clock : TuringProgram Γ → List α → ℕ)
    (sideLength : Unit ⊕ ℕ ⊕ List (Policy.Event Γ) → ℕ) (P : TuringProgram Γ) (x : List α) : ℕ :=
  let v := observed m ι clock P x
  x.length + (v.1.getD []).length + sideLength v.2

theorem output_le_exampleLength (m : Mode) (ι : α ↪ Γ) (clock : TuringProgram Γ → List α → ℕ)
    (sideLength : Unit ⊕ ℕ ⊕ List (Policy.Event Γ) → ℕ) {P x y}
    (h : wordSem ι P x = some y) : y.length ≤ exampleLength m ι clock sideLength P x := by
  simp only [exampleLength,observed,h,Option.getD_some]
  omega

def HasMass (ι : α ↪ Γ) (A : Set (List α × O) → R) (rep : R → List α → Option (List α))
    (obs : TuringProgram Γ → List α → O) (cost : TuringProgram Γ → List α → ℕ)
    (β : TuringProgram Γ → ℕ) : Prop :=
  ∀ P, linearTotal ι P → ∃ S : Finset (List α),
    Characteristic ι A rep obs P (↑S : Set _) ∧ ∑ x ∈ S, cost P x ≤ β P

/-- The paper counts states with the tape alphabet held fixed. -/
private theorem states_le (P : TuringProgram Γ) : (Policy.states P).card ≤ Encodable.encode P + 2 := by
  have h := Finset.card_insert_le 1 (insert 0 (P.map Prod.fst).toFinset)
  have j := Finset.card_insert_le 0 (P.map Prod.fst).toFinset
  have k := List.toFinset_card_le (P.map Prod.fst)
  have l := Encodable.length_le_encode P
  simp only [List.length_map] at k
  unfold Policy.states
  omega

/-- Already the polynomial-data requirement of IPTD is impossible. This
quantifies over all learners, including ones with unrestricted computation. -/
theorem no_polynomial_mass (ι : α ↪ Γ) (noBlank : ∀ a, ι a ≠ default) (a : α)
    (A : Set (List α × O) → R) (rep : R → List α → Option (List α))
    (obs : TuringProgram Γ → List α → O) (cost : TuringProgram Γ → List α → ℕ)
    (pays : ∀ P x y, wordSem ι P x = some y → y.length ≤ cost P x) :
    ¬ ∃ K d : ℕ, HasMass ι A rep obs cost (fun P ↦ K*((Policy.states P).card+1)^d) := by
  rintro ⟨K,d,all⟩
  have powPrim : Primrec₂ (fun a b : ℕ ↦ a^b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  have hc : Computable (fun n : ℕ ↦ K*(n+3)^d) := (Primrec.nat_mul.comp (Primrec.const K)
    (powPrim.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 3)) (Primrec.const d))).to_comp
  obtain ⟨g,hg,bound⟩ := bounded_indices (ι a) _ hc
  have ub c := (Nat.mul_le_mul_left K (Nat.pow_le_pow_left
    (show (Policy.states (constantTeacher (ι a) c)).card+1 ≤ Encodable.encode (constantTeacher (ι a) c)+3
      from Nat.succ_le_succ (states_le _)) d)).trans (bound c _ le_rfl)
  apply no_output_bound ι noBlank a A rep obs (fun P ↦ K*((Policy.states P).card+1)^d) g hg ub
  intro P hp
  obtain ⟨S,hS,hm⟩ := all P hp
  exact ⟨S,hS,fun x hx y hy ↦ (pays P x y hy).trans
    ((Finset.single_le_sum (fun i _ ↦ Nat.zero_le (cost P i)) hx).trans hm)⟩

end GenLimit.LearningAlgorithmsLimit.NativeTape
