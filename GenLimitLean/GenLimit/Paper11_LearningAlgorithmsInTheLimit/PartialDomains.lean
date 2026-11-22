import GenLimit.Paper11_LearningAlgorithmsInTheLimit.CharacteristicSets
import Mathlib.Computability.Partrec

/-! # Positive observations on partial domains

In Definitions 7 and 8 a representation need only agree with its teacher
on the teacher's defined inputs. Consider the zero program and a program
that diverges at 1 and outputs zero everywhere else. The same zero program
is a correct stable guess for either teacher on every legal input source.
Their singleton characteristic sets can therefore coincide. -/
namespace GenLimit.LearningAlgorithmsLimit.PartialDomains

/-- The flag selects whether the program diverges at the one exceptional input. -/
def value : Bool → ℕ → Option ℕ
  | false, _ => some 0
  | true, x => if x = 1 then none else some 0

def domain (m : Bool) : Set ℕ := {x | ∃ y, value m x = some y}

theorem effective (m : Bool) : Partrec (fun x ↦ (value m x : Part ℕ)) := by
  apply Computable.ofOption
  cases m with
  | false => exact Computable.const _
  | true =>
    exact (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
      (Primrec.const none) (Primrec.const (some 0))).to_comp

theorem domain_infinite (m : Bool) : (domain m).Infinite := by
  have hs : ({1} : Set ℕ)ᶜ ⊆ domain m := by
    intro x hx
    have h : x ≠ 1 := hx
    cases m <;> exact ⟨0,by simp [value,h]⟩
  exact (Set.finite_singleton 1).infinite_compl.mono hs

private theorem zero_correct (m : Bool) {S : Set ℕ} (hS : DefinedOn (value m) S) :
    CorrectOn value (value m) S false := by
  intro x hx
  obtain ⟨y,hy⟩ := hS x hx
  cases m with
  | false => rfl
  | true =>
    by_cases h : x = 1
    · simp [value,h] at hy
    · simp [value,h]

/-- On legal inputs the IOO value is zero for both teachers. The input
itself is also part of every observation sent to the history learner. -/
theorem solves : SolvesLearningProblem Set.univ value (fun _ x ↦ (x,(0 : ℕ)))
    value (fun _ ↦ false) := by
  intro m _ S s hS _
  exact ⟨false,zero_correct m hS,0,fun _ _ ↦ rfl⟩

theorem characteristic (m : Bool) :
    IsCharacteristicSet (fun _ ↦ false) (fun _ _ ↦ (0 : ℕ)) value value
      (Set.univ ∩ domain m) m {0} := by
  refine ⟨?_,fun _ _ _ ↦ zero_correct m (fun _ hx ↦ hx.2)⟩
  rintro _ (rfl : _ = 0)
  exact ⟨trivial,0,by cases m <;> decide⟩

/-- Counterexample to the distinguishability conclusion of Lemmas 9 and
25 for the paper's teacher-relative positive-observation hypotheses. -/
theorem lemma_9_counterexample :
    SolvesLearningProblem Set.univ value (fun _ x ↦ (x,(0 : ℕ))) value (fun _ ↦ false) ∧
    (∀ m, Partrec (fun x ↦ (value m x : Part ℕ)) ∧ (domain m).Infinite ∧
      IsCharacteristicSet (fun _ ↦ false) (fun _ _ ↦ (0 : ℕ)) value value
        (Set.univ ∩ domain m) m {0}) ∧
    ¬AgreeOn value Set.univ false true ∧
    ¬∃ x ∈ ({0} : Set ℕ) ∪ {0}, x ∉ domain false ∩ domain true ∨ value false x ≠ value true x := by
  refine ⟨solves,fun m ↦ ⟨effective m,domain_infinite m,characteristic m⟩,?_,?_⟩
  · intro h
    have hx := h 1 trivial
    simp [value] at hx
  · rintro ⟨x,hx,hd⟩
    have : x = 0 := by simpa using hx
    subst x
    simp [domain,value] at hd

end GenLimit.LearningAlgorithmsLimit.PartialDomains
