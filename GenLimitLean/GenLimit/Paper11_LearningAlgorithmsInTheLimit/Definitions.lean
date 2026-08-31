import GenLimit.Core.GenericGeneration
import GenLimit.Core.Identification
import Mathlib.Data.Set.Finite.Basic

/-!
# Learning algorithms in the limit: semantic framework

Source: Hristo Papazov and Nicolas Flammarion,
*Learning Algorithms in the Limit*, PMLR 291 (COLT 2025), 4486--4510.

This file records the quantifier structure of Definition 7.  In particular,
one learner consumes finite ordered observation histories and must work for
every target model, restricted source, and exhaustive ordering.  Target
models and the learner's output representations are intentionally separate
types.

Computability of a concrete learner is established by defining an executable
Lean function.  The semantic interfaces below do not declare every function
inhabiting their types to be computable.
-/

namespace GenLimit.LearningAlgorithmsLimit

/-- An exact presentation of a restricted input source.  This is the shared
paper-independent `Generic.Presents` notion: repetitions are allowed, every
presented input lies in the source, and every source input eventually occurs. -/
abbrev Covers (stream : ℕ → Input) (source : Set Input) : Prop :=
  GenLimit.Generic.Presents stream source

theorem covers_stream_mem
    {stream : ℕ → Input} {source : Set Input}
    (hcover : Covers stream source) (n : ℕ) :
    stream n ∈ source := by
  rw [← hcover]
  exact ⟨n, rfl⟩

theorem covers_exists_eq
    {stream : ℕ → Input} {source : Set Input}
    (hcover : Covers stream source) {x : Input} (hx : x ∈ source) :
    ∃ n, stream n = x := by
  rw [← hcover] at hx
  exact hx

/-- Agreement of two representations on a restricted input source. -/
def AgreeOn
    (semantics : Rep → Input → Option Output)
    (source : Set Input) (i j : Rep) : Prop :=
  ∀ x ∈ source, semantics i x = semantics j x

/-- Correctness of a representation on a restricted source. -/
def CorrectOn
    (semantics : Rep → Input → Option Output)
    (target : Input → Option Output)
    (source : Set Input) (representation : Rep) : Prop :=
  ∀ x ∈ source, semantics representation x = target x

/-- A partial target is defined at every input in the restricted source. -/
def DefinedOn
    (target : Input → Option Output) (source : Set Input) : Prop :=
  ∀ x ∈ source, ∃ y, target x = some y

/-- Identification in the limit relative to an arbitrary correctness
criterion.  This form is useful when representations have relational
semantics, as concrete Turing machines do. -/
def LearnsByCriterion
    (learner : GenLimit.Learner Info Rep)
    (information : ℕ → Info)
    (correct : Rep → Prop) : Prop :=
  ∃ representation, correct representation ∧
    GenLimit.StabilizesTo
      (fun t => learner (GenLimit.textPrefix information t))
      representation

/-- Definition 7 for one target/source/presentation.  Unlike the previous
target-specific guess-sequence interface, `learner` receives only the finite
ordered observation history. -/
def LearnsInLimit
    (learner : GenLimit.Learner Info Rep)
    (information : ℕ → Info)
    (semantics : Rep → Input → Option Output)
    (target : Input → Option Output)
    (source : Set Input) : Prop :=
  LearnsByCriterion learner information
    (CorrectOn semantics target source)

/-- The full model-class quantifier structure of Definition 7.  A single
learner must succeed for every target model, every source contained in its
halting domain, and every exact presentation of that source. -/
def SolvesLearningProblem
    (modelClass : Set Model)
    (modelSemantics : Model → Input → Option Output)
    (observe : Model → Input → Info)
    (representationSemantics : Rep → Input → Option Output)
    (learner : GenLimit.Learner Info Rep) : Prop :=
  ∀ model ∈ modelClass, ∀ source stream,
    DefinedOn (modelSemantics model) source →
    Covers stream source →
    LearnsInLimit learner
      (fun n => observe model (stream n))
      representationSemantics (modelSemantics model) source

end GenLimit.LearningAlgorithmsLimit
