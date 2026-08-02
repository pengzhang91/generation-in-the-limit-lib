import GenLimit.Angluin
import Mathlib.Data.Countable.Defs

/-!
# Hallucination detection in the limit

Paper-facing definitions for Karbasi, Montasser, Sous, and Velegkas,
`(Im)possibility of Automated Hallucination Detection in Large Language Models`,
arXiv:2504.17004v2.

The source permits finitely many adaptive membership queries to the candidate
set in every round.  `OracleTree` records exactly such a finite interaction:
every internal node is one membership query and every leaf is a Boolean
answer.  Thus the semantic model below does not silently grant the detector
unrestricted access to the candidate set.
-/

namespace GenLimit.HallucinationDetection

open GenLimit.Generic

/-- A finite adaptive membership-query computation.  The first branch of a
query is followed when the queried point belongs to the oracle set. -/
inductive OracleTree (α : Type*) where
  | answer : Bool → OracleTree α
  | query : α → OracleTree α → OracleTree α → OracleTree α

namespace OracleTree

noncomputable local instance definitionsPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Evaluate a finite query tree against a set oracle. -/
noncomputable def eval (G : Set α) : OracleTree α → Bool
  | answer b => b
  | query x yes no => if x ∈ G then eval G yes else eval G no

end OracleTree

/-- A detector builds one finite adaptive query tree from each finite positive
history. -/
abbrev Detector (α : Type*) := ∀ t : ℕ, (Fin t → α) → OracleTree α

/-- Run a detector after the first `t` positive examples, with `G` as the
candidate set being checked for hallucinations. -/
noncomputable def detectorOutput
    (D : Detector α) (G : Set α) (stream : Stream α) (t : ℕ) : Bool :=
  OracleTree.eval G (D t (fun i => stream i))

/-- Correctness in one round: output `true` exactly when `G` is contained in
the target language. -/
def DetectorCorrectAt
    (D : Detector α) (G K : Set α) (stream : Stream α) (t : ℕ) : Prop :=
  detectorOutput D G stream t = true ↔ G ⊆ K

/-- Definition 1: `D` detects hallucinations in the limit for every indexed
target, every exact positive presentation, and every candidate set. -/
def DetectsHallucinations
    (D : Detector α) (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream (C z) → ∀ G : Set α,
    ∃ T, ∀ t, T ≤ t → DetectorCorrectAt D G (C z) stream t

/-- A collection admits hallucination detection in the limit. -/
def HallucinationDetectable
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ D : Detector α, DetectsHallucinations D C

/-- The semantic positive-data identification notion used in Theorem 2.1. -/
def IdentifiableInLimit
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    GenLimit.Angluin.SemanticallyIdentifies M C

/-! ## Labeled enumerations and negative examples -/

/-- A stream of domain points together with their target-membership labels. -/
abbrev LabeledStream (α : Type*) := ℕ → α × Bool

/-- A labeled enumeration lists the whole domain and labels every point
correctly for the target language. -/
def IsLabeledEnumeration (stream : LabeledStream α) (K : Set α) : Prop :=
  Set.range (fun n => (stream n).1) = Set.univ ∧
    ∀ n, (stream n).2 = true ↔ (stream n).1 ∈ K

/-- A detector in the negative-example model sees a finite labeled history
and may make finitely many adaptive membership queries to `G`. -/
abbrev NegativeExampleDetector (α : Type*) :=
  ∀ t : ℕ, (Fin t → α × Bool) → OracleTree α

noncomputable def negativeDetectorOutput
    (D : NegativeExampleDetector α) (G : Set α)
    (stream : LabeledStream α) (t : ℕ) : Bool :=
  OracleTree.eval G (D t (fun i => stream i))

def NegativeDetectorCorrectAt
    (D : NegativeExampleDetector α) (G K : Set α)
    (stream : LabeledStream α) (t : ℕ) : Prop :=
  negativeDetectorOutput D G stream t = true ↔ G ⊆ K

/-- Definition 2: detection in the limit from a complete labeled enumeration
of the domain. -/
def DetectsWithNegativeExamples
    (D : NegativeExampleDetector α)
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : LabeledStream α, IsLabeledEnumeration stream (C z) →
    ∀ G : Set α, ∃ T, ∀ t, T ≤ t →
      NegativeDetectorCorrectAt D G (C z) stream t

/-- A collection admits hallucination detection with negative examples. -/
def DetectableWithNegativeExamples
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ D : NegativeExampleDetector α, DetectsWithNegativeExamples D C

end GenLimit.HallucinationDetection
