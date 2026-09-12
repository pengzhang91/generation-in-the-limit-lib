import GenLimit.Paper18_SafeLanguageGeneration.CorollarySixOneDiagnostic
import GenLimit.Paper18_SafeLanguageGeneration.Impossibility
import GenLimit.Paper18_SafeLanguageGeneration.InfiniteDifference
import GenLimit.Paper18_SafeLanguageGeneration.MachineEncoding
import GenLimit.Paper18_SafeLanguageGeneration.SafeIdentification

/-!
# Paper 18: main-results overview

This module is the public results facade for Anastasopoulos--Ateniese--
Kornaropoulos, *Safe Language Generation in the Limit*
(arXiv:2601.08648v2).  The declarations below are thin wrappers around the
canonical proof modules; no proof is duplicated here.

## Coverage and source qualifications

The development formalizes the paper's deterministic semantic model over
explicitly indexed countable families.  It does not claim an extracted
implementation or running-time bound.

* Theorem 3.1 is a deterministic repair.  Definition 1's instruction to
  insert the safe difference at a "random location" gives no probability
  law, quantifier over locations, or information model.  Lean instead proves
  a stronger fixed-family impossibility in which every relevant difference
  is already extensionally represented.
* Theorem 5.1 is proved after repairing Algorithm 1's finite-run reset: every
  candidate call is a prefix of one fixed infinite labeled presentation, so
  the safe generator's limit guarantee applies.
* Theorem 6.1 uses the conventional representation by pairs of Mathlib
  partial-recursive program codes.  Valid inputs are total Boolean deciders
  for infinite languages.  `MachineEncoding.lean` proves that every
  computable predicate has such a code, so the representation covers all
  recursive languages.  The lower-level hard subclass and generic
  representation-transport theorem remain available separately.
* The printed Corollary 6.1 reduction does not prove the claimed consequence.
  Its empty and singleton cases both fall in Definition 2's eventual-bottom
  branch; the collapse is formalized as a diagnostic below.
* Theorem 6.2 is a repaired semantic/oracle theorem.  The printed proof only
  assumes its key family property and treats non-occurrence as observable;
  Lean instead derives the result from Theorem 5.1 and an explicit
  non-identifiable family already checked in Paper 28.
* Theorem 6.3 is fully represented at the paper's explicit indexed-family
  semantic interface.
-/

namespace GenLimit.SafeGeneration.Results

open GenLimit.Generic

/-! ## Safe identification -/

/-- Deterministic fixed-family repair of Theorem 3.1. -/
theorem theorem_3_1 :
    (∀ i,
      (SafeIdentification.candidateFamily i).Infinite) ∧
    (∀ j,
      (SafeIdentification.harmfulFamily j).Infinite) ∧
    (∀ j, SafeIdentification.DifferenceRepresented
      SafeIdentification.candidateFamily
      (SafeIdentification.candidateFamily 0)
      (SafeIdentification.harmfulFamily j)) ∧
    ∀ M : SafeIdentification.SafeIdentifier SafeIdentification.Point,
      ∃ j, SafeIdentification.DifferenceRepresented
          SafeIdentification.candidateFamily
          (SafeIdentification.candidateFamily 0)
          (SafeIdentification.harmfulFamily j) ∧
        LabeledPresents (SafeIdentification.diagonalStream M)
          (SafeIdentification.candidateFamily 0)
          (SafeIdentification.harmfulFamily j) ∧
        ¬ SafeIdentification.SafelyIdentifiesFrom M
          SafeIdentification.candidateFamily
          (SafeIdentification.candidateFamily 0)
          (SafeIdentification.harmfulFamily j)
          (SafeIdentification.diagonalStream M) :=
  SafeIdentification.theorem_3_1_deterministic_repair

/-! ## Safe generation versus identification -/

/-- Repaired, prefix-compatible semantic form of Theorem 5.1. -/
theorem theorem_5_1 [Countable α]
    (G : SafeGenerator (α × ℕ))
    (C : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (C i).Infinite)
    (hFamilies :
      SafelyGeneratesFamilies G
        (fun i => verticalPad (C i))
        (fun i => verticalPad (C i))) :
    ∃ M : GenLimit.Angluin.SemanticIdentifier α,
      GenLimit.Angluin.SemanticallyIdentifies M C :=
  GenLimit.SafeGeneration.theorem_5_1
    G C hInfinite hFamilies

/-! ## Difference emptiness and impossibility -/

/-- Theorem 6.1 for pairs of total Boolean partial-recursive language-decider
codes, restricted by the promise that both represented languages are
infinite. -/
theorem theorem_6_1 :
    ¬∃ P : DiffEmpty.MachineEncoding.LanguagePairCode → Prop,
      ComputablePred P ∧
        ∀ pair, DiffEmpty.MachineEncoding.IsValidLanguagePair pair →
          (P pair ↔ DiffEmpty.MachineEncoding.CodedDiffEmpty pair) :=
  DiffEmpty.MachineEncoding.theorem_6_1_machine_codes

/-- The encoded hard subclass used internally to prove Theorem 6.1. -/
theorem theorem_6_1_restricted :
    ¬ComputablePred DiffEmpty.DiffEmptyInstance :=
  DiffEmpty.theorem_6_1_restricted

/-- Representation-independent transport form of Theorem 6.1. -/
theorem theorem_6_1_of_hard_embedding
    {Rep : Type*} [Primcodable Rep]
    (left right : Rep → Set ℕ)
    (encode : Nat.Partrec.Code → Rep)
    (hencode : Computable encode)
    (hcorrect :
      ∀ c,
        left (encode c) \ right (encode c) = ∅ ↔
          DiffEmpty.DiffEmptyInstance c) :
    ¬ComputablePred
      (fun r => left r \ right r = ∅) :=
  DiffEmpty.diffEmpty_not_computable_of_hard_embedding
    left right encode hencode hcorrect

/-- Diagnostic for the printed Corollary 6.1 reduction: both source cases
require exactly eventual bottom under Definition 2. -/
theorem corollary_6_1_printed_reduction_collapses
    (G : SafeGenerator ℕ)
    (stream : Stream (Tagged ℕ))
    (c : Nat.Partrec.Code) :
    SafelyGenerates G DiffEmpty.leftLanguage
        (DiffEmpty.PrintedReduction.printedRightLanguage c) stream ↔
      EventuallyBottom G stream :=
  DiffEmpty.PrintedReduction.printed_corollary_6_1_reduction_collapses
    G stream c

/-- Repaired oracle-facing form of Theorem 6.2. -/
theorem theorem_6_2 :
    ∃ targets harmfuls : Generic.LanguageFamily (ℕ × ℕ),
      (∀ i, (targets i).Infinite) ∧
      (∀ j, (harmfuls j).Infinite) ∧
      ∀ O : SetDifferenceOracle (ℕ × ℕ),
        IsCorrectSetDifferenceOracle O →
        ∀ A : OracleSafeAlgorithm (ℕ × ℕ),
          ¬ SafelyGeneratesFamilies (A O) targets harmfuls :=
  GenLimit.SafeGeneration.corrected_theorem_6_2_with_oracle

/-! ## Infinite cross-differences -/

/-- Theorem 6.3 for explicit indexed families. -/
theorem theorem_6_3
    (targets harmfuls : Generic.LanguageFamily α)
    (hCross : AllCrossDifferencesInfinite targets harmfuls) :
    SafelyGeneratesInfiniteDifferences
      (infiniteDifferenceGenerator targets harmfuls hCross)
      targets harmfuls :=
  GenLimit.SafeGeneration.theorem_6_3 targets harmfuls hCross

end GenLimit.SafeGeneration.Results
