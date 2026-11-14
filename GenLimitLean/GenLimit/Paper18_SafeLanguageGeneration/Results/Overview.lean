import GenLimit.Paper18_SafeLanguageGeneration.CorollarySixOneDiagnostic
import GenLimit.Paper18_SafeLanguageGeneration.Impossibility
import GenLimit.Paper18_SafeLanguageGeneration.InfiniteDifference
import GenLimit.Paper18_SafeLanguageGeneration.MachineEncoding
import GenLimit.Paper18_SafeLanguageGeneration.Results.Supporting
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
  representation-transport theorem remain available in `Results.Supporting`.
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

open SafeIdentification in
/-- Deterministic fixed-family repair of Theorem 3.1: no identifier succeeds
on every valid labeled presentation, although every safe difference is represented.
The paper's statement does not require harmful languages to be infinite, although
its proof uses such a family. With an empty harmful language, safe identification
reduces to ordinary identification in the limit. -/
theorem theorem_3_1 :
    (∀ i, (candidateFamily i).Infinite) ∧
    (∀ j, (harmfulFamily j).Infinite) ∧
    (∀ j, DifferenceRepresented candidateFamily
      (candidateFamily 0) (harmfulFamily j)) ∧
    ¬ ∃ M : SafeIdentifier Point,
      ∀ j stream,
        LabeledPresents stream (candidateFamily 0) (harmfulFamily j) →
        SafelyIdentifiesFrom M candidateFamily
          (candidateFamily 0) (harmfulFamily j) stream := by
  obtain ⟨hCandidates, hHarmfuls, hRepresented, hFailure⟩ :=
    theorem_3_1_deterministic_repair
  refine ⟨hCandidates, hHarmfuls, hRepresented, ?_⟩
  rintro ⟨M, hIdentifies⟩
  obtain ⟨j, _, hPresents, hFails⟩ := hFailure M
  exact hFails (hIdentifies j (diagonalStream M) hPresents)

/-! ## Safe generation versus identification -/

/-- Repaired, prefix-compatible semantic form of Theorem 5.1.
The constructed identifier calls `G` on finite labeled histories. This is a
semantic reduction using classical membership tests and chosen candidate
enumerations; computability relative to specified oracles is not formalized. -/
theorem theorem_5_1 [Countable α]
    (G : SafeGenerator (α × ℕ))
    (C : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (C i).Infinite)
    (hFamilies :
      SafelyGeneratesFamilies G
        (fun i => verticalPad (C i))
        (fun i => verticalPad (C i))) :
    GenLimit.Angluin.SemanticallyIdentifies
      (identificationFromSafeGenerator G C
        (fun i => verticalPadPresentation (C i) (hInfinite i).nonempty)) C :=
  theorem_5_1_prefix_compatible G C
    (fun i => verticalPadPresentation (C i) (hInfinite i).nonempty)
    (fun i => verticalPadPresentation_presents (C i) (hInfinite i).nonempty)
    hFamilies

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
