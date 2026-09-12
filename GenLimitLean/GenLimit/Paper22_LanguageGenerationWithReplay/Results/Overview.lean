import GenLimit.Paper22_LanguageGenerationWithReplay.FiniteQueryTrace
import GenLimit.Paper22_LanguageGenerationWithReplay.NonuniformSeparation
import GenLimit.Paper22_LanguageGenerationWithReplay.ProperMembershipLowerBound

/-!
# Paper 22: main-results overview

This module is the public results facade for Racca--Valko--Sanyal,
*Language Generation with Replay: A Learning-Theoretic View of Model
Collapse* (arXiv:2603.11784v2).  The declarations below are thin wrappers
around the canonical proof modules; no proof is duplicated here.

## Coverage boundary

Theorems 4.1, 5.1, 6.6, and 7.3 are exposed in their complete semantic form.
For Theorem 6.1, the facade uses the literal persistent-cutoff version of
Algorithm 2.  It exposes both the semantic result on an arbitrary countable
domain and the executable natural-number machine together with a finite
answered-query cache covering every test through each terminating cutoff.
An extensional locality theorem proves that any oracle returning the same
cached answers produces exactly the same round transition.
No separate Mathlib `Computable` certificate or query-complexity bound is
claimed; those are optional strengthening results rather than part of the
source theorem's access-model conclusion.

Theorem 7.1 is not presented as complete.  Lean defines its adaptive
membership-query machine statement and verifies the diagonal endgame, but
the recursive Algorithm 3 construction remains an explicit premise.  The
diagnostic below also records why the older, stronger premise quantified over
too many nonterminating machines.
-/

namespace GenLimit.Replay.Results

open GenLimit.Generic

/-! ## Uniform and non-uniform replay -/

/-- Theorem 4.1 at a fixed positive threshold, preserving that threshold in
both directions. -/
theorem theorem_4_1
    {α : Type*} [Inhabited α]
    (H : LanguageClass α) (d : ℕ) (hd : 0 < d) :
    (∃ gen : Generator α, IsUniformGeneratorAt gen H d) ↔
      ∃ gen : Generator α,
        IsUniformReplayGeneratorAt gen H d :=
  GenLimit.Replay.theorem_4_1 H d hd

/-- Theorem 5.1's explicit countable separation. -/
theorem theorem_5_1 :
    NonuniformlyGeneratable nonuniformHardClass ∧
      ¬NonuniformlyGeneratableWithReplay nonuniformHardClass :=
  GenLimit.Replay.theorem_5_1

/-! ## Limit generation with replay -/

/-- Semantic Theorem 6.1 for the source's literal persistent-cutoff
Algorithm 2, transported from `ℕ` to an arbitrary countable domain. -/
theorem theorem_6_1
    {α : Type*}
    (F : CountableDomainOracleFamily α) [Countable α] :
    ∃ gen : Generator α,
      IsLimitReplayGenerator gen (Set.range F.language) :=
  CountableDomainOracleFamily.theorem_6_1_countable_carried_paper F

/-- Theorem 6.1's executable finite-membership-query realization on the
source's normalized natural-number universe.  The first conjunct is the full
semantic guarantee; the second gives a finite valid answer cache at every
literal carried-cutoff transition, with an explicit cutoff-dependent
cardinality bound and an extensional proof that the cache determines the
transition. -/
theorem theorem_6_1_finite_query (O : GenLimit.OracleFamily) :
    IsLimitReplayGenerator O.carriedWitnessProtectionGenerator
        (Set.range O.language) ∧
      O.CarriedWitnessProtectionUsesFiniteQueries :=
  GenLimit.Replay.theorem_6_1_finite_query O

/-- Theorem 6.6's explicit uncountable ordinary-versus-replay separation. -/
theorem theorem_6_6 :
    ∃ H : LanguageClass LimitReplayPoint,
      ¬H.Countable ∧ UUS H ∧
        GeneratableInLimit H ∧
        ¬GeneratableInLimitWithReplay H :=
  GenLimit.Replay.theorem_6_6_paper

/-! ## Proper generation -/

/-- Checked reduction of Theorem 7.1 to the remaining source-faithful
Algorithm 3 construction under the same universal-generator hypothesis. -/
theorem theorem_7_1_of_algorithm3
    (hconstruction : Algorithm3UniversalConstructionStatement) :
    Theorem71Statement :=
  GenLimit.Replay.theorem_7_1_of_universal_algorithm3 hconstruction

/-- Diagnostic for the obsolete over-strong Algorithm 3 obligation: it also
quantifies over machines that query forever and never finish a round. -/
theorem theorem_7_1_overstrong_construction_is_false :
    ¬Algorithm3ConstructionStatement :=
  GenLimit.Replay.algorithm3ConstructionStatement_is_false

/-- Theorem 7.3's explicit four-language proper-generation separation. -/
theorem theorem_7_3 :
    ∃ family : HardHypothesis → Generic.Language ℤ,
      Fintype.card HardHypothesis = 4 ∧
      (∀ i, (family i).Infinite) ∧
      ¬ProperlyGeneratableInLimitWithReplay family :=
  GenLimit.Replay.theorem_7_3_paper

end GenLimit.Replay.Results
