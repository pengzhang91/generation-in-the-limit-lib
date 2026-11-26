import GenLimit.Paper22_LanguageGenerationWithReplay.FiniteQueryTrace
import GenLimit.Paper22_LanguageGenerationWithReplay.NonuniformSeparation
import GenLimit.Paper22_LanguageGenerationWithReplay.ProperDiagonal

/-!
# Paper 22: main-results overview

This module is the public results facade for Racca--Valko--Sanyal,
*Language Generation with Replay: A Learning-Theoretic View of Model
Collapse* (arXiv:2603.11784v2).  The declarations below are thin wrappers
around the canonical proof modules; no proof is duplicated here.

## Coverage boundary

Theorems 4.1, 5.1, 6.6, and 7.3 are exposed in their complete semantic form.
Theorem 6.1 uses a single encoding of the countable domain by `ℕ` for both
guarantees of Algorithm 2. The generator uses the persistent cutoff and succeeds
under replay. On the encoded family, a finite cache of membership answers
covers every test through each terminating cutoff.
An extensional locality theorem proves that any oracle returning the same
cached answers produces exactly the same round transition.
No separate Mathlib `Computable` certificate or query-complexity bound is
claimed; those are optional strengthening results rather than part of the
source theorem's access-model conclusion.

Theorem 7.1 uses a computable search over finite dialogue transcripts and an
indexed recursive family that preserves each committed transcript.
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

/-- Theorem 6.1. For some encoding `e` of the countable domain, Witness
Protection generates in the limit with replay. On the family encoded by `e`,
finitely many membership answers determine each round of the same machine. -/
theorem theorem_6_1
    {α : Type*}
    (F : CountableDomainOracleFamily α) [Countable α] :
    ∃ e : α ≃ ℕ,
      IsLimitReplayGenerator (F.carriedWitnessProtectionGenerator e) (Set.range F.language) ∧
      (F.encode e).CarriedWitnessProtectionUsesFiniteQueries := by
  let e := F.countableEquivNat
  exact ⟨e, F.theorem_6_1_carried_equiv e, (F.encode e).carriedWitnessProtection_usesFiniteQueries⟩

/-- Theorem 6.6's explicit uncountable ordinary-versus-replay separation. -/
theorem theorem_6_6 :
    ∃ H : LanguageClass LimitReplayPoint,
      ¬H.Countable ∧ UUS H ∧
        GeneratableInLimit H ∧
        ¬GeneratableInLimitWithReplay H :=
  GenLimit.Replay.theorem_6_6_paper

/-! ## Proper generation -/

/-- Theorem 7.1. No single computable proper generator using only adaptive
membership queries succeeds on all uniformly recursive indexed families of infinite languages. -/
theorem theorem_7_1 :
    ¬ ∃ A : ProperMembershipAlgorithm, UniversalProperMembershipGenerator A :=
  ProperDiagonal.impossibility

/-- Theorem 7.3's explicit four-language proper-generation separation. -/
theorem theorem_7_3 :
    ∃ family : HardHypothesis → Generic.Language ℤ,
      Fintype.card HardHypothesis = 4 ∧
      (∀ i, (family i).Infinite) ∧
      ¬ProperlyGeneratableInLimitWithReplay family :=
  GenLimit.Replay.theorem_7_3_paper

end GenLimit.Replay.Results
