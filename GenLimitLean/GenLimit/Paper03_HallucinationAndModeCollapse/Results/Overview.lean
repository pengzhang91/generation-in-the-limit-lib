import GenLimit.Paper03_HallucinationAndModeCollapse.PositiveBreadth

/-!
# Paper 03 online results overview

This module exposes the three completed probability-free online results in a
single paper-facing namespace.  Each declaration is a thin wrapper around the
proof module that owns the construction or reduction.
-/

namespace GenLimit.HallucinationModeCollapse.Results

open GenLimit.Generic

/-- Semantic support-oracle form of Theorem 3.5: under the paper's uniform
family-membership oracle, positive-data identification is equivalent to
fresh breadth in the limit. -/
theorem theorem_3_5_semantic
    {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) :
    IdentifiableInLimit C ↔
      ∃ G : SupportGenerator, FreshBreadthInLimit G C :=
  HallucinationModeCollapse.identifiableInLimit_iff_freshBreadthInLimit O

/-- Impossibility form of the semantic online core of Theorem 3.7. -/
theorem theorem_3_7_semantic
    {C : Generic.LanguageFamily ℕ}
    (hnot : ¬IdentifiableInLimit C) :
    ¬∃ G : SupportGenerator,
      Stable G C ∧ UnambiguousInLimit G C :=
  HallucinationModeCollapse.not_exists_stable_unambiguousInLimit_of_not_identifiableInLimit
    hnot

/-- Impossibility form of the semantic online core of Theorem 3.9. -/
theorem theorem_3_9_semantic
    {C : Generic.LanguageFamily ℕ}
    (hnot : ¬IdentifiableInLimit C) :
    ¬∃ G : SupportGenerator,
      Stable G C ∧ ApproximateBreadthInLimit G C :=
  HallucinationModeCollapse.not_exists_stable_approximateBreadthInLimit_of_not_identifiableInLimit
    hnot

end GenLimit.HallucinationModeCollapse.Results
