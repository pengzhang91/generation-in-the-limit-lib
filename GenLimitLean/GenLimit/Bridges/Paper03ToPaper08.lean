import GenLimit.Paper03_HallucinationAndModeCollapse.Results.Overview
import GenLimit.Paper08_HallucinationDetection.Reductions

/-!
# Bridge between Paper 03 fresh breadth and Paper 08 hallucination detection

Both papers characterize their native property through the shared semantic
positive-data identification predicate.  Exact fresh breadth implies
hallucination detectability without any family-membership oracle.  Under the
uniform family-membership oracle assumed by Paper 03's positive construction,
the two properties are equivalent.

This is a library-derived cross-paper consequence, not a theorem explicitly
stated in either source paper.  It is semantic: no Turing-machine compilation,
probability bound, or convergence-rate equivalence is claimed.
-/

namespace GenLimit.Bridge.Paper03ToPaper08

/-- Exact Paper 03 fresh breadth implies Paper 08 hallucination detectability.
This direction does not require a family-membership oracle. -/
theorem freshBreadth_implies_hallucinationDetectable
    {C : Generic.LanguageFamily ℕ}
    {G : HallucinationModeCollapse.SupportGenerator}
    (hBreadth : HallucinationModeCollapse.FreshBreadthInLimit G C) :
    HallucinationDetection.HallucinationDetectable C := by
  apply (HallucinationDetection.theorem_2_1 C).mpr
  exact
    HallucinationModeCollapse.freshBreadthInLimit_implies_identifiableInLimit
      hBreadth

/-- Under Paper 03's uniform family-membership oracle, Paper 08 hallucination
detectability is equivalent to existence of a Paper 03 fresh-breadth support
generator. -/
theorem hallucinationDetectable_iff_freshBreadthInLimit
    {C : Generic.LanguageFamily ℕ}
    (O : MembershipOracle C) :
    HallucinationDetection.HallucinationDetectable C ↔
      ∃ G : HallucinationModeCollapse.SupportGenerator,
        HallucinationModeCollapse.FreshBreadthInLimit G C :=
  (HallucinationDetection.theorem_2_1 C).trans
    (HallucinationModeCollapse.Results.theorem_3_5_semantic O)

end GenLimit.Bridge.Paper03ToPaper08
