import GenLimit.Paper03_HallucinationAndModeCollapse.PositiveBreadth
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Breadth

/-!
# Bridge from Paper 04 exact breadth to Paper 03 fresh breadth

The two papers package breadth using different algorithmic objects.  This
module records their theorem-level relationship without making either native
paper development depend on the other.

Paper 04 exact breadth first yields semantic positive-data identification.
Under Paper 03's uniform language-membership oracle, its positive direction
then turns that identifier into a support-valued fresh-breadth generator.
This is a semantic implication; it does not compile either object to a
Turing-machine implementation.
-/

namespace GenLimit.Bridge.Paper03ToPaper04

/-- Paper 04 exact breadth implies the identification property occurring on
the left side of Paper 03 Theorem 3.5. -/
theorem paper04_breadth_implies_paper03_identifiable
    {F : Generic.LanguageFamily ℕ}
    (hBreadth : CharikarPabbaraju.BreadthGeneratable F) :
    HallucinationModeCollapse.IdentifiableInLimit F := by
  obtain ⟨A, hA⟩ := hBreadth
  exact ⟨CharikarPabbaraju.breadthIdentifier A F,
    CharikarPabbaraju.breadthGenerator_semanticallyIdentifies hA⟩

/-- With the membership oracle assumed by Paper 03, Paper 04 exact breadth
also implies existence of a Paper 03 fresh-breadth support generator. -/
theorem paper04_breadth_implies_paper03_fresh_breadth
    {F : Generic.LanguageFamily ℕ}
    (O : MembershipOracle F)
    (hBreadth : CharikarPabbaraju.BreadthGeneratable F) :
    ∃ G : HallucinationModeCollapse.SupportGenerator,
      HallucinationModeCollapse.FreshBreadthInLimit G F :=
  HallucinationModeCollapse.identifiableInLimit_implies_freshBreadthInLimit O
    (paper04_breadth_implies_paper03_identifiable hBreadth)

end GenLimit.Bridge.Paper03ToPaper04
