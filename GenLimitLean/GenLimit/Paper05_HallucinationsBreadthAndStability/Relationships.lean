import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineReductions
import GenLimit.Paper05_HallucinationsBreadthAndStability.Definitions

/-!
# P03 semantic reuse

This file adapts P05's query-free support algorithms to the richer semantic
support-oracle interface used by P03.  The adapter is used only to reuse the
already formalized stable-approximate-to-identification reduction; it makes no
computability claim.
-/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Generic

noncomputable section

noncomputable local instance relationshipsPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Add P03's semantic support-membership interface to a P05 support
algorithm.  This adapter makes no computability claim. -/
noncomputable def asP03SupportGenerator
    (G : SupportAlgorithm ℕ) :
    GenLimit.HallucinationModeCollapse.SupportGenerator where
  support t xs := G (List.ofFn xs)
  query t xs x := decide (x ∈ G (List.ofFn xs))
  query_spec := by
    intro t xs x
    simp

@[simp] theorem p03_supportAt_asP03SupportGenerator
    (G : SupportAlgorithm ℕ) (stream : Generic.Stream ℕ) (t : ℕ) :
    GenLimit.HallucinationModeCollapse.supportAt
        (asP03SupportGenerator G) stream t =
      supportAt G stream t := by
  rw [GenLimit.HallucinationModeCollapse.supportAt, supportAt,
    asP03SupportGenerator, GenLimit.textPrefix_eq_ofFn]

theorem asP03SupportGenerator_stable
    {G : SupportAlgorithm ℕ} {F : Generic.LanguageFamily ℕ}
    (h : IsStableGenerator G F) :
    GenLimit.HallucinationModeCollapse.Stable
      (asP03SupportGenerator G) F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := h z stream hP
  refine ⟨T, ?_⟩
  intro n n' hn hn'
  simpa using hT n n' hn hn'

theorem asP03SupportGenerator_approximate
    {G : SupportAlgorithm ℕ} {F : Generic.LanguageFamily ℕ}
    (h : IsApproximateBreadthGenerator G F) :
    GenLimit.HallucinationModeCollapse.ApproximateBreadthInLimit
      (asP03SupportGenerator G) F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := h z stream hP
  refine ⟨T, ?_⟩
  intro t ht
  simpa [GenLimit.HallucinationModeCollapse.ApproximateBreadthAt,
    ApproximateBreadthCorrectAt] using hT t ht

/-- Reuse of P03's query-independent semantic reduction: stable approximate
breadth implies positive-data identification. -/
theorem stableApproximate_implies_semanticallyInferrable
    {G : SupportAlgorithm ℕ} {F : Generic.LanguageFamily ℕ}
    (hStable : IsStableGenerator G F)
    (hApprox : IsApproximateBreadthGenerator G F) :
    GenLimit.Angluin.SemanticallyInferrable F :=
  GenLimit.HallucinationModeCollapse.stable_approximateBreadthInLimit_implies_identifiableInLimit
      (asP03SupportGenerator_stable hStable)
      (asP03SupportGenerator_approximate hApprox)

end

end GenLimit.BreadthCharacterizations
