import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Breadth
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.ExhaustiveCharacterization
import GenLimit.Paper05_HallucinationsBreadthAndStability.ExactBreadth

/-!
# Bridge from Paper 04 breadth to Paper 05 breadth

P04 packages a finite history as an enumeration-valued generator, whereas
P05 maps the same history directly to a support set.  These declarations
record the conversions and the shared weak-Angluin characterization without
making either paper present the other's results as native theorems.
-/

namespace GenLimit.Bridge.Paper04ToPaper05

open GenLimit.Generic
open GenLimit.BreadthCharacterizations

/-- Regard a P04 enumeration-valued generator as its P05 support. -/
def supportOfExhaustive
    (A : GenLimit.CharikarPabbaraju.ExhaustiveAlgorithm α) :
    SupportAlgorithm α :=
  GenLimit.learnerOfFiniteHistory fun t xs => Set.range (A t xs)

@[simp] theorem supportAt_supportOfExhaustive
    (A : GenLimit.CharikarPabbaraju.ExhaustiveAlgorithm α)
    (stream : Generic.Stream α) (t : ℕ) :
    supportAt (supportOfExhaustive A) stream t =
      GenLimit.CharikarPabbaraju.generateOnly A stream t := by
  simp [supportAt, supportOfExhaustive,
    GenLimit.CharikarPabbaraju.generateOnly,
    GenLimit.CharikarPabbaraju.generatorAt,
    GenLimit.learnerOfFiniteHistory_textPrefix]

/-- P04 whole-target breadth yields P05 literal exact breadth after removing
the observed sample. -/
theorem paper04_breadth_implies_paper05_literalExact
    {F : Generic.LanguageFamily α}
    (h : GenLimit.CharikarPabbaraju.BreadthGeneratable F) :
    ExactBreadthGeneratable F := by
  obtain ⟨A, hA⟩ := h
  refine ⟨removeObserved (supportOfExhaustive A), ?_⟩
  apply wholeTarget_implies_literalExact
  intro z stream hP
  obtain ⟨T, hT⟩ := hA z stream hP
  refine ⟨T, ?_⟩
  intro t ht
  simpa [WholeTargetCorrectAt,
    GenLimit.CharikarPabbaraju.BreadthCorrectAt] using hT t ht

/-- P05's indexed weak-Angluin predicate is equivalent to P04's
collection-valued predicate. -/
theorem paper05_weakAngluin_iff_paper04_range
    (F : Generic.LanguageFamily α) :
    WeakAngluinCondition F ↔
      GenLimit.CharikarPabbaraju.WeakAngluinExistence (Set.range F) := by
  constructor
  · intro h L hL
    obtain ⟨i, rfl⟩ := hL
    obtain ⟨T, hT⟩ := h i
    refine ⟨T, hT.1, ?_⟩
    intro L' hL' hTL' hproper
    obtain ⟨j, rfl⟩ := hL'
    exact hT.2 j hTL' hproper
  · intro h i
    obtain ⟨T, hT, hrest⟩ := h (F i) ⟨i, rfl⟩
    refine ⟨T, hT, ?_⟩
    intro j hTj hproper
    exact hrest (F j) ⟨j, rfl⟩ hTj hproper

/-- P04 Overview Theorem 4 transported to P05's indexed weak-Angluin
predicate. -/
theorem paper04_exhaustive_iff_paper05_weakAngluin
    [Countable α] (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable (Set.range F) ↔
      WeakAngluinCondition F := by
  rw [GenLimit.CharikarPabbaraju.theorem4_exhaustive_generation_characterization
    F hInfinite, paper05_weakAngluin_iff_paper04_range]

end GenLimit.Bridge.Paper04ToPaper05
