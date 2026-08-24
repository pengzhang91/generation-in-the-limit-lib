import GenLimit.Core.Identification
import GenLimit.Paper05_HallucinationsBreadthAndStability.Definitions
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.ExhaustiveCharacterization

/-!
# Approximate-breadth upper bound

This file formalizes the constructive direction of Theorem 3.8 in
Kalavasis--Mehrotra--Velegkas, arXiv:2412.18530v2: the weak Angluin
condition suffices for approximate breadth.

The semantic algorithm selects the last critical language among the finite
index scope.  Eventually the target is critical, the selected language is a
subset of the target, and the target differs from it by only finitely many
points.  This is the same critical-language core used by the strong-oracle
exhaustive generator, without its finite hallucination augmentation.
-/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Generic
open GenLimit.CharikarPabbaraju

/-- The support is the current last critical language. -/
noncomputable def approximateFocusAlgorithm
    (F : Generic.LanguageFamily α) : SupportAlgorithm α :=
  GenLimit.learnerOfFiniteHistory fun _ xs => F (exhaustiveFocus F xs)

@[simp] theorem supportAt_approximateFocusAlgorithm
    (F : Generic.LanguageFamily α) (stream : Generic.Stream α) (t : ℕ) :
    supportAt (approximateFocusAlgorithm F) stream t =
      F (exhaustiveFocus F (fun j : Fin t => stream j)) := by
  simp [supportAt, approximateFocusAlgorithm,
    GenLimit.learnerOfFiniteHistory_textPrefix]

/-- Eventual pointwise correctness of the critical-language support. -/
theorem approximateFocus_eventually_correct
    {F : Generic.LanguageFamily α}
    (hWeak : WeakAngluinCondition F)
    {stream : Generic.Stream α} {z : ℕ}
    (hP : Generic.Presents stream (F z)) :
    ∃ T, ∀ t, T ≤ t →
      ApproximateBreadthCorrectAt
        (approximateFocusAlgorithm F) (F z) stream t := by
  classical
  obtain ⟨tell, htellTarget, htell⟩ := hWeak z
  obtain ⟨Ttell, hTtell⟩ :=
    Generic.finset_eventually_subset_sample hP tell htellTarget
  obtain ⟨Tcritical, hTcritical⟩ :=
    exhaustiveTarget_eventually_critical hP
  refine ⟨max (max Ttell Tcritical) z, ?_⟩
  intro t ht
  let xs : Fin t → α := fun j => stream j
  let focus := exhaustiveFocus F xs
  have htellTime : Ttell ≤ t :=
    (Nat.le_max_left Ttell Tcritical).trans
      ((Nat.le_max_left (max Ttell Tcritical) z).trans ht)
  have hcriticalTime : Tcritical ≤ t :=
    (Nat.le_max_right Ttell Tcritical).trans
      ((Nat.le_max_left (max Ttell Tcritical) z).trans ht)
  have hzt : z ≤ t :=
    (Nat.le_max_right (max Ttell Tcritical) z).trans ht
  have hzCritical : ExhaustiveHistoryCritical F xs z :=
    hTcritical t hcriticalTime
  have hfocus := exhaustiveFocus_spec hzt hzCritical
  have hfocusSub : F focus ⊆ F z := by
    exact exhaustiveHistoryCritical_subset_of_le
      hfocus.2.2 hzCritical hfocus.2.1
  have htellSample : tell ⊆ Generic.sample stream t :=
    hTtell.trans (Generic.sample_mono htellTime)
  have hsampleFocus :
      (↑(Generic.sample stream t) : Set α) ⊆ F focus := by
    simpa [xs, focus, exhaustiveHistoryConsistent_prefix_iff] using
      hfocus.2.1.1
  have htellFocus : (↑tell : Set α) ⊆ F focus := by
    intro x hx
    exact hsampleFocus (htellSample hx)
  have hdiff : (F z \ F focus).Finite := by
    by_cases heq : F focus = F z
    · simp [heq]
    · exact htell focus htellFocus
        (Set.ssubset_iff_subset_ne.mpr ⟨hfocusSub, heq⟩)
  simpa [ApproximateBreadthCorrectAt, xs, focus] using
    And.intro hfocusSub hdiff

/-- Sufficiency direction of Theorem 3.8. -/
theorem weakAngluin_implies_approximateBreadth
    {F : Generic.LanguageFamily α}
    (hWeak : WeakAngluinCondition F) :
    IsApproximateBreadthGenerator (approximateFocusAlgorithm F) F := by
  intro z stream hP
  exact approximateFocus_eventually_correct hWeak hP

theorem weakAngluin_implies_approximateBreadthGeneratable
    {F : Generic.LanguageFamily α}
    (hWeak : WeakAngluinCondition F) :
    ApproximateBreadthGeneratable F :=
  ⟨approximateFocusAlgorithm F,
    weakAngluin_implies_approximateBreadth hWeak⟩

end GenLimit.BreadthCharacterizations
