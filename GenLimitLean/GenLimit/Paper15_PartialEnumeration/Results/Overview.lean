import GenLimit.Paper15_PartialEnumeration.SharpDensity
import GenLimit.Paper15_PartialEnumeration.Results.Supporting
import GenLimit.Paper15_PartialEnumeration.PartialTopology
import GenLimit.Bridges.Paper39ToPaper15

/-!
# Paper 15: main-results overview

This facade states the formalized main theorems of Kleinberg--Wei,
*Language Generation and Identification From Partial Enumeration*:
Theorems 1.3 and 1.6 give the ordered density guarantees by an independent
patient-scope argument. Theorems 1.5, 1.7–1.9 cover generation, conjunctions,
and full texts. Theorem 1.11 holds directly in the partial-text model. For
Theorem 1.10 the displayed topology yields a counterexample.
Supporting results, detailed-number duplicates, and the Corollary 4.10
partial-text counterexample are retained in `Results.Supporting`.
-/

namespace GenLimit.KleinbergWei.PartialEnumeration.Results

open GenLimit.Bridge.Paper39ToPaper15 GenLimit.PartialEnumeration
open GenLimit.KleinbergWei.DensityMeasures GenLimit.KleinbergWei.DensityMeasures.OrderedFocus

/-- Theorem 1.3, full-text density for compatible orders. -/
theorem theorem_1_3 (O : ℕ → OrderedLanguage) (hc : Compatible O)
    {z : ℕ} {s : ℕ → ℕ} (hp : Presents s (O z).carrier) :
    ElementValid s (OrderedFocus.generate O s) (O z).carrier ∧
      (1 / 2 : ℝ) ≤ (O z).lowerDensity (Set.range (OrderedFocus.generate O s)) :=
  GenLimit.Bridge.Paper39ToPaper15.theorem_1_3 O hc hp

/-- Theorem 1.5 (restated as Theorem 2.1): generation in the limit from any
infinite partial enumeration of a target in a countable family of infinite
languages. The finite-scope construction supplies the generator. -/
theorem theorem_1_5
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    GeneratesFromPartialEnumeration C stream z :=
  GenLimit.KleinbergWei.PartialEnumeration.theorem_2_1
    hLanguagesInfinite hP hE hEz

/-- Theorem 1.6 / 3.5, relative output density on partial texts. -/
theorem theorem_1_6 (O : ℕ → OrderedLanguage) (hc : Compatible O)
    {z : ℕ} {E : Language} {s : ℕ → ℕ} (hp : Presents s E) (hi : E.Infinite)
    (hs : E ⊆ (O z).carrier) {α : ℝ} (ha : α ≤ (O z).lowerDensity E) :
    ElementValid s (GenLimit.Bridge.Paper39ToPaper15.generate O s) (O z).carrier ∧
      α / 2 ≤ (O z).lowerDensity (Set.range (GenLimit.Bridge.Paper39ToPaper15.generate O s)) :=
  GenLimit.Bridge.Paper39ToPaper15.theorem_1_6 O hc hp hi hs ha

/-- Theorem 1.7: conjunction-based generation from any infinite partial
enumeration. The selected finite intersections are infinite at every round
and eventually contained in the target. -/
theorem theorem_1_7
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    SemiIndexGenerates C stream z :=
  GenLimit.KleinbergWei.PartialEnumeration.theorem_1_7
    hLanguagesInfinite hP hE hEz

/-- Theorem 1.8: conjunction-based generation whose finite intersection also
contains the entire partially enumerated set at arbitrarily late times.
The witness is the raw-index stuttering realization of Algorithm 1. -/
theorem theorem_1_8
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    SemiIndexTraceGenerates C (algorithmOneIndices C stream) z ∧
      ∀ T, ∃ t, T ≤ t ∧
        E ⊆ intersectionOf C (algorithmOneIndices C stream t) :=
  GenLimit.KleinbergWei.PartialEnumeration.theorem_1_8
    hLanguagesInfinite hP hE hEz

/-- Theorem 1.9 (restated as Theorem 4.9): full-text identification is
equivalent to countability and the `T_D` property of the full-enumeration
topology. Nonempty languages ensure that identification forces countability. -/
theorem theorem_1_9
    (X : Set Language)
    (hLanguagesNonempty : ∀ L, L ∈ X → L.Nonempty) :
    FullTopology.IdentifiableOnFullTexts X ↔
      X.Countable ∧ FullTopology.TDSpace X :=
  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.theorem_4_9_fullText
    X hLanguagesNonempty

/-- The printed Theorem 1.10 / 4.12 has a counterexample. -/
theorem theorem_1_10_counterexample :
    ¬ (PartialIdentifiable PartialTopology.coSingleClass ↔
      ∀ L ∈ PartialTopology.coSingleClass, ∀ C : Language,
        C.Infinite → C ⊆ L → PartialTopology.QuotientTD PartialTopology.coSingleClass C) :=
  PartialTopology.not_theorem_4_12

/-- Theorem 1.11 / 4.13, invariance under finite deletion. -/
theorem theorem_1_11 (X : Set Language) (W : Finset ℕ) :
    PartialIdentifiable X ↔ PartialIdentifiable (deleteWords W X) := theorem_4_13 X W

/-- Theorem 3.3, attainable upper density on all compatible orderings. -/
theorem theorem_3_3 (O : ℕ → OrderedLanguage)
    (hc : DensityMeasures.OrderedFocus.Compatible O) {z : ℕ} {E : Language} {s : ℕ → ℕ}
    (hp : Presents s E) (hi : E.Infinite) (hs : E ⊆ (O z).carrier) {α : ℝ}
    (ha : α ≤ (O z).lowerDensity E) :
    DensityMeasures.OrderedFocus.ElementValid s (Bridge.Paper39ToPaper15.generate O s) (O z).carrier ∧
      α / 2 ≤ (O z).upperDensity (Set.range (Bridge.Paper39ToPaper15.generate O s)) := by
  obtain ⟨v,h⟩ := Bridge.Paper39ToPaper15.theorem_1_6 O hc hp hi hs ha
  exact ⟨v,h.trans (Filter.liminf_le_limsup
    (Filter.isBoundedUnder_of ⟨1,fun n ↦ (O z).prefixRatio_le_one _ n⟩)
    (Filter.isBoundedUnder_of ⟨0,fun n ↦ (O z).prefixRatio_nonneg _ n⟩))⟩

end GenLimit.KleinbergWei.PartialEnumeration.Results
