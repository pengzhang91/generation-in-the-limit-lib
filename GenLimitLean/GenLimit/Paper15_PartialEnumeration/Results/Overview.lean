import GenLimit.Paper15_PartialEnumeration.Results.Supporting

/-!
# Paper 15: main-results overview

This facade states the formalized main theorems of Kleinberg--Wei,
*Language Generation and Identification From Partial Enumeration*:
Theorems 1.5, 1.7, 1.8, and 1.9. Each statement delegates to its canonical
proof. Languages are sets of natural numbers, and the algorithms are semantic.

Theorem 1.6 (restated as Theorem 3.5) currently has only conditional density
endgames; Theorems 1.10 and 1.11 remain unformalized because of the source's
ambiguous partial-enumeration topology. They are not asserted here.
Supporting results, detailed-number duplicates, and the Corollary 4.10
partial-text counterexample are retained in `Results.Supporting`.
-/

namespace GenLimit.KleinbergWei.PartialEnumeration.Results

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

end GenLimit.KleinbergWei.PartialEnumeration.Results
