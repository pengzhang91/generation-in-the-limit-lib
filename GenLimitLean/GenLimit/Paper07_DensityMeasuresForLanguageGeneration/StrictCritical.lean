import GenLimit.Core.PartialPresentation

/-!
# #07 Density Measures: strict criticality

Definition 3.1, Claim 3.2, and Lemma 3.3 of Kleinberg--Wei,
*Density Measures for Language Generation* (arXiv:2504.14370v1).

The displayed Definition 3.1 includes the current language and would require
it to be a proper subset of itself. Following the sentence immediately after
the display, the definition below compares only with earlier indices.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- Corrected Definition 3.1: candidate n is consistent and is a proper
subset of every earlier consistent candidate. -/
def StrictCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t n : ℕ) : Prop :=
  Consistent C stream t n ∧
    ∀ i, i < n → Consistent C stream t i → C n ⊂ C i

/-- Strictly critical languages form a proper descending chain. -/
theorem strictCritical_ssubset_of_lt
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i j : ℕ}
    (hij : i < j)
    (hi : StrictCritical C stream t i)
    (hj : StrictCritical C stream t j) :
    C j ⊂ C i :=
  hj.2 i hij hi.1

/-- The least consistent candidate is strictly critical. -/
theorem least_consistent_strictCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (hn : Consistent C stream t n)
    (hleast : ∀ i, i < n → ¬Consistent C stream t i) :
    StrictCritical C stream t n := by
  refine ⟨hn, ?_⟩
  intro i hin hicon
  exact False.elim ((hleast i hin) hicon)

/-- Claim 3.2: strict criticality persists while the language remains
consistent. The source proof's bound i < r is corrected to i < n. -/
theorem claim_3_2
    {C : LanguageFamily} {stream : ℕ → ℕ} {t r n : ℕ}
    (htr : t ≤ r)
    (hn : StrictCritical C stream t n)
    (hconsistent : Consistent C stream r n) :
    StrictCritical C stream r n := by
  refine ⟨hconsistent, ?_⟩
  intro i hin hi
  apply hn.2 i hin
  intro u hu
  exact hi (sample_mono htr hu)

/-- The target index is its first occurrence in the indexed family. -/
def FirstOccurrence (C : LanguageFamily) (z : ℕ) : Prop :=
  ∀ i, i < z → C i ≠ C z

/-- Lemma 3.3: the first occurrence of an exactly presented target is
strictly critical from some finite time onward. -/
theorem lemma_3_3
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ t, T ≤ t → StrictCritical C stream t z := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := C) (stream := stream) (E := C z) hP z
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨presents_consistent hP, ?_⟩
  intro i hiz hi
  have hsub : C z ⊆ C i := (hT t ht i hiz).mp hi
  exact Set.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun heq => hfirst i hiz heq.symm⟩

end GenLimit.KleinbergWei.DensityMeasures
