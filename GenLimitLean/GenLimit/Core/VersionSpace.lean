import GenLimit.Core.GenericGeneration
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Powerset

/-!
# Positive version spaces and closure

Paper-independent definitions and elementary facts for a class of languages
conditioned on a finite positive sample.
-/

namespace GenLimit.Generic

/-- Languages in `H` that contain the positive sample `S`. -/
def versionSpace (H : LanguageClass α) (S : Finset α) : Set (Language α) :=
  {L | L ∈ H ∧ (↑S : Set α) ⊆ L}

/-- The intersection of all languages in a positive version space. -/
def commonCore (H : LanguageClass α) (S : Finset α) : Language α :=
  {x | ∀ L, L ∈ versionSpace H S → x ∈ L}

/-- Positive closure, with `none` representing an empty version space. -/
noncomputable def closure
    (H : LanguageClass α) (S : Finset α) : Option (Language α) := by
  classical
  exact if (versionSpace H S).Nonempty then some (commonCore H S) else none

theorem mem_versionSpace_iff
    {H : LanguageClass α} {S : Finset α} {L : Language α} :
    L ∈ versionSpace H S ↔ L ∈ H ∧ (↑S : Set α) ⊆ L :=
  Iff.rfl

theorem closure_eq_none_iff
    {H : LanguageClass α} {S : Finset α} :
    closure H S = none ↔ ¬(versionSpace H S).Nonempty := by
  classical
  constructor
  · intro hnone hVS
    have hsome : closure H S = some (commonCore H S) := by
      simp [closure, hVS]
    rw [hnone] at hsome
    cases hsome
  · intro hVS
    simp [closure, hVS]

theorem closure_eq_some_iff
    {H : LanguageClass α} {S : Finset α} {C : Language α} :
    closure H S = some C ↔
      (versionSpace H S).Nonempty ∧ C = commonCore H S := by
  classical
  constructor
  · intro hcl
    by_cases hVS : (versionSpace H S).Nonempty
    · refine ⟨hVS, ?_⟩
      have hc : commonCore H S = C := by
        simpa [closure, hVS] using hcl
      exact hc.symm
    · simp [closure, hVS] at hcl
  · rintro ⟨hVS, rfl⟩
    simp [closure, hVS]

theorem sample_subset_of_streamIn
    {stream : Stream α} {L : Language α} (hstream : StreamIn stream L)
    (t : ℕ) : (↑(sample stream t) : Set α) ⊆ L := by
  intro x hx
  obtain ⟨s, -, rfl⟩ := mem_sample_iff.mp hx
  exact hstream ⟨s, rfl⟩

theorem target_mem_versionSpace
    {H : LanguageClass α} {L : Language α} (hLH : L ∈ H)
    {stream : Stream α} (hstream : StreamIn stream L) (t : ℕ) :
    L ∈ versionSpace H (sample stream t) :=
  ⟨hLH, sample_subset_of_streamIn hstream t⟩

theorem sample_subset_commonCore
    {H : LanguageClass α} {S : Finset α} :
    (↑S : Set α) ⊆ commonCore H S := by
  intro x hx L hL
  exact hL.2 hx

theorem commonCore_subset_of_mem_versionSpace
    {H : LanguageClass α} {S : Finset α} {L : Language α}
    (hL : L ∈ versionSpace H S) :
    commonCore H S ⊆ L := by
  intro x hx
  exact hx L hL

/-! ## The finite collection of possible subclass cores -/

/-- The intersection of every language in an arbitrary subclass.  Unlike
`commonCore`, this definition does not mention a positive sample. -/
def subclassCore (V : Set (Language α)) : Language α :=
  {x | ∀ L, L ∈ V → x ∈ L}

theorem commonCore_eq_subclassCore
    (H : LanguageClass α) (S : Finset α) :
    commonCore H S = subclassCore (versionSpace H S) :=
  rfl

theorem finite_subclassCore_image
    {H : LanguageClass α} (hH : H.Finite) :
    (subclassCore '' Set.powerset H).Finite :=
  hH.powerset.image subclassCore

/-- All intersections arising from subclasses of a fixed finite language
class. -/
noncomputable def subclassCores
    (H : LanguageClass α) (hH : H.Finite) : Finset (Language α) := by
  classical
  exact (finite_subclassCore_image hH).toFinset

theorem mem_subclassCores_iff
    {H : LanguageClass α} (hH : H.Finite) {C : Language α} :
    C ∈ subclassCores H hH ↔
      ∃ V : Set (Language α), V ⊆ H ∧ subclassCore V = C := by
  classical
  rw [subclassCores, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨V, hV, rfl⟩
    exact ⟨V, hV, rfl⟩
  · rintro ⟨V, hV, rfl⟩
    exact ⟨V, hV, rfl⟩

theorem subclassCore_mem_subclassCores
    {H : LanguageClass α} (hH : H.Finite)
    {V : Set (Language α)} (hV : V ⊆ H) :
    subclassCore V ∈ subclassCores H hH :=
  (mem_subclassCores_iff hH).2 ⟨V, hV, rfl⟩

theorem commonCore_mem_subclassCores
    {H : LanguageClass α} (hH : H.Finite) (S : Finset α) :
    commonCore H S ∈ subclassCores H hH := by
  rw [commonCore_eq_subclassCore]
  apply subclassCore_mem_subclassCores hH
  intro L hL
  exact hL.1

/-- The finite intersections arising from subclasses of a finite class have
a uniform cardinality bound. -/
theorem finite_language_class_has_subclassCore_bound
    {H : LanguageClass α} (hH : H.Finite) :
    ∃ B : ℕ, ∀ V : Set (Language α),
      V ⊆ H → (subclassCore V).Finite → (subclassCore V).ncard ≤ B := by
  classical
  let cores := subclassCores H hH
  let B : ℕ := cores.sup Set.ncard
  refine ⟨B, ?_⟩
  intro V hVH _hcore
  exact Finset.le_sup (f := Set.ncard)
    (show subclassCore V ∈ cores from subclassCore_mem_subclassCores hH hVH)

end GenLimit.Generic
