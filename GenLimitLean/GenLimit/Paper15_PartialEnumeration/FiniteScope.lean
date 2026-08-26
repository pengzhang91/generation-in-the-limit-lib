import GenLimit.Core.OnlineGeneration
import GenLimit.Core.PartialPresentation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

/-!
# #15 Partial Enumeration: a finite-scope witness

This file proves the semantic content of Theorem 2.1 of Kleinberg--Wei,
*Language Generation and Identification From Partial Enumeration*
(arXiv:2511.05295v1).

At time t, the witness chooses the largest visible family prefix whose
intersection of consistent candidates is infinite, then emits a fresh point
from that intersection. It proves the paper's existential conclusion without
claiming round-for-round equality with the displayed three-case algorithm.
The infinitude test and fresh choice are semantic and noncomputable.
-/

namespace GenLimit.KleinbergWei.PartialEnumeration

/-- Intersection of candidates before s that are consistent at time t. -/
def prefixIntersection
    (C : LanguageFamily) (stream : ℕ → ℕ) (t s : ℕ) : Language :=
  {u | ∀ i, i < s → Consistent C stream t i → u ∈ C i}

@[simp] theorem prefixIntersection_zero
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    prefixIntersection C stream t 0 = Set.univ := by
  ext u
  simp [prefixIntersection]

/-- Visible scopes with infinite consistent-candidate intersection. -/
noncomputable def admissibleScopes
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t + 2)).filter fun s =>
    (prefixIntersection C stream t s).Infinite

@[simp] theorem mem_admissibleScopes
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s : ℕ} :
    s ∈ admissibleScopes C stream t ↔
      s ≤ t + 1 ∧ (prefixIntersection C stream t s).Infinite := by
  classical
  simp [admissibleScopes, Nat.lt_succ_iff]

theorem zero_mem_admissibleScopes
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    0 ∈ admissibleScopes C stream t := by
  classical
  simp [Set.infinite_univ]

/-- Largest visible scope with infinite intersection. Scope zero makes this
maximum total. -/
noncomputable def selectedScope
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ := by
  classical
  let S := admissibleScopes C stream t
  exact S.max' ⟨0, zero_mem_admissibleScopes C stream t⟩

theorem selectedScope_mem
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    selectedScope C stream t ∈ admissibleScopes C stream t := by
  classical
  let S := admissibleScopes C stream t
  simpa [selectedScope, S] using
    Finset.max'_mem S ⟨0, zero_mem_admissibleScopes C stream t⟩

theorem le_selectedScope_of_admissible
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s : ℕ}
    (hs : s ∈ admissibleScopes C stream t) :
    s ≤ selectedScope C stream t := by
  classical
  let S := admissibleScopes C stream t
  simpa [selectedScope, S] using Finset.le_max' S s (by simpa [S] using hs)

/-- Infinite set from which the witness chooses at time t. -/
def selectedIntersection
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : Language :=
  prefixIntersection C stream t (selectedScope C stream t)

theorem selectedIntersection_infinite
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (selectedIntersection C stream t).Infinite :=
  (mem_admissibleScopes.mp (selectedScope_mem C stream t)).2

/-- Semantic fresh choice from the selected infinite intersection. -/
noncomputable def freshOutput
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  Classical.choose
    ((selectedIntersection_infinite C stream t).exists_notMem_finset
      (sample stream t))

theorem freshOutput_mem_selectedIntersection
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    freshOutput C stream t ∈ selectedIntersection C stream t :=
  (Classical.choose_spec
    ((selectedIntersection_infinite C stream t).exists_notMem_finset
      (sample stream t))).1

theorem freshOutput_fresh
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    freshOutput C stream t ∉ sample stream t :=
  (Classical.choose_spec
    ((selectedIntersection_infinite C stream t).exists_notMem_finset
      (sample stream t))).2

/-- Paper-local name for the shared fresh-generation specification. -/
abbrev GeneratesFromPartialEnumeration
    (C : LanguageFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  FreshGeneratesInLimit stream (freshOutput C stream) (C z)

theorem prefixIntersection_infinite_of_stable
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {t s : ℕ}
    (hE : E.Infinite)
    (hstable : ∀ i, i < s →
      (Consistent C stream t i ↔ E ⊆ C i)) :
    (prefixIntersection C stream t s).Infinite := by
  apply hE.mono
  intro u hu i hi hcon
  exact (hstable i hi).mp hcon hu

/-- The shared stabilization core behind the element and semi-index versions
of partial-enumeration generation. -/
theorem selectedIntersection_eventually_subset_target
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    ∃ T, ∀ t, T ≤ t → selectedIntersection C stream t ⊆ C z := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := C) (stream := stream) (E := E) hP (z + 1)
  refine ⟨max T z, ?_⟩
  intro t ht
  have htT : T ≤ t := (Nat.le_max_left _ _).trans ht
  have hzt : z ≤ t := (Nat.le_max_right _ _).trans ht
  have hInf : (prefixIntersection C stream t (z + 1)).Infinite :=
    prefixIntersection_infinite_of_stable hE (hT t htT)
  have hadm : z + 1 ∈ admissibleScopes C stream t :=
    mem_admissibleScopes.mpr ⟨by omega, hInf⟩
  have hzscope : z < selectedScope C stream t := by
    have := le_selectedScope_of_admissible hadm
    omega
  have hzcon : Consistent C stream t z :=
    consistent_of_presented_subset hP hEz
  intro u hu
  exact hu z hzscope hzcon

/-- Theorem 2.1 (Overview Theorem 1.5): every indexed family of infinite
languages is generatable in the limit from an infinite partial enumeration
of its target. `_hLanguagesInfinite` records the paper's standing model; this
finite-scope proof itself needs only `hE`. -/
theorem theorem_2_1
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (_hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    GeneratesFromPartialEnumeration C stream z := by
  obtain ⟨T, hT⟩ :=
    selectedIntersection_eventually_subset_target hP hE hEz
  refine ⟨T, ?_⟩
  intro t ht
  exact
    ⟨hT t ht (freshOutput_mem_selectedIntersection C stream t),
      freshOutput_fresh C stream t⟩

end GenLimit.KleinbergWei.PartialEnumeration
