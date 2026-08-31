import GenLimit.Paper15_PartialEnumeration.FiniteScope

/-!
# #15 Finite-intersection semi-indices

The finite conjunction implicit in the Theorem 2.1 witness, yielding the
conjunction-based conclusion of Overview Theorem 1.7. The selected scopes are
semantic and noncomputable because admissibility tests infinitude.
-/

namespace GenLimit.KleinbergWei.PartialEnumeration

/-- Intersection of languages named by a finite semi-index. -/
def intersectionOf (C : LanguageFamily) (I : Finset ℕ) : Language :=
  {u | ∀ i ∈ I, u ∈ C i}

/-- Consistent indices in the selected finite scope. -/
noncomputable def selectedIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (selectedScope C stream t)).filter
    (Consistent C stream t)

@[simp] theorem mem_selectedIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i : ℕ} :
    i ∈ selectedIndices C stream t ↔
      i < selectedScope C stream t ∧ Consistent C stream t i := by
  classical
  simp [selectedIndices]

theorem intersectionOf_selectedIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    intersectionOf C (selectedIndices C stream t) =
      selectedIntersection C stream t := by
  ext u
  constructor
  · intro hu i hi hcon
    exact hu i (mem_selectedIndices.mpr ⟨hi, hcon⟩)
  · intro hu i hi
    have hip := mem_selectedIndices.mp hi
    exact hu i hip.1 hip.2

theorem selectedIndices_intersection_infinite
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (intersectionOf C (selectedIndices C stream t)).Infinite := by
  rw [intersectionOf_selectedIndices]
  exact selectedIntersection_infinite C stream t

/-- Conjunction-based partial-enumeration generation. -/
def SemiIndexGenerates
    (C : LanguageFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  (∀ t, (intersectionOf C (selectedIndices C stream t)).Infinite) ∧
    ∃ T, ∀ t, T ≤ t →
      intersectionOf C (selectedIndices C stream t) ⊆ C z

/-- Overview Theorem 1.7. `_hLanguagesInfinite` records the paper's standing
model; this finite-scope proof itself needs only `hE`. -/
theorem theorem_1_7
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (_hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    SemiIndexGenerates C stream z := by
  refine ⟨selectedIndices_intersection_infinite C stream, ?_⟩
  obtain ⟨T, hT⟩ :=
    selectedIntersection_eventually_subset_target hP hE hEz
  refine ⟨T, ?_⟩
  intro t ht
  rw [intersectionOf_selectedIndices]
  exact hT t ht

end GenLimit.KleinbergWei.PartialEnumeration
