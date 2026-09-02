import GenLimit.Core.GenericGeneration
import Mathlib.Data.Set.Card

/-!
# Finite contamination

Paper-independent vocabulary for streams with finitely many invalid
occurrences or finitely many distinct values outside a target.  The two
counting conventions are kept separate: they agree for injective streams,
but differ when observations may repeat.
-/

namespace GenLimit.Generic

/-- The time indices at which `stream` violates `Acceptable`. -/
def ViolationIndices
    (stream : ℕ → α) (Acceptable : α → Prop) : Set ℕ :=
  {t | ¬Acceptable (stream t)}

/-- Only finitely many stream occurrences violate `Acceptable`. -/
def FinitelyManyViolations
    (stream : ℕ → α) (Acceptable : α → Prop) : Prop :=
  (ViolationIndices stream Acceptable).Finite

/-- At most `n` stream occurrences violate `Acceptable`. -/
def ViolationsAtMost
    (stream : ℕ → α) (Acceptable : α → Prop)
    (n : ℕ) : Prop :=
  (ViolationIndices stream Acceptable).Finite ∧
    (ViolationIndices stream Acceptable).ncard ≤ n

/-- Finset-witness form of the occurrence bound, matching papers that write
the finite indicator sum explicitly. -/
theorem violationsAtMost_iff_exists_finset
    (stream : ℕ → α) (Acceptable : α → Prop) (n : ℕ) :
    ViolationsAtMost stream Acceptable n ↔
      ∃ F : Finset ℕ,
        F.card ≤ n ∧ ∀ t, t ∈ F ↔ ¬Acceptable (stream t) := by
  constructor
  · intro h
    refine ⟨h.1.toFinset, ?_, ?_⟩
    · calc
        h.1.toFinset.card = (ViolationIndices stream Acceptable).ncard := by
          symm
          exact Set.ncard_eq_toFinset_card _ h.1
        _ ≤ n := h.2
    · intro t
      rw [Set.Finite.mem_toFinset]
      rfl
  · rintro ⟨F, hcard, hF⟩
    have heq : ViolationIndices stream Acceptable = (F : Set ℕ) := by
      ext t
      simpa [ViolationIndices] using (hF t).symm
    change (ViolationIndices stream Acceptable).Finite ∧
      (ViolationIndices stream Acceptable).ncard ≤ n
    rw [heq]
    constructor
    · exact F.finite_toSet
    · simpa using hcard

theorem violationsAtMost_mono
    {stream : ℕ → α} {Acceptable : α → Prop}
    {i j : ℕ} (hij : i ≤ j)
    (h : ViolationsAtMost stream Acceptable i) :
    ViolationsAtMost stream Acceptable j :=
  ⟨h.1, h.2.trans hij⟩

theorem finitelyManyViolations_of_violationsAtMost
    {stream : ℕ → α} {Acceptable : α → Prop}
    {n : ℕ} (h : ViolationsAtMost stream Acceptable n) :
    FinitelyManyViolations stream Acceptable :=
  h.1

theorem exists_violationsAtMost_of_finitelyManyViolations
    {stream : ℕ → α} {Acceptable : α → Prop}
    (h : FinitelyManyViolations stream Acceptable) :
    ∃ n, ViolationsAtMost stream Acceptable n :=
  ⟨(ViolationIndices stream Acceptable).ncard, h, le_rfl⟩

/-- A finite-witness formulation of `A` having at most `n` elements outside
`B`.  Exposing the witness is useful in constructions that enumerate the
exceptional values. -/
def SetDifferenceAtMost (A B : Set α) (n : ℕ) : Prop :=
  ∃ F : Finset α, (F : Set α) = A \ B ∧ F.card ≤ n

theorem setDifferenceAtMost_iff_finite_ncard_le
    (A B : Set α) (n : ℕ) :
    SetDifferenceAtMost A B n ↔
      (A \ B).Finite ∧ (A \ B).ncard ≤ n := by
  constructor
  · rintro ⟨F, hF, hcard⟩
    rw [← hF]
    constructor
    · exact F.finite_toSet
    · simpa using hcard
  · rintro ⟨hfinite, hcard⟩
    refine ⟨hfinite.toFinset, ?_, ?_⟩
    · ext x
      simp
    · simpa [Set.ncard_eq_toFinset_card (A \ B) hfinite] using hcard

theorem setDifferenceAtMost_mono
    {A B : Set α} {i j : ℕ} (hij : i ≤ j)
    (h : SetDifferenceAtMost A B i) :
    SetDifferenceAtMost A B j := by
  obtain ⟨F, hF, hcard⟩ := h
  exact ⟨F, hF, hcard.trans hij⟩

theorem setDifferenceAtMost_zero_iff_subset
    (A B : Set α) :
    SetDifferenceAtMost A B 0 ↔ A ⊆ B := by
  rw [setDifferenceAtMost_iff_finite_ncard_le]
  constructor
  · rintro ⟨hfinite, hcard⟩
    have hempty : A \ B = ∅ :=
      Set.ncard_eq_zero hfinite |>.mp (Nat.eq_zero_of_le_zero hcard)
    exact Set.diff_eq_empty.mp hempty
  · intro hAB
    simp [Set.diff_eq_empty.mpr hAB]

/-- At most `n` distinct values in the range of `stream` lie outside `L`. -/
def ValuesOutsideAtMost
    (stream : Stream α) (L : Language α) (n : ℕ) : Prop :=
  SetDifferenceAtMost (Set.range stream) L n

theorem valuesOutsideAtMost_mono
    {stream : Stream α} {L : Language α} {i j : ℕ}
    (hij : i ≤ j) (h : ValuesOutsideAtMost stream L i) :
    ValuesOutsideAtMost stream L j :=
  setDifferenceAtMost_mono hij h

/-- An occurrence-counted contaminated presentation.  Repetitions are
allowed, every target value is covered, and at most `n` time indices are
outside the target. -/
def OccurrenceContaminatedPresentationAtMost
    (stream : Stream α) (L : Language α) (n : ℕ) : Prop :=
  (ViolationIndices stream (fun x => x ∈ L)).Finite ∧
    (ViolationIndices stream (fun x => x ∈ L)).ncard ≤ n ∧
    L ⊆ Set.range stream

theorem occurrenceContaminatedPresentationAtMost_mono
    {stream : Stream α} {L : Language α} {i j : ℕ}
    (hij : i ≤ j)
    (h : OccurrenceContaminatedPresentationAtMost stream L i) :
    OccurrenceContaminatedPresentationAtMost stream L j :=
  ⟨h.1, h.2.1.trans hij, h.2.2⟩

/-- An occurrence-counted presentation with an unspecified finite number of
invalid observations. -/
def OccurrenceContaminatedPresentation
    (stream : Stream α) (L : Language α) : Prop :=
  L ⊆ Set.range stream ∧
    FinitelyManyViolations stream (fun x => x ∈ L)

/-- An injective presentation with at most `n` distinct range values outside
the target. -/
def InjectiveValueContaminatedPresentationAtMost
    (stream : Stream α) (L : Language α) (n : ℕ) : Prop :=
  Function.Injective stream ∧
    L ⊆ Set.range stream ∧
    ValuesOutsideAtMost stream L n

theorem injectiveValueContaminatedPresentationAtMost_mono
    {stream : Stream α} {L : Language α} {i j : ℕ}
    (hij : i ≤ j)
    (h : InjectiveValueContaminatedPresentationAtMost stream L i) :
    InjectiveValueContaminatedPresentationAtMost stream L j :=
  ⟨h.1, h.2.1, valuesOutsideAtMost_mono hij h.2.2⟩

/-- An injective presentation with finitely many distinct range values
outside the target. -/
def InjectiveValueContaminatedPresentation
    (stream : Stream α) (L : Language α) : Prop :=
  Function.Injective stream ∧
    L ⊆ Set.range stream ∧
    (Set.range stream \ L).Finite

theorem valuesOutside_eq_image_violationIndices
    (stream : Stream α) (L : Language α) :
    Set.range stream \ L =
      stream '' ViolationIndices stream (fun x => x ∈ L) := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, rfl⟩, ht⟩

/-- For an injective stream, counting distinct invalid values is equivalent
to counting invalid occurrences. -/
theorem valuesOutsideAtMost_iff_violationsAtMost_of_injective
    {stream : Stream α} {L : Language α}
    (hinjective : Function.Injective stream) (n : ℕ) :
    ValuesOutsideAtMost stream L n ↔
      ViolationsAtMost stream (fun x => x ∈ L) n := by
  rw [ValuesOutsideAtMost,
    setDifferenceAtMost_iff_finite_ncard_le,
    ViolationsAtMost,
    valuesOutside_eq_image_violationIndices]
  rw [Set.finite_image_iff hinjective.injOn,
    Set.ncard_image_of_injective _ hinjective]

/-- The unbounded finite variants likewise agree for injective streams. -/
theorem finite_valuesOutside_iff_finitelyManyViolations_of_injective
    {stream : Stream α} {L : Language α}
    (hinjective : Function.Injective stream) :
    (Set.range stream \ L).Finite ↔
      FinitelyManyViolations stream (fun x => x ∈ L) := by
  rw [FinitelyManyViolations, valuesOutside_eq_image_violationIndices,
    Set.finite_image_iff hinjective.injOn]

end GenLimit.Generic
