import GenLimit.Core.GenericGeneration
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FieldSimp

/-!
# Finite contamination

Paper-independent vocabulary for streams with finitely many invalid
occurrences or finitely many distinct values outside a target.  The two
counting conventions are kept separate: they agree for injective streams,
but differ when observations may repeat.
-/

namespace GenLimit.Generic

/-! ## Quantitative finite-sample contamination -/

/-- Number of elements of a finite sample satisfying `Acceptable`.  The
sample type is deliberately generic: callers may sample time indices (and
therefore count occurrences) or values (and therefore count distinct
elements). -/
noncomputable def acceptedCount
    (Acceptable : α → Prop) (sample : Finset α) : ℕ := by
  classical
  exact (sample.filter Acceptable).card

/-- Number of elements of a finite sample violating `Acceptable`. -/
noncomputable def rejectedCount
    (Acceptable : α → Prop) (sample : Finset α) : ℕ := by
  classical
  exact (sample.filter fun x => ¬Acceptable x).card

theorem acceptedCount_le
    (Acceptable : α → Prop) (sample : Finset α) :
    acceptedCount Acceptable sample ≤ sample.card := by
  classical
  exact Finset.card_filter_le _ _

theorem rejectedCount_le
    (Acceptable : α → Prop) (sample : Finset α) :
    rejectedCount Acceptable sample ≤ sample.card := by
  classical
  exact Finset.card_filter_le _ _

/-- Accepted and rejected elements partition a finite sample. -/
theorem acceptedCount_add_rejectedCount
    (Acceptable : α → Prop) (sample : Finset α) :
    acceptedCount Acceptable sample + rejectedCount Acceptable sample =
      sample.card := by
  classical
  unfold acceptedCount rejectedCount
  exact Finset.filter_card_add_filter_neg_card_eq_card
    (s := sample) (p := Acceptable)

theorem acceptedCount_mono
    {P Q : α → Prop} (hPQ : ∀ x, P x → Q x) (sample : Finset α) :
    acceptedCount P sample ≤ acceptedCount Q sample := by
  classical
  unfold acceptedCount
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hx).1, hPQ x (Finset.mem_filter.mp hx).2⟩

theorem rejectedCount_anti
    {P Q : α → Prop} (hPQ : ∀ x, P x → Q x) (sample : Finset α) :
    rejectedCount Q sample ≤ rejectedCount P sample := by
  classical
  unfold rejectedCount
  apply Finset.card_le_card
  intro x hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, ?_⟩
  exact fun hPx => (Finset.mem_filter.mp hx).2 (hPQ x hPx)

/-- Accepted fraction of a finite sample.  Empty samples receive value zero. -/
noncomputable def acceptedFraction
    (Acceptable : α → Prop) (sample : Finset α) : ℝ :=
  if sample.card = 0 then 0
  else (acceptedCount Acceptable sample : ℝ) / sample.card

/-- Rejected fraction of a finite sample.  Empty samples receive value zero. -/
noncomputable def rejectedFraction
    (Acceptable : α → Prop) (sample : Finset α) : ℝ :=
  if sample.card = 0 then 0
  else (rejectedCount Acceptable sample : ℝ) / sample.card

@[simp] theorem acceptedFraction_empty (Acceptable : α → Prop) :
    acceptedFraction Acceptable ∅ = 0 := by
  simp [acceptedFraction]

@[simp] theorem rejectedFraction_empty (Acceptable : α → Prop) :
    rejectedFraction Acceptable ∅ = 0 := by
  simp [rejectedFraction]

theorem acceptedFraction_nonneg
    (Acceptable : α → Prop) (sample : Finset α) :
    0 ≤ acceptedFraction Acceptable sample := by
  by_cases hs : sample.card = 0
  · simp [acceptedFraction, hs]
  · simp only [acceptedFraction, hs, if_false]
    positivity

theorem rejectedFraction_nonneg
    (Acceptable : α → Prop) (sample : Finset α) :
    0 ≤ rejectedFraction Acceptable sample := by
  by_cases hs : sample.card = 0
  · simp [rejectedFraction, hs]
  · simp only [rejectedFraction, hs, if_false]
    positivity

theorem acceptedFraction_le_one
    (Acceptable : α → Prop) (sample : Finset α) :
    acceptedFraction Acceptable sample ≤ 1 := by
  by_cases hs : sample.card = 0
  · simp [acceptedFraction, hs]
  · simp only [acceptedFraction, hs, if_false]
    have hpos : (0 : ℝ) < sample.card := by
      exact_mod_cast Nat.pos_of_ne_zero hs
    rw [div_le_one hpos]
    exact_mod_cast acceptedCount_le Acceptable sample

theorem rejectedFraction_le_one
    (Acceptable : α → Prop) (sample : Finset α) :
    rejectedFraction Acceptable sample ≤ 1 := by
  by_cases hs : sample.card = 0
  · simp [rejectedFraction, hs]
  · simp only [rejectedFraction, hs, if_false]
    have hpos : (0 : ℝ) < sample.card := by
      exact_mod_cast Nat.pos_of_ne_zero hs
    rw [div_le_one hpos]
    exact_mod_cast rejectedCount_le Acceptable sample

theorem acceptedFraction_mono
    {P Q : α → Prop} (hPQ : ∀ x, P x → Q x) (sample : Finset α) :
    acceptedFraction P sample ≤ acceptedFraction Q sample := by
  by_cases hs : sample.card = 0
  · simp [acceptedFraction, hs]
  · simp only [acceptedFraction, hs, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast acceptedCount_mono hPQ sample)
      (Nat.cast_nonneg _)

theorem rejectedFraction_anti
    {P Q : α → Prop} (hPQ : ∀ x, P x → Q x) (sample : Finset α) :
    rejectedFraction Q sample ≤ rejectedFraction P sample := by
  by_cases hs : sample.card = 0
  · simp [rejectedFraction, hs]
  · simp only [rejectedFraction, hs, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast rejectedCount_anti hPQ sample)
      (Nat.cast_nonneg _)

/-- On a nonempty sample, accepted and rejected fractions are complements. -/
theorem acceptedFraction_eq_one_sub_rejectedFraction
    (Acceptable : α → Prop) {sample : Finset α}
    (hs : sample.card ≠ 0) :
    acceptedFraction Acceptable sample =
      1 - rejectedFraction Acceptable sample := by
  simp only [acceptedFraction, rejectedFraction, hs, if_false]
  have hsumNat := acceptedCount_add_rejectedCount Acceptable sample
  have hsumReal :
      (acceptedCount Acceptable sample : ℝ) +
          (rejectedCount Acceptable sample : ℝ) = (sample.card : ℝ) := by
    exact_mod_cast hsumNat
  have hcardReal : (sample.card : ℝ) ≠ 0 := by exact_mod_cast hs
  field_simp
  linarith

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
