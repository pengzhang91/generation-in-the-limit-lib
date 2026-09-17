import GenLimit.Core.GenericGeneration

/-!
# Paper-independent eventual-generation quantifiers

Several generation models differ only in which presentations are admissible
and in the convention used to state correctness at a time.  This module
isolates their three recurring quantifier patterns: a class-uniform threshold,
a target-dependent threshold, and a presentation-dependent threshold.

The admissibility and correctness predicates remain explicit parameters.  In
particular, this layer does not identify exact, noisy, injective, or feedback
presentations, and it does not impose either an inclusive or exclusive time
convention.
-/

namespace GenLimit.Generic

/-- One threshold works for every target and admissible presentation. -/
def IsUniformEventuallyCorrect
    (correct : Generator α → Language α → Stream α → ℕ → Prop)
    (admissible : Stream α → Language α → Prop)
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∃ T, ∀ L, L ∈ C → ∀ stream, admissible stream L →
    ∀ t, T ≤ t → correct gen L stream t

/-- The threshold may depend on the target, but not on its presentation. -/
def IsTargetwiseEventuallyCorrect
    (correct : Generator α → Language α → Stream α → ℕ → Prop)
    (admissible : Stream α → Language α → Prop)
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∃ T, ∀ stream, admissible stream L →
    ∀ t, T ≤ t → correct gen L stream t

/-- The threshold may depend on both the target and its presentation. -/
def IsPresentationwiseEventuallyCorrect
    (correct : Generator α → Language α → Stream α → ℕ → Prop)
    (admissible : Stream α → Language α → Prop)
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∀ stream, admissible stream L →
    ∃ T, ∀ t, T ≤ t → correct gen L stream t

theorem uniformEventuallyCorrect_implies_targetwise
    {correct : Generator α → Language α → Stream α → ℕ → Prop}
    {admissible : Stream α → Language α → Prop}
    {gen : Generator α} {C : LanguageClass α}
    (h : IsUniformEventuallyCorrect correct admissible gen C) :
    IsTargetwiseEventuallyCorrect correct admissible gen C := by
  obtain ⟨T, hT⟩ := h
  intro L hLC
  exact ⟨T, hT L hLC⟩

theorem targetwiseEventuallyCorrect_implies_presentationwise
    {correct : Generator α → Language α → Stream α → ℕ → Prop}
    {admissible : Stream α → Language α → Prop}
    {gen : Generator α} {C : LanguageClass α}
    (h : IsTargetwiseEventuallyCorrect correct admissible gen C) :
    IsPresentationwiseEventuallyCorrect correct admissible gen C := by
  intro L hLC
  obtain ⟨T, hT⟩ := h L hLC
  intro stream hstream
  exact ⟨T, hT stream hstream⟩

/-- A guarantee for a broader presentation model restricts to any narrower
model. -/
theorem uniformEventuallyCorrect_mono_admissible
    {correct : Generator α → Language α → Stream α → ℕ → Prop}
    {admissible₁ admissible₂ : Stream α → Language α → Prop}
    {gen : Generator α} {C : LanguageClass α}
    (hadmissible : ∀ stream L, admissible₁ stream L → admissible₂ stream L)
    (h : IsUniformEventuallyCorrect correct admissible₂ gen C) :
    IsUniformEventuallyCorrect correct admissible₁ gen C := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro L hLC stream hstream
  exact hT L hLC stream (hadmissible stream L hstream)

theorem targetwiseEventuallyCorrect_mono_admissible
    {correct : Generator α → Language α → Stream α → ℕ → Prop}
    {admissible₁ admissible₂ : Stream α → Language α → Prop}
    {gen : Generator α} {C : LanguageClass α}
    (hadmissible : ∀ stream L, admissible₁ stream L → admissible₂ stream L)
    (h : IsTargetwiseEventuallyCorrect correct admissible₂ gen C) :
    IsTargetwiseEventuallyCorrect correct admissible₁ gen C := by
  intro L hLC
  obtain ⟨T, hT⟩ := h L hLC
  refine ⟨T, ?_⟩
  intro stream hstream
  exact hT stream (hadmissible stream L hstream)

theorem presentationwiseEventuallyCorrect_mono_admissible
    {correct : Generator α → Language α → Stream α → ℕ → Prop}
    {admissible₁ admissible₂ : Stream α → Language α → Prop}
    {gen : Generator α} {C : LanguageClass α}
    (hadmissible : ∀ stream L, admissible₁ stream L → admissible₂ stream L)
    (h : IsPresentationwiseEventuallyCorrect correct admissible₂ gen C) :
    IsPresentationwiseEventuallyCorrect correct admissible₁ gen C := by
  intro L hLC stream hstream
  exact h L hLC stream (hadmissible stream L hstream)

end GenLimit.Generic
