import GenLimit.Paper06_NoisyExamples.NoisyClosure
import GenLimit.Support.FiniteContamination

/-!
# Quantifying Noise: paper-facing definitions

Source: *Characterizing the Effect of Noise on Language Generation*,
arXiv:2601.21237v2, Definitions 2.1--2.7 and 2.14--2.15.

This module deliberately does not identify the paper's enumerations with the
older Raman--Raman stream API.  Definition 2.5 requires an injective infinite
sequence whose range contains the target and has at most `i` extraneous
*values*.  Moreover, at paper time `t` the algorithm has already observed
`x₀,...,xₜ`; hence `observed stream t` is the generic sample at `t + 1`.
-/

namespace GenLimit.QuantifyingNoise

/-- A set `S` has at most `i` elements outside `L`.

The finite witness is used instead of `Set.ncard`: `Set.ncard` is zero on an
infinite set, whereas the paper's cardinal inequality forces the difference
to be finite. -/
abbrev MissingAtMost (S L : Set α) (i : ℕ) : Prop :=
  GenLimit.Support.MissingAtMost S L i

theorem missingAtMost_mono
    {S L : Set α} {i j : ℕ} (hij : i ≤ j)
    (h : MissingAtMost S L i) :
    MissingAtMost S L j :=
  GenLimit.Support.missingAtMost_mono hij h

theorem missingAtMost_empty (L : Set α) (i : ℕ) :
    MissingAtMost (∅ : Set α) L i := by
  refine ⟨∅, ?_, by simp⟩
  ext x
  simp

/-- Definition 2.5: an injective enumeration of `L` with noise level at most
`i`.  The range may contain fewer than `i` extraneous strings. -/
abbrev EnumerationWithNoiseAtMost
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (i : ℕ) : Prop :=
  GenLimit.Support.EnumerationWithNoiseAtMost stream L i

theorem enumerationWithNoiseAtMost_mono
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i j : ℕ}
    (hij : i ≤ j) (h : EnumerationWithNoiseAtMost stream L i) :
    EnumerationWithNoiseAtMost stream L j :=
  GenLimit.Support.enumerationWithNoiseAtMost_mono hij h

/-- The paper's set `S(x)_t = {x₀,...,xₜ}`. -/
noncomputable def observed
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Finset α :=
  GenLimit.Generic.sample stream (t + 1)

/-- Run the generator after observing `x₀,...,xₜ`. -/
def outputAt
    (gen : GenLimit.Generic.Generator α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : α :=
  gen (t + 1) (fun k => stream k)

/-- Correctness at paper time `t`: output a target string outside
`S(x)_t`. -/
def CorrectAt
    (gen : GenLimit.Generic.Generator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  outputAt gen stream t ∈ L ∧ outputAt gen stream t ∉ observed stream t

theorem correctAt_iff_generic
    {gen : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ} :
    CorrectAt gen L stream t ↔
      GenLimit.Generic.CorrectAt gen L stream (t + 1) := by
  rfl

theorem observed_eq_sequenceSample
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    observed stream t =
      GenLimit.Generic.sequenceSample
        (fun k : Fin (t + 1) => stream k) := by
  simpa [observed] using
    (GenLimit.Generic.sequenceSample_prefix stream (t + 1)).symm

theorem observed_card_of_injective
    {stream : GenLimit.Generic.Stream α}
    (hinj : Function.Injective stream) (t : ℕ) :
    (observed stream t).card = t + 1 := by
  rw [observed_eq_sequenceSample]
  apply GenLimit.NoisyExamples.sequenceSample_card_of_injective
  intro a b hab
  exact Fin.ext (hinj hab)

/-- Definition 2.14 at a fixed generator. -/
def IsUniformGeneratorAtNoiseLevel
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) : Prop :=
  ∃ T : ℕ, ∀ L, L ∈ C →
    ∀ stream : GenLimit.Generic.Stream α,
      EnumerationWithNoiseAtMost stream L i →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Uniform generatability at the fixed noise level `i` (Definition 2.14). -/
def UniformGeneratableAtNoiseLevel
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsUniformGeneratorAtNoiseLevel gen C i

/-- Definition 2.15 at a fixed generator. -/
def IsNonuniformGeneratorAtNoiseLevel
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) : Prop :=
  ∀ L, L ∈ C → ∃ T : ℕ,
    ∀ stream : GenLimit.Generic.Stream α,
      EnumerationWithNoiseAtMost stream L i →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Non-uniform generatability at the fixed noise level `i`
(Definition 2.15). -/
def NonuniformGeneratableAtNoiseLevel
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsNonuniformGeneratorAtNoiseLevel gen C i

/-- Definition 2.6: one generator, with a uniform time bound allowed to
depend on the finite noise level. -/
def IsUniformNoiseDependentGenerator
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ i : ℕ, IsUniformGeneratorAtNoiseLevel gen C i

def UniformNoiseDependentGeneratable
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsUniformNoiseDependentGenerator gen C

/-- Definition 2.7: the time bound may depend on both noise level and target,
but not on the enumeration. -/
def IsNonuniformNoiseDependentGenerator
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ i : ℕ, IsNonuniformGeneratorAtNoiseLevel gen C i

def NonuniformNoiseDependentGeneratable
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsNonuniformNoiseDependentGenerator gen C

/-! ## Elementary fixed-level implications -/

theorem isUniformGeneratorAtNoiseLevel_anti
    {gen : GenLimit.Generic.Generator α}
    {C : GenLimit.Generic.LanguageClass α} {i j : ℕ}
    (hij : i ≤ j) (h : IsUniformGeneratorAtNoiseLevel gen C j) :
    IsUniformGeneratorAtNoiseLevel gen C i := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro L hLC stream henum
  exact hT L hLC stream (enumerationWithNoiseAtMost_mono hij henum)

theorem uniformGeneratableAtNoiseLevel_anti
    {C : GenLimit.Generic.LanguageClass α} {i j : ℕ}
    (hij : i ≤ j) (h : UniformGeneratableAtNoiseLevel C j) :
    UniformGeneratableAtNoiseLevel C i := by
  obtain ⟨gen, hgen⟩ := h
  exact ⟨gen, isUniformGeneratorAtNoiseLevel_anti hij hgen⟩

theorem isNonuniformGeneratorAtNoiseLevel_anti
    {gen : GenLimit.Generic.Generator α}
    {C : GenLimit.Generic.LanguageClass α} {i j : ℕ}
    (hij : i ≤ j) (h : IsNonuniformGeneratorAtNoiseLevel gen C j) :
    IsNonuniformGeneratorAtNoiseLevel gen C i := by
  intro L hLC
  obtain ⟨T, hT⟩ := h L hLC
  refine ⟨T, ?_⟩
  intro stream henum
  exact hT stream (enumerationWithNoiseAtMost_mono hij henum)

theorem nonuniformGeneratableAtNoiseLevel_anti
    {C : GenLimit.Generic.LanguageClass α} {i j : ℕ}
    (hij : i ≤ j) (h : NonuniformGeneratableAtNoiseLevel C j) :
    NonuniformGeneratableAtNoiseLevel C i := by
  obtain ⟨gen, hgen⟩ := h
  exact ⟨gen, isNonuniformGeneratorAtNoiseLevel_anti hij hgen⟩

/-! ## Bridge from injective, value-bounded noise to the Raman--Raman API -/

/-- An injective enumeration with at most `i` extraneous values also has at
most `i` extraneous time indices.  Injectivity is essential here. -/
theorem hasNoiseAtMost_of_enumerationWithNoiseAtMost
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i : ℕ}
    (h : EnumerationWithNoiseAtMost stream L i) :
    GenLimit.NoisyExamples.HasNoiseAtMost stream L i := by
  apply
    (GenLimit.Generic.valuesOutsideAtMost_iff_violationsAtMost_of_injective
      h.1 i).mp
  exact h.2.2

end GenLimit.QuantifyingNoise
