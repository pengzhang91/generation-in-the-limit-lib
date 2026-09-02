import GenLimit.Paper19_EffectOfNoise.SquareRoot
import GenLimit.Paper06_NoisyExamples.Nonuniform
import Mathlib.Data.Nat.Find

/-!
# Quantifying Noise: non-uniform finite-noise collapse

This module formalizes the non-uniform half of Theorem 2.16 and the
Section 4 characterization in Li--Zhang,
*Characterizing the Effect of Noise in Language Generation in the Limit*,
arXiv:2601.21237v2.

The key point in Lemma 4.1 is that the generators witnessing uniform
generatability of the countably many layers need not agree.  The paper
dovetails them by running, at time `t`, the generator in the largest layer
whose selected uniform threshold has already elapsed.  `scheduledLayer`
implements that maximum literally using `Nat.findGreatest`.

All statements below use the paper's injective enumerations and inclusive
time convention.  The Raman--Raman API is used only in the sufficiency
direction of the noise-dependent characterization, where its stronger
generator is transported to the paper API by the proved bridge.
-/

namespace GenLimit.QuantifyingNoise

/-! ## The countable exhaustion in Lemma 4.1 -/

/-- The right-hand side of Lemma 4.1: an increasing countable exhaustion
whose every layer has finite noisy-closure dimension at the fixed level. -/
def HasFiniteDimensionExhaustionAt
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) : Prop :=
  ∃ layers : ℕ → GenLimit.Generic.LanguageClass α,
    Monotone layers ∧
      C = ⋃ j, layers j ∧
      ∀ j, FiniteNoisyClosureDimensionAt (layers j) i

/-- The subclass on which one fixed generator is already correct from paper
time `j` onwards.  This is the canonical exhaustion used in the necessity
direction of Lemma 4.1. -/
def correctFromClass
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) (i j : ℕ) :
    GenLimit.Generic.LanguageClass α :=
  {L | L ∈ C ∧
    ∀ stream : GenLimit.Generic.Stream α,
      EnumerationWithNoiseAtMost stream L i →
      ∀ t, j ≤ t → CorrectAt gen L stream t}

theorem correctFromClass_mono
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) :
    Monotone (correctFromClass gen C i) := by
  intro j k hjk L hL
  refine ⟨hL.1, ?_⟩
  intro stream henum t hkt
  exact hL.2 stream henum t (hjk.trans hkt)

theorem correctFromClass_cover
    {gen : GenLimit.Generic.Generator α}
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hgen : IsNonuniformGeneratorAtNoiseLevel gen C i) :
    C = ⋃ j, correctFromClass gen C i j := by
  ext L
  constructor
  · intro hLC
    obtain ⟨T, hT⟩ := hgen L hLC
    exact Set.mem_iUnion.mpr ⟨T, hLC, hT⟩
  · intro hL
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hL
    exact hj.1

/-! ## The paper's maximum-index dovetail -/

/-- At paper time `t`, choose the largest layer `j ≤ t` whose selected
uniform threshold has elapsed.  If there is no such positive layer, Lean's
`findGreatest` convention returns zero; correctness is only claimed once a
target-containing layer is eligible. -/
def scheduledLayer (threshold : ℕ → ℕ) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun j => threshold j ≤ t) t

theorem scheduledLayer_le
    (threshold : ℕ → ℕ) (t : ℕ) :
    scheduledLayer threshold t ≤ t :=
  Nat.findGreatest_le t

theorem le_scheduledLayer
    {threshold : ℕ → ℕ} {j t : ℕ}
    (hjt : j ≤ t) (helapsed : threshold j ≤ t) :
    j ≤ scheduledLayer threshold t :=
  Nat.le_findGreatest hjt helapsed

theorem scheduledLayer_elapsed
    {threshold : ℕ → ℕ} {j t : ℕ}
    (hjt : j ≤ t) (helapsed : threshold j ≤ t) :
    threshold (scheduledLayer threshold t) ≤ t :=
  Nat.findGreatest_spec
    (P := fun k => threshold k ≤ t) hjt helapsed

/-- Run the generator selected by `scheduledLayer`.  A generic history of
length `n` corresponds to paper time `n-1`; in particular, an `outputAt`
call at paper time `t` selects the layer scheduled at exactly `t`. -/
def dovetailGenerator
    (gens : ℕ → GenLimit.Generic.Generator α)
    (threshold : ℕ → ℕ) :
    GenLimit.Generic.Generator α :=
  fun n xs => gens (scheduledLayer threshold (n - 1)) n xs

theorem outputAt_dovetailGenerator
    (gens : ℕ → GenLimit.Generic.Generator α)
    (threshold : ℕ → ℕ)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    outputAt (dovetailGenerator gens threshold) stream t =
      outputAt (gens (scheduledLayer threshold t)) stream t := by
  simp [outputAt, dovetailGenerator]

theorem correctAt_dovetailGenerator
    (gens : ℕ → GenLimit.Generic.Generator α)
    (threshold : ℕ → ℕ)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    CorrectAt (dovetailGenerator gens threshold) L stream t ↔
      CorrectAt (gens (scheduledLayer threshold t)) L stream t := by
  simp only [CorrectAt, outputAt_dovetailGenerator]

/-! ## Lemma 4.1 -/

/-- Lemma 4.1, necessity: a non-uniform generator gives an increasing
exhaustion by the languages on which its threshold is at most `j`. -/
theorem nonuniform_fixed_level_implies_dimension_exhaustion
    [Countable α]
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hInfinite : AllLanguagesInfinite C)
    (hgen : NonuniformGeneratableAtNoiseLevel C i) :
    HasFiniteDimensionExhaustionAt C i := by
  obtain ⟨gen, hgen⟩ := hgen
  refine ⟨correctFromClass gen C i,
    correctFromClass_mono gen C i,
    correctFromClass_cover hgen, ?_⟩
  intro j
  apply uniform_fixed_level_implies_finite_dimension
  · intro L hL
    exact hInfinite L hL.1
  · exact ⟨gen, j, fun L hL => hL.2⟩

/-- Lemma 4.1, sufficiency: uniformly generate each layer, then execute the
paper's largest-eligible-index schedule. -/
theorem dimension_exhaustion_implies_nonuniform_fixed_level
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hInfinite : AllLanguagesInfinite C)
    (hexhaustion : HasFiniteDimensionExhaustionAt C i) :
    NonuniformGeneratableAtNoiseLevel C i := by
  classical
  obtain ⟨layers, hlayersMono, hlayersCover, hlayersDim⟩ := hexhaustion
  have hlayersInfinite : ∀ j, AllLanguagesInfinite (layers j) := by
    intro j L hLj
    apply hInfinite L
    rw [hlayersCover]
    exact Set.mem_iUnion.mpr ⟨j, hLj⟩
  have huniform :
      ∀ j, UniformGeneratableAtNoiseLevel (layers j) i := by
    intro j
    exact (lemma_3_1 (hlayersInfinite j)).mpr (hlayersDim j)
  choose gens hgens using huniform
  choose threshold hthreshold using fun j => hgens j
  refine ⟨dovetailGenerator gens threshold, ?_⟩
  intro L hLC
  have hLUnion : L ∈ ⋃ j, layers j := by
    rw [← hlayersCover]
    exact hLC
  obtain ⟨j, hLj⟩ := Set.mem_iUnion.mp hLUnion
  refine ⟨max j (threshold j), ?_⟩
  intro stream henum t ht
  have hjt : j ≤ t :=
    (Nat.le_max_left j (threshold j)).trans ht
  have hjThreshold : threshold j ≤ t :=
    (Nat.le_max_right j (threshold j)).trans ht
  let selected := scheduledLayer threshold t
  have hjSelected : j ≤ selected :=
    le_scheduledLayer hjt hjThreshold
  have hLSelected : L ∈ layers selected :=
    hlayersMono hjSelected hLj
  have hSelectedElapsed : threshold selected ≤ t :=
    scheduledLayer_elapsed hjt hjThreshold
  rw [correctAt_dovetailGenerator]
  exact
    hthreshold selected L hLSelected stream henum t
      hSelectedElapsed

/-- Lemma 4.1 in the paper's literal injective, inclusive-time model. -/
theorem lemma_4_1
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hInfinite : AllLanguagesInfinite C) :
    NonuniformGeneratableAtNoiseLevel C i ↔
      HasFiniteDimensionExhaustionAt C i := by
  constructor
  · exact
      nonuniform_fixed_level_implies_dimension_exhaustion hInfinite
  · exact
      dimension_exhaustion_implies_nonuniform_fixed_level hInfinite

/-! ## Theorem 4.2 and the non-uniform half of Theorem 2.16 -/

/-- Theorem 4.2: every positive finite noise level gives the same
non-uniform generatability class as level one. -/
theorem theorem_4_2_nonuniform_finite_noise_collapse
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C)
    {i : ℕ} (hi : 1 ≤ i) :
    NonuniformGeneratableAtNoiseLevel C i ↔
      NonuniformGeneratableAtNoiseLevel C 1 := by
  constructor
  · exact nonuniformGeneratableAtNoiseLevel_anti hi
  · intro hOne
    obtain ⟨layers, hmono, hcover, hdimOne⟩ :=
      (lemma_4_1 hInfinite (i := 1)).mp hOne
    apply (lemma_4_1 hInfinite (i := i)).mpr
    refine ⟨layers, hmono, hcover, ?_⟩
    intro j
    exact finite_dimension_propagates_from_one
      (hdimOne j) i hi

/-- Paper-numbered alias for the non-uniform half of Theorem 2.16. -/
theorem theorem_2_16_nonuniform
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C)
    {i : ℕ} (hi : 1 ≤ i) :
    NonuniformGeneratableAtNoiseLevel C i ↔
      NonuniformGeneratableAtNoiseLevel C 1 :=
  theorem_4_2_nonuniform_finite_noise_collapse hInfinite hi

/-- Theorem 2.16 in one declaration, combining the uniform result from
Section 3 with the non-uniform result above. -/
theorem theorem_2_16
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C)
    {i : ℕ} (hi : 1 ≤ i) :
    (UniformGeneratableAtNoiseLevel C i ↔
        UniformGeneratableAtNoiseLevel C 1) ∧
      (NonuniformGeneratableAtNoiseLevel C i ↔
        NonuniformGeneratableAtNoiseLevel C 1) :=
  ⟨theorem_2_16_uniform hInfinite hi,
    theorem_2_16_nonuniform hInfinite hi⟩

/-! ## Non-uniform noise-dependent generation -/

/-- Lemma 4.5.  A level-one finite-dimension exhaustion suffices for one
generator at every finite noise level.

The diagonal sufficiency theorem of Raman--Raman is applicable after
propagating the `j`th layer's level-one dimension to level `j`.  Its
generator handles the more permissive repeated-stream model, so the
`rr_nonuniform_implies_nonuniformNoiseDependent` bridge gives precisely the
paper's injective Definition 2.7. -/
theorem lemma_4_5
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C)
    (hexhaustion : HasFiniteDimensionExhaustionAt C 1) :
    NonuniformNoiseDependentGeneratable C := by
  obtain ⟨layers, hmono, hcover, hdimOne⟩ := hexhaustion
  have hdimDiagonal :
      ∀ j, FiniteNoisyClosureDimensionAt (layers j) j := by
    intro j
    by_cases hj : j = 0
    · subst j
      exact finiteNoisyClosureDimensionAt_anti
        (i := 0) (j := 1) (by omega) (hdimOne 0)
    · exact finite_dimension_propagates_from_one
        (hdimOne j) j (Nat.one_le_iff_ne_zero.mpr hj)
  have hrrDim :
      ∀ j,
        GenLimit.NoisyExamples.FiniteNoisyClosureDimensionAt
          (layers j) j := by
    intro j
    exact
      (finiteNoisyClosureDimensionAt_iff_rr (layers j) j).mp
        (hdimDiagonal j)
  have hrr :
      GenLimit.NoisyExamples.NonuniformNoiseDependentGeneratable C := by
    apply GenLimit.NoisyExamples.lemma_3_6 hInfinite
    · exact ⟨hmono, hcover⟩
    · exact hrrDim
  exact rr_nonuniform_implies_nonuniformNoiseDependent hrr

/-- Lemma 4.6.  Necessity needs only the level-one component of the
paper's one-generator-for-all-levels definition, followed by Lemma 4.1. -/
theorem lemma_4_6
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C)
    (hgen : NonuniformNoiseDependentGeneratable C) :
    HasFiniteDimensionExhaustionAt C 1 := by
  obtain ⟨gen, hgen⟩ := hgen
  apply (lemma_4_1 hInfinite (i := 1)).mp
  exact ⟨gen, hgen 1⟩

/-- Theorem 4.7: exact characterization of non-uniform noise-dependent
generatability by a countable increasing level-one finite-dimension
exhaustion. -/
theorem theorem_4_7
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C) :
    NonuniformNoiseDependentGeneratable C ↔
      HasFiniteDimensionExhaustionAt C 1 := by
  constructor
  · exact lemma_4_6 hInfinite
  · exact lemma_4_5 hInfinite

/-- The three positive equivalences in Theorem 2.19.  As in the existing
uniform Theorem 2.18 declaration, the separate noiseless/noisy separation
is kept out of this conjunction and belongs to Theorem 2.17. -/
theorem theorem_2_19_nonuniform_equivalences
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C) :
    HasFiniteDimensionExhaustionAt C 1 ↔
      ((∀ i : ℕ, 1 ≤ i →
          NonuniformGeneratableAtNoiseLevel C i) ∧
        NonuniformNoiseDependentGeneratable C) := by
  constructor
  · intro hexhaustion
    have hOne :
        NonuniformGeneratableAtNoiseLevel C 1 :=
      (lemma_4_1 hInfinite (i := 1)).mpr hexhaustion
    refine ⟨?_, (theorem_4_7 hInfinite).mpr hexhaustion⟩
    intro i hi
    exact
      (theorem_4_2_nonuniform_finite_noise_collapse
        hInfinite hi).mpr hOne
  · rintro ⟨hlevels, _hdependent⟩
    exact
      (lemma_4_1 hInfinite (i := 1)).mp
        (hlevels 1 (by omega))

/-- Literal three-way packaging of the positive non-uniform equivalences in
Theorem 2.19.  Both other conditions are separately equivalent to a
level-one finite-dimension exhaustion. -/
theorem theorem_2_19_nonuniform_equivalences_full
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C) :
    (HasFiniteDimensionExhaustionAt C 1 ↔
      ∀ i : ℕ, 1 ≤ i → NonuniformGeneratableAtNoiseLevel C i) ∧
    (HasFiniteDimensionExhaustionAt C 1 ↔
      NonuniformNoiseDependentGeneratable C) := by
  refine ⟨?_, (theorem_4_7 hInfinite).symm⟩
  constructor
  · intro hExhaustion
    exact (theorem_2_19_nonuniform_equivalences hInfinite).mp hExhaustion |>.1
  · intro hLevels
    exact
      (lemma_4_1 hInfinite (i := 1)).mp
        (hLevels 1 (by omega))

end GenLimit.QuantifyingNoise
