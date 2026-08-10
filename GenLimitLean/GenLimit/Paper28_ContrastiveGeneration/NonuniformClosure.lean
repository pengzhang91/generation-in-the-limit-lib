import GenLimit.Paper28_ContrastiveGeneration.ClosureDimension
import GenLimit.Core.ClassCovers
import Mathlib.Data.Finset.Max

/-!
# Non-uniform contrastive generation

This file formalizes Theorem 5.5 of Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*
(arXiv:2605.06211v1).

The source's threshold-and-defer construction selects the largest component
whose closure-dimension threshold has been reached.  We use the literal
padded threshold

`m + CΔ(𝓗 m) + 1`.

The padding by `m` bounds every active index by the finite distinct-edge
count, so the maximum is mathematically well-defined without an additional
monotonicity assumption on a chosen sequence of dimension bounds.
-/

namespace GenLimit
namespace ContrastiveGeneration

/-- One generator has a target-dependent finite distinct-edge threshold. -/
def NonuniformlyContrastivelyGenerates
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α)) : Prop :=
  ∀ h, h ∈ 𝓗 →
    ∃ d, ∀ t, ∀ history : Fin t → Edge α,
      (∀ i, Crosses h (history i)) →
      d ≤ (distinctUnorderedEdges history).card →
        G t history ∈ h ∧ G t history ∉ seenPrefix history

/-- Definition 5.2's non-uniform contrastive generatability. -/
def NonuniformlyContrastivelyGeneratable
    (𝓗 : Set (Set α)) : Prop :=
  ∃ G : ContrastiveGenerator α,
    NonuniformlyContrastivelyGenerates G 𝓗

/-- The targets on which `G` is uniformly correct after `n+1` distinct
unordered edges.  The shift makes the closure-dimension bound at level `n`
equal to `n`. -/
def generatorLevel
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α))
    (n : ℕ) : Set (Set α) :=
  {h | h ∈ 𝓗 ∧
    ∀ t, ∀ history : Fin t → Edge α,
      (∀ i, Crosses h (history i)) →
      n + 1 ≤ (distinctUnorderedEdges history).card →
        G t history ∈ h ∧ G t history ∉ seenPrefix history}

theorem generatorLevel_mono
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α)) :
    Monotone (generatorLevel G 𝓗) := by
  intro m n hmn h hh
  constructor
  · exact hh.1
  · intro t history hcross hcard
    exact hh.2 t history hcross
      ((Nat.add_le_add_right hmn 1).trans hcard)

theorem generatorLevels_cover
    {G : ContrastiveGenerator α} {𝓗 : Set (Set α)}
    (hG : NonuniformlyContrastivelyGenerates G 𝓗) :
    𝓗 = ⋃ n, generatorLevel G 𝓗 n := by
  ext h
  constructor
  · intro hh
    obtain ⟨d, hd⟩ := hG h hh
    refine Set.mem_iUnion.mpr ⟨d, hh, ?_⟩
    intro t history hcross hcard
    exact hd t history hcross
      ((Nat.le_succ d).trans hcard)
  · intro hh
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
    exact hn.1

theorem generatorLevel_uniform
    {G : ContrastiveGenerator α} {𝓗 : Set (Set α)}
    (n : ℕ) :
    UniformlyContrastivelyGeneratesAt
      G (generatorLevel G 𝓗 n) (n + 1) := by
  intro h hh t history hcross hcard
  exact hh.2 t history hcross hcard

/-- Necessity in Theorem 5.5: target-dependent thresholds stratify the class
into a nondecreasing cover of finite closure dimension. -/
theorem theorem_5_5_necessity
    {𝓗 : Set (Set α)}
    (hNonuniform : NonuniformlyContrastivelyGeneratable 𝓗) :
    ∃ classes : ℕ → Set (Set α),
      GenLimit.Generic.IsNondecreasingCover 𝓗 classes ∧
      ∀ n, FiniteContrastiveClosureDimension (classes n) := by
  obtain ⟨G, hG⟩ := hNonuniform
  let classes := generatorLevel G 𝓗
  refine ⟨classes, ?_, ?_⟩
  · exact
      ⟨generatorLevel_mono G 𝓗,
        generatorLevels_cover hG⟩
  · intro n
    refine ⟨n, ?_⟩
    exact generator_implies_dimension_bound
      (generatorLevel_uniform (G := G) (𝓗 := 𝓗) n)

/-- One selected finite bound on each component's contrastive closure
dimension. -/
noncomputable def selectedClosureBound
    (classes : ℕ → Set (Set α))
    (hdim : ∀ n, FiniteContrastiveClosureDimension (classes n))
    (n : ℕ) : ℕ :=
  Classical.choose (hdim n)

theorem selectedClosureBound_spec
    {classes : ℕ → Set (Set α)}
    (hdim : ∀ n, FiniteContrastiveClosureDimension (classes n))
    (n : ℕ) :
    ContrastiveClosureDimensionAtMost
      (classes n) (selectedClosureBound classes hdim n) :=
  Classical.choose_spec (hdim n)

/-- The paper's padded threshold `m + CΔ(𝓗_m) + 1`, using any selected
finite upper bound on the dimension. -/
def nonuniformPaddedThreshold
    (bound : ℕ → ℕ) (m : ℕ) : ℕ :=
  m + bound m + 1

/-- Component indices whose padded threshold has been reached at distinct
edge count `k`. -/
def nonuniformEligibleLevels
    (bound : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter
    (fun m => nonuniformPaddedThreshold bound m ≤ k)

theorem mem_nonuniformEligibleLevels_iff
    {bound : ℕ → ℕ} {m k : ℕ} :
    m ∈ nonuniformEligibleLevels bound k ↔
      nonuniformPaddedThreshold bound m ≤ k := by
  simp only [nonuniformEligibleLevels, Finset.mem_filter,
    Finset.mem_range, Nat.lt_add_one_iff]
  constructor
  · exact fun h => h.2
  · intro h
    constructor
    · exact
        (Nat.le_add_right m (bound m + 1)).trans h
    · exact h

/-- The maximum currently active component. -/
noncomputable def selectedNonuniformLevel
    (bound : ℕ → ℕ) (k : ℕ)
    (hE : (nonuniformEligibleLevels bound k).Nonempty) : ℕ :=
  (nonuniformEligibleLevels bound k).max' hE

theorem selectedNonuniformLevel_mem
    {bound : ℕ → ℕ} {k : ℕ}
    (hE : (nonuniformEligibleLevels bound k).Nonempty) :
    selectedNonuniformLevel bound k hE ∈
      nonuniformEligibleLevels bound k :=
  Finset.max'_mem _ _

theorem le_selectedNonuniformLevel
    {bound : ℕ → ℕ} {m k : ℕ}
    (hm : m ∈ nonuniformEligibleLevels bound k)
    (hE : (nonuniformEligibleLevels bound k).Nonempty) :
    m ≤ selectedNonuniformLevel bound k hE :=
  Finset.le_max' _ _ hm

/-- The threshold-and-defer generator in the sufficiency proof of
Theorem 5.5. -/
noncomputable def nonuniformClosureGenerator
    [Nonempty α]
    (classes : ℕ → Set (Set α)) (bound : ℕ → ℕ) :
    ContrastiveGenerator α := by
  classical
  exact fun t history =>
    let k := (distinctUnorderedEdges history).card
    let eligible := nonuniformEligibleLevels bound k
    if hE : eligible.Nonempty then
      closureDimensionGenerator (classes (eligible.max' hE))
        t history
    else
      Classical.choice inferInstance

theorem nonuniformClosureGenerator_eq_selected
    [Nonempty α]
    {classes : ℕ → Set (Set α)} {bound : ℕ → ℕ}
    {t : ℕ} {history : Fin t → Edge α}
    (hE :
      (nonuniformEligibleLevels bound
        (distinctUnorderedEdges history).card).Nonempty) :
    nonuniformClosureGenerator classes bound t history =
      closureDimensionGenerator
        (classes
          (selectedNonuniformLevel bound
            (distinctUnorderedEdges history).card hE))
        t history := by
  simp only [nonuniformClosureGenerator,
    dif_pos hE, selectedNonuniformLevel]

/-- Sufficiency in Theorem 5.5.  The proof uses one closure generator at the
largest active component and monotonicity of the cover to retain the target. -/
theorem theorem_5_5_sufficiency
    [Nonempty α] {𝓗 : Set (Set α)}
    {classes : ℕ → Set (Set α)}
    (hcover :
      GenLimit.Generic.IsNondecreasingCover 𝓗 classes)
    (hdim : ∀ n,
      FiniteContrastiveClosureDimension (classes n)) :
    NonuniformlyContrastivelyGeneratable 𝓗 := by
  classical
  let bound := selectedClosureBound classes hdim
  let G := nonuniformClosureGenerator classes bound
  refine ⟨G, ?_⟩
  intro h hh
  have hhUnion : h ∈ ⋃ n, classes n := by
    rw [← hcover.2]
    exact hh
  obtain ⟨targetLevel, hhTarget⟩ :=
    Set.mem_iUnion.mp hhUnion
  refine
    ⟨nonuniformPaddedThreshold bound targetLevel, ?_⟩
  intro t history hcross hcard
  let k := (distinctUnorderedEdges history).card
  let eligible := nonuniformEligibleLevels bound k
  have htargetMem : targetLevel ∈ eligible := by
    exact mem_nonuniformEligibleLevels_iff.mpr hcard
  have hE : eligible.Nonempty :=
    ⟨targetLevel, htargetMem⟩
  let selected := selectedNonuniformLevel bound k hE
  have hselectedMem : selected ∈ eligible :=
    selectedNonuniformLevel_mem hE
  have htargetSelected : targetLevel ≤ selected :=
    le_selectedNonuniformLevel htargetMem hE
  have hhSelected : h ∈ classes selected :=
    hcover.1 htargetSelected hhTarget
  have hselectedThreshold :
      nonuniformPaddedThreshold bound selected ≤ k :=
    mem_nonuniformEligibleLevels_iff.mp hselectedMem
  have hdimensionThreshold :
      bound selected + 1 ≤ k := by
    exact
      (Nat.le_add_left (bound selected + 1) selected).trans
        (by
          simpa [nonuniformPaddedThreshold,
            Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hselectedThreshold)
  have hselectedCorrect :=
    dimensionBound_suffices
      (selectedClosureBound_spec hdim selected)
      h hhSelected t history hcross hdimensionThreshold
  have houtput :
      G t history =
        closureDimensionGenerator (classes selected) t history := by
    simpa [G, bound, k, eligible, selected] using
      nonuniformClosureGenerator_eq_selected
        (classes := classes)
        (bound := bound)
        (history := history)
        hE
  simpa [houtput] using hselectedCorrect

/-- Theorem 5.5: non-uniform contrastive generation is equivalent to being
an increasing union of classes of finite contrastive closure dimension. -/
theorem theorem_5_5
    [Nonempty α] (𝓗 : Set (Set α)) :
    NonuniformlyContrastivelyGeneratable 𝓗 ↔
      ∃ classes : ℕ → Set (Set α),
        GenLimit.Generic.IsNondecreasingCover 𝓗 classes ∧
        ∀ n, FiniteContrastiveClosureDimension (classes n) := by
  constructor
  · exact theorem_5_5_necessity
  · rintro ⟨classes, hcover, hdim⟩
    exact theorem_5_5_sufficiency hcover hdim

end ContrastiveGeneration
end GenLimit
