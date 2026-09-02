import GenLimit.Core.FiniteContamination
import GenLimit.Core.OrderedDensity
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Infinite contamination: source-faithful semantic definitions

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Sections 3.1--3.6.

The source uses repetition-free enumerations.  We therefore keep
`Function.Injective stream` separate from the noise and omission predicates
and include it in every paper-level enumeration predicate below.  A prefix of
length `n` is indexed by `Finset.range n`, matching the source's
`x₁, ..., xₙ`.  The value at `n = 0` is set to zero; this convention has no
effect on an asymptotic noise rate.

The paper's element generator has a stronger freshness requirement than the
generic project API: its output must avoid both the observed sample and every
earlier generated value.  `FreshElementCorrectAt` records that literal rule.
-/

namespace GenLimit.InfiniteContamination

open Filter
open scoped Topology
open GenLimit.KleinbergWei

/-! ## Noise and omission regimes (Definitions 6--8) -/

/-- Number of contaminated occurrences among the first `n` inputs. -/
noncomputable def noiseCount
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter fun t => stream t ∉ L).card

/-- Definition 6: empirical noise rate in the first `n` inputs.

The artificial zero-length prefix is assigned rate zero. -/
noncomputable def empiricalNoiseRate
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (noiseCount stream L n : ℝ) / n

@[simp] theorem empiricalNoiseRate_zero
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) :
    empiricalNoiseRate stream L 0 = 0 := by
  simp [empiricalNoiseRate]

theorem noiseCount_le
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) :
    noiseCount stream L n ≤ n := by
  classical
  simpa [noiseCount] using
    Finset.card_filter_le
      (s := Finset.range n) (p := fun t => stream t ∉ L)

theorem empiricalNoiseRate_nonneg
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) :
    0 ≤ empiricalNoiseRate stream L n := by
  by_cases hn : n = 0
  · simp [empiricalNoiseRate, hn]
  · simp only [empiricalNoiseRate, hn, if_false]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem empiricalNoiseRate_le_one
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) :
    empiricalNoiseRate stream L n ≤ 1 := by
  by_cases hn : n = 0
  · simp [empiricalNoiseRate, hn]
  · simp only [empiricalNoiseRate, hn, if_false]
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_le_one hnpos]
    exact_mod_cast noiseCount_le stream L n

/-- There is no additive noise: every displayed value belongs to `L`. -/
abbrev NoNoise
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  GenLimit.Generic.StreamIn stream L

/-- Definition 7, finite-noise component.

Because paper-level enumerations are injective, finiteness of the bad time
indices is equivalent to finiteness of the distinct noisy values. -/
abbrev FiniteNoise
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  GenLimit.Generic.FinitelyManyViolations stream (fun x => x ∈ L)

/-- Definition 7, `o(1)`-noise component. -/
def VanishingNoise
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Tendsto (empiricalNoiseRate stream L) atTop (𝓝 0)

/-- Definition 7, eventual `c`-noise component. -/
def ConstantNoise
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (c : ℝ) : Prop :=
  ∃ N, ∀ n, N ≤ n → empiricalNoiseRate stream L n ≤ c

/-- No omissions: every target string occurs in the stream. -/
def NoOmissions
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  L ⊆ Set.range stream

/-- Definition 8, finite omissions. -/
def FiniteOmissions
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  (L \ Set.range stream).Finite

/-- Definition 8, arbitrary omissions: the true part that remains is
infinite. -/
def ArbitraryOmissions
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  (Set.range stream ∩ L).Infinite

/-- Definition 8, `c`-omissions, with the paper's canonical ordering of the
target supplied as an `OrderedLanguage`. -/
def OmissionsAtMost
    (stream : GenLimit.Generic.Stream ℕ)
    (K : OrderedLanguage) (c : ℝ) : Prop :=
  1 - c ≤ K.lowerDensity (Set.range stream ∩ K.carrier)

/-- A repetition-free full enumeration with finite additive noise. -/
def FiniteNoiseEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Function.Injective stream ∧ NoOmissions stream L ∧ FiniteNoise stream L

/-- On the repetition-free streams used by the paper, the occurrence-based
finite-noise predicate is equivalent to the Core predicate saying that only
finitely many distinct displayed values lie outside the target. -/
theorem finiteNoise_iff_valuesOutside_finite_of_injective
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hinjective : Function.Injective stream) :
    FiniteNoise stream L ↔ (Set.range stream \ L).Finite :=
  (GenLimit.Generic.finite_valuesOutside_iff_finitelyManyViolations_of_injective
    hinjective).symm

/-- `FiniteNoiseEnumeration` is exactly the paper-independent Core interface
for an injective, fully covering presentation with finite contamination. -/
theorem finiteNoiseEnumeration_iff_core
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) :
    FiniteNoiseEnumeration stream L ↔
      GenLimit.Generic.InjectiveValueContaminatedPresentation stream L := by
  constructor
  · rintro ⟨hinjective, hcover, hnoise⟩
    exact ⟨hinjective, hcover,
      (finiteNoise_iff_valuesOutside_finite_of_injective hinjective).mp hnoise⟩
  · rintro ⟨hinjective, hcover, hnoise⟩
    exact ⟨hinjective, hcover,
      (finiteNoise_iff_valuesOutside_finite_of_injective hinjective).mpr hnoise⟩

/-- A repetition-free full enumeration with vanishing additive noise. -/
def VanishingNoiseEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Function.Injective stream ∧ NoOmissions stream L ∧ VanishingNoise stream L

/-- A repetition-free full enumeration with eventual noise rate at most
`c`. -/
def ConstantNoiseEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (c : ℝ) : Prop :=
  Function.Injective stream ∧ NoOmissions stream L ∧ ConstantNoise stream L c

/-- Finite noise together with arbitrary omissions. -/
def FiniteNoiseArbitraryOmissionEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Function.Injective stream ∧
    ArbitraryOmissions stream L ∧ FiniteNoise stream L

/-- The adversary class in Theorem 5.1: vanishing noise and arbitrary
omissions. -/
def VanishingNoiseArbitraryOmissionEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Function.Injective stream ∧
    ArbitraryOmissions stream L ∧ VanishingNoise stream L

/-- The adversary class in Theorem 5.4: eventual `c`-noise and arbitrary
omissions. -/
def ConstantNoiseArbitraryOmissionEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (c : ℝ) : Prop :=
  Function.Injective stream ∧
    ArbitraryOmissions stream L ∧ ConstantNoise stream L c

/-- A no-noise repetition-free enumeration with finite omissions. -/
def FiniteOmissionEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Function.Injective stream ∧
    NoNoise stream L ∧ FiniteOmissions stream L

/-- The combined finite-contamination presentation from §3.5 and Theorem 6.5:
the stream is repetition-free, has only finitely many values outside the
target, and may omit only finitely many target values.

This predicate is intentionally distinct from `FiniteNoiseEnumeration`,
whose middle conjunct requires **no** omissions, and from
`FiniteOmissionEnumeration`, whose middle conjunct requires **no** noise. -/
def FiniteNoiseFiniteOmissionEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Function.Injective stream ∧
    FiniteNoise stream L ∧ FiniteOmissions stream L

/-- A no-noise repetition-free enumeration with arbitrary omissions. -/
def ArbitraryOmissionEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Function.Injective stream ∧
    NoNoise stream L ∧ ArbitraryOmissions stream L

/-! ## Literal element-output freshness -/

/-- All values generated strictly before time `t`. -/
noncomputable def generatedBefore
    (gen : GenLimit.Generic.Generator α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Finset α := by
  classical
  exact (Finset.range t).image (GenLimit.Generic.output gen stream)

theorem mem_generatedBefore_iff
    {gen : GenLimit.Generic.Generator α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ} {x : α} :
    x ∈ generatedBefore gen stream t ↔
      ∃ s < t, GenLimit.Generic.output gen stream s = x := by
  classical
  simp [generatedBefore]

/-- Definition 3's complete correctness rule at time `t`: the output is in
the target, unseen in the input prefix, and distinct from every earlier
output. -/
def FreshElementCorrectAt
    (gen : GenLimit.Generic.Generator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  GenLimit.Generic.output gen stream t ∈ L ∧
    GenLimit.Generic.output gen stream t ∉
      GenLimit.Generic.sample stream t ∧
    GenLimit.Generic.output gen stream t ∉
      generatedBefore gen stream t

/-- Eventual element generation on one fixed target and stream. -/
def GeneratesElementInLimitOn
    (gen : GenLimit.Generic.Generator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) : Prop :=
  ∃ T, ∀ t, T ≤ t → FreshElementCorrectAt gen L stream t

/-- Set-valued prefix generators from Definition 4. -/
abbrev SetGenerator (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → Set α

/-- The source's set-generator codomain: every output is infinite, including
outputs on finite histories that do not arise from a particular run. -/
def IsInfiniteSetGenerator (gen : SetGenerator α) : Prop :=
  ∀ t samples, (gen t samples).Infinite

/-- Output of a set generator on the prefix strictly before `t`. -/
def setOutput
    (gen : SetGenerator α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Set α :=
  gen t (fun i => stream i)

/-- A set output is valid and avoids all observed strings. -/
def SetCorrectAt
    (gen : SetGenerator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  setOutput gen stream t ⊆ L ∧
    Disjoint (setOutput gen stream t)
      (↑(GenLimit.Generic.sample stream t) : Set α)

/-- Source-faithful set correctness: in addition to validity and freshness,
the output set is infinite.  This strengthens `SetCorrectAt` without changing
the existing weak predicate used by the density obstruction results. -/
def InfiniteSetCorrectAt
    (gen : SetGenerator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  SetCorrectAt gen L stream t ∧
    (setOutput gen stream t).Infinite

/-- Infinite-output correctness forgets to ordinary set correctness. -/
theorem InfiniteSetCorrectAt.setCorrectAt
    {gen : SetGenerator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (h : InfiniteSetCorrectAt gen L stream t) :
    SetCorrectAt gen L stream t :=
  h.1

/-- Infinite-output correctness exposes the source's infinitude condition. -/
theorem InfiniteSetCorrectAt.output_infinite
    {gen : SetGenerator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (h : InfiniteSetCorrectAt gen L stream t) :
    (setOutput gen stream t).Infinite :=
  h.2

/-- Index-valued ("proper") prefix generators from Definition 2. -/
abbrev IndexGenerator (ι α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → ι

/-- Output of an index generator on a stream prefix. -/
def indexOutput
    (gen : IndexGenerator ι α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : ι :=
  gen t (fun i => stream i)

/-- Proper correctness: the selected family member is contained in the
target. -/
def IndexCorrectAt
    (family : ι → GenLimit.Generic.Language α)
    (gen : IndexGenerator ι α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  family (indexOutput gen stream t) ⊆ L

end GenLimit.InfiniteContamination
