import GenLimit.Paper17_InfiniteContamination.EvenDensity
import Mathlib.Tactic.Linarith

/-!
# Set-density obstructions under omissions

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Theorem 6.4 and Example 6.6.

The general theorem below isolates the exact semantic obstruction behind
Theorem 6.4.  If one input stream is compatible with a smaller target `L₁`
and a larger target `L₂`, eventual validity for `L₁` forces every late output
inside `L₁`; its set-based upper density in `L₂` therefore cannot exceed the
ordered density of `L₁` in `L₂`.
-/

namespace GenLimit.InfiniteContamination

open Filter
open scoped Topology
open GenLimit.KleinbergWei

/-- Eventual set generation on one fixed target and stream. -/
def GeneratesSetInLimitOn
    (gen : SetGenerator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) : Prop :=
  ∃ T, ∀ t, T ≤ t → SetCorrectAt gen L stream t

/-- Eventual set generation with the source's global infinite-output
requirement.  Infinitude is a property of the generator on every finite
history, not merely of the eventually correct outputs along this run. -/
def GeneratesInfiniteSetInLimitOn
    (gen : SetGenerator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) : Prop :=
  IsInfiniteSetGenerator gen ∧
    GeneratesSetInLimitOn gen L stream

/-- Infinite-output generation implies the pre-existing weak set-generation
predicate. -/
theorem GeneratesInfiniteSetInLimitOn.generatesSetInLimitOn
    {gen : SetGenerator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α}
    (h : GeneratesInfiniteSetInLimitOn gen L stream) :
    GeneratesSetInLimitOn gen L stream :=
  h.2

/-- A source-typed set generator has an infinite output on every history. -/
theorem GeneratesInfiniteSetInLimitOn.output_infinite
    {gen : SetGenerator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α}
    (h : GeneratesInfiniteSetInLimitOn gen L stream)
    (t : ℕ) :
    (setOutput gen stream t).Infinite :=
  h.1 t (fun i => stream i)

/-- Compatibility form of the global infinitude guarantee. -/
theorem GeneratesInfiniteSetInLimitOn.eventually_output_infinite
    {gen : SetGenerator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α}
    (h : GeneratesInfiniteSetInLimitOn gen L stream) :
    ∃ T, ∀ t, T ≤ t → (setOutput gen stream t).Infinite := by
  exact ⟨0, fun t _ht => h.output_infinite t⟩

/-- Definition 10's set-based upper density: at each time first take the
ordered lower density of the output set in the target, then take `limsup`
over time. -/
noncomputable def setBasedUpperDensity
    (gen : SetGenerator ℕ)
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ) : ℝ :=
  limsup (fun t => K.lowerDensity (setOutput gen stream t)) atTop

/-- Definition 10's set-based lower density. -/
noncomputable def setBasedLowerDensity
    (gen : SetGenerator ℕ)
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ) : ℝ :=
  liminf (fun t => K.lowerDensity (setOutput gen stream t)) atTop

/-- A pointwise eventual containment yields the corresponding upper-density
bound. -/
theorem setBasedUpperDensity_le_of_eventually_subset
    (gen : SetGenerator ℕ)
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (A : Set ℕ)
    (hsubset :
      ∀ᶠ t : ℕ in atTop, setOutput gen stream t ⊆ A) :
    setBasedUpperDensity gen K stream ≤ K.lowerDensity A := by
  unfold setBasedUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun t =>
        K.lowerDensity_nonneg (setOutput gen stream t))
  · filter_upwards [hsubset] with t ht
    exact K.lowerDensity_mono ht

/-- The analytic obstruction used in the necessity half of Theorem 6.5:
if infinitely many outputs are contained in `A`, the generator's set-based
lower density cannot exceed the density of `A` in the target.

The paper's alternating-prefix adversary is the separate combinatorial step
that produces this frequent containment from its asymmetric finite-difference
hypothesis. -/
theorem setBasedLowerDensity_le_of_frequently_subset
    (gen : SetGenerator ℕ)
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (A : Set ℕ)
    (hsubset :
      ∃ᶠ t : ℕ in atTop, setOutput gen stream t ⊆ A) :
    setBasedLowerDensity gen K stream ≤ K.lowerDensity A := by
  unfold setBasedLowerDensity
  apply liminf_le_of_frequently_le
  · exact hsubset.mono fun t ht =>
      K.lowerDensity_mono ht
  · exact isBoundedUnder_of
      ⟨0, fun t =>
        K.lowerDensity_nonneg (setOutput gen stream t)⟩

/-- General semantic obstruction behind Theorem 6.4. -/
theorem theorem_6_4_semantic_obstruction
    (gen : SetGenerator ℕ)
    (K₂ : OrderedLanguage)
    (L₁ : Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ)
    (hgenerate₁ : GeneratesSetInLimitOn gen L₁ stream) :
    setBasedUpperDensity gen K₂ stream ≤ K₂.lowerDensity L₁ := by
  obtain ⟨T, hT⟩ := hgenerate₁
  apply setBasedUpperDensity_le_of_eventually_subset
  exact (eventually_atTop.2 ⟨T, fun t ht => (hT t ht).1⟩)

/-! ## The concrete half-density instance -/

/-- Canonical repetition-free enumeration of the even numbers. -/
def evenStream : GenLimit.Generic.Stream ℕ := fun n => 2 * n

theorem evenStream_injective :
    Function.Injective evenStream := by
  intro m n h
  simp only [evenStream] at h
  omega

theorem range_evenStream :
    Set.range evenStream = evenNaturals := by
  ext n
  simp [evenStream, evenNaturals, eq_comm, even_iff_exists_two_mul]

theorem evenStream_noNoise :
    NoNoise evenStream evenNaturals := by
  change Set.range evenStream ⊆ evenNaturals
  rw [range_evenStream]

theorem evenStream_noOmissions :
    NoOmissions evenStream evenNaturals := by
  rw [NoOmissions, range_evenStream]

theorem evenStream_exactEnumeration :
    Function.Injective evenStream ∧
      NoNoise evenStream evenNaturals ∧
      NoOmissions evenStream evenNaturals :=
  ⟨evenStream_injective, evenStream_noNoise, evenStream_noOmissions⟩

/-- The even stream omits exactly one half of the canonical `ℕ` target in
the ordered-density sense. -/
theorem evenStream_half_omissions :
    OmissionsAtMost evenStream naturalOrder (1 / 2 : ℝ) := by
  unfold OmissionsAtMost
  rw [range_evenStream]
  have hcarrier :
      evenNaturals ∩ naturalOrder.carrier = evenNaturals := by
    ext n
    simp [naturalOrder]
  rw [hcarrier, evenNaturals_lowerDensity]
  norm_num

/-- The concrete `1/2` instance of Theorem 6.4. -/
theorem theorem_6_4_half_density_instance
    (gen : SetGenerator ℕ)
    (hgenerateEven :
      GeneratesSetInLimitOn gen evenNaturals evenStream) :
    setBasedUpperDensity gen naturalOrder evenStream ≤ (1 / 2 : ℝ) := by
  calc
    setBasedUpperDensity gen naturalOrder evenStream
        ≤ naturalOrder.lowerDensity evenNaturals :=
      theorem_6_4_semantic_obstruction
        gen naturalOrder evenNaturals evenStream hgenerateEven
    _ = (1 / 2 : ℝ) := evenNaturals_lowerDensity

/-- Impossibility form matching the source prose: the same stream cannot
force eventual validity for the even target while attaining upper density
strictly above one half when interpreted as a presentation with one-half
omissions from `ℕ`. -/
theorem theorem_6_4_no_better_than_half
    (gen : SetGenerator ℕ) :
    ¬(GeneratesSetInLimitOn gen evenNaturals evenStream ∧
      (1 / 2 : ℝ) <
        setBasedUpperDensity gen naturalOrder evenStream) := by
  rintro ⟨hgenerate, hdense⟩
  exact (not_lt_of_ge
    (theorem_6_4_half_density_instance gen hgenerate)) hdense

end GenLimit.InfiniteContamination
