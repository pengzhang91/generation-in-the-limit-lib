import GenLimit.Paper17_InfiniteContamination.EvenDensity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
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

/-- The P17 run-wise predicate is definitionally the generic Core predicate. -/
theorem generatesSetInLimitOn_iff_generic
    (gen : SetGenerator α) (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) :
    GeneratesSetInLimitOn gen L stream ↔
      GenLimit.Generic.GeneratesSetInLimitOn gen L stream :=
  Iff.rfl

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

/-! ## Arbitrary-density witnesses -/

/-- The lower mechanical word of slope `p`, regarded as a subset of the
natural numbers.  Membership at `n` records that the floor of `p * n`
increases between `n` and `n + 1`.

For `0 ≤ p ≤ 1`, every increment is zero or one, so the number of
members below `n` telescopes to exactly `⌊p * n⌋`. -/
noncomputable def floorIncrementLanguage (p : ℝ) : GenLimit.Language :=
  {n | ⌊p * (n + 1 : ℕ)⌋₊ = ⌊p * (n : ℕ)⌋₊ + 1}

theorem floor_mul_succ_eq_or_eq_add_one
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    ⌊p * (n + 1 : ℕ)⌋₊ = ⌊p * (n : ℕ)⌋₊ ∨
      ⌊p * (n + 1 : ℕ)⌋₊ = ⌊p * (n : ℕ)⌋₊ + 1 := by
  have hmonoReal : p * (n : ℝ) ≤ p * (n + 1 : ℕ) := by
    gcongr
    omega
  have hmono : ⌊p * (n : ℕ)⌋₊ ≤ ⌊p * (n + 1 : ℕ)⌋₊ :=
    Nat.floor_mono hmonoReal
  have hupperReal : p * (n + 1 : ℕ) ≤ p * (n : ℕ) + 1 := by
    push_cast
    nlinarith
  have hupper : ⌊p * (n + 1 : ℕ)⌋₊ ≤ ⌊p * (n : ℕ)⌋₊ + 1 := by
    calc
      ⌊p * (n + 1 : ℕ)⌋₊ ≤ ⌊p * (n : ℕ) + 1⌋₊ :=
        Nat.floor_mono hupperReal
      _ = ⌊p * (n : ℕ)⌋₊ + 1 := by
        rw [Nat.floor_add_one]
        positivity
  omega

/-- Exact finite-prefix count for the arbitrary-density witness. -/
theorem naturalOrder_prefixCount_floorIncrementLanguage
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    naturalOrder.prefixCount (floorIncrementLanguage p) n =
      ⌊p * (n : ℕ)⌋₊ := by
  induction n with
  | zero =>
      simp [OrderedLanguage.prefixCount, floorIncrementLanguage]
  | succ n ih =>
      classical
      have hrecurrence :
          naturalOrder.prefixCount (floorIncrementLanguage p) (n + 1) =
            naturalOrder.prefixCount (floorIncrementLanguage p) n +
              if n ∈ floorIncrementLanguage p then 1 else 0 := by
        classical
        unfold OrderedLanguage.prefixCount
        dsimp [naturalOrder]
        rw [Finset.range_add_one, Finset.filter_insert]
        by_cases hmem : n ∈ floorIncrementLanguage p
        · simp [hmem]
        · simp [hmem]
      rw [hrecurrence, ih]
      rcases floor_mul_succ_eq_or_eq_add_one p hp0 hp1 n with hsame | hstep
      · have hnotmem : n ∉ floorIncrementLanguage p := by
          simp only [floorIncrementLanguage, Set.mem_setOf_eq]
          omega
        rw [if_neg hnotmem, Nat.add_zero]
        simpa only [Nat.cast_add, Nat.cast_one] using hsame.symm
      · have hmem : n ∈ floorIncrementLanguage p := by
          simpa [floorIncrementLanguage] using hstep
        rw [if_pos hmem]
        simpa only [Nat.cast_add, Nat.cast_one] using hstep.symm

/-- The finite prefix ratios of the witness converge to its slope. -/
theorem tendsto_naturalOrder_prefixRatio_floorIncrementLanguage
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Tendsto (naturalOrder.prefixRatio (floorIncrementLanguage p))
      atTop (𝓝 p) := by
  have hfloor :
      Tendsto (fun n : ℕ => (⌊p * (n : ℕ)⌋₊ : ℝ) / n)
        atTop (𝓝 p) :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hp0).comp
      tendsto_natCast_atTop_atTop
  apply hfloor.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [OrderedLanguage.prefixRatio, hn,
    naturalOrder_prefixCount_floorIncrementLanguage p hp0 hp1]

/-- Every slope in `[0,1]` is realized as an exact lower density. -/
theorem floorIncrementLanguage_lowerDensity
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    naturalOrder.lowerDensity (floorIncrementLanguage p) = p := by
  exact
    (tendsto_naturalOrder_prefixRatio_floorIncrementLanguage p hp0 hp1).liminf_eq

/-- Every slope in `[0,1]` is realized as an exact upper density. -/
theorem floorIncrementLanguage_upperDensity
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    naturalOrder.upperDensity (floorIncrementLanguage p) = p := by
  exact
    (tendsto_naturalOrder_prefixRatio_floorIncrementLanguage p hp0 hp1).limsup_eq

/-- A positive-slope witness contains infinitely many natural numbers. -/
theorem floorIncrementLanguage_infinite
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (floorIncrementLanguage p).Infinite := by
  intro hfinite
  have htendsto :
      Tendsto (fun n : ℕ => ⌊p * (n : ℕ)⌋₊) atTop atTop :=
    tendsto_nat_floor_mul_atTop p hp
  obtain ⟨n, hn⟩ :=
    (tendsto_atTop.1 htendsto
      (hfinite.toFinset.card + 1)).exists
  have hcard :=
    naturalOrder.prefixCount_le_ncard_of_finite hfinite n
  rw [naturalOrder_prefixCount_floorIncrementLanguage
    p hp.le hp1] at hcard
  omega

/-- Increasing enumeration of the arbitrary-density witness. -/
noncomputable def floorIncrementStream (p : ℝ) :
    GenLimit.Generic.Stream ℕ :=
  Nat.nth fun n => n ∈ floorIncrementLanguage p

theorem floorIncrementStream_injective
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    Function.Injective (floorIncrementStream p) := by
  exact Nat.nth_injective
    (floorIncrementLanguage_infinite p hp hp1)

theorem range_floorIncrementStream
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    Set.range (floorIncrementStream p) = floorIncrementLanguage p := by
  exact Nat.range_nth_of_infinite
    (floorIncrementLanguage_infinite p hp hp1)

/-- The witness language equipped with its increasing enumeration. -/
noncomputable def floorIncrementOrder
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) : OrderedLanguage where
  carrier := floorIncrementLanguage p
  enumeration := floorIncrementStream p
  enumeration_injective := floorIncrementStream_injective p hp hp1
  range_enumeration := range_floorIncrementStream p hp hp1

theorem floorIncrementStream_noNoise
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    NoNoise (floorIncrementStream p) (floorIncrementLanguage p) := by
  rw [← range_floorIncrementStream p hp hp1]
  exact Set.Subset.rfl

theorem floorIncrementStream_noOmissions
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    NoOmissions (floorIncrementStream p) (floorIncrementLanguage p) := by
  rw [NoOmissions, range_floorIncrementStream p hp hp1]

theorem floorIncrementStream_omissionsAtMost_self
    (p c : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hc0 : 0 ≤ c) :
    OmissionsAtMost (floorIncrementStream p)
      (floorIncrementOrder p hp hp1) c := by
  unfold OmissionsAtMost
  rw [range_floorIncrementStream p hp hp1]
  change 1 - c ≤
    (floorIncrementOrder p hp hp1).lowerDensity
      ((floorIncrementOrder p hp hp1).carrier ∩
        (floorIncrementOrder p hp hp1).carrier)
  rw [Set.inter_self, OrderedLanguage.lowerDensity_carrier]
  linarith

theorem floorIncrementStream_exact_omissions_in_naturals
    (p c : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpc : p = 1 - c) :
    OmissionsAtMost (floorIncrementStream p) naturalOrder c := by
  unfold OmissionsAtMost
  change 1 - c ≤
    naturalOrder.lowerDensity
      (Set.range (floorIncrementStream p) ∩ Set.univ)
  rw [Set.inter_univ, range_floorIncrementStream p hp hp1]
  rw [floorIncrementLanguage_lowerDensity p hp.le hp1, hpc]

/-- A generator meets an upper-density target uniformly over a family and
its supplied canonical target orderings, for every no-noise injective stream
whose omissions are at most `c`. -/
def GuaranteesSetBasedUpperDensityUnderOmissionsOn
    (gen : SetGenerator ℕ)
    (family : ι → GenLimit.Language)
    (orders : ι → OrderedLanguage)
    (c ρ : ℝ) : Prop :=
  ∀ z stream,
    Function.Injective stream →
    NoNoise stream (family z) →
    OmissionsAtMost stream (orders z) c →
    GeneratesSetInLimitOn gen (family z) stream ∧
      ρ ≤ setBasedUpperDensity gen (orders z) stream

/-- The two-language hard family for Theorem 6.4.  The `false` member is
the mechanical density witness and the `true` member is all naturals. -/
def theoremSixFourFamily (p : ℝ) : Bool → GenLimit.Language :=
  fun b => if b then Set.univ else floorIncrementLanguage p

/-- Canonical orderings matching `theoremSixFourFamily`. -/
noncomputable def theoremSixFourOrders
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) : Bool → OrderedLanguage :=
  fun b => if b then naturalOrder else floorIncrementOrder p hp hp1

@[simp] theorem theoremSixFourOrders_carrier
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (b : Bool) :
    (theoremSixFourOrders p hp hp1 b).carrier = theoremSixFourFamily p b := by
  cases b <;> rfl

/-- Full arbitrary-constant instance of Theorem 6.4.

For every omission allowance `c ∈ (0,1)`, the explicit two-language family
`{floorIncrementLanguage (1-c), ℕ}` defeats every uniform generator at
every requested upper-density level strictly above `1-c`.  The same
repetition-free stream is a complete noiseless enumeration of the smaller
language and a noiseless `c`-omission enumeration of the larger one. -/
theorem theorem_6_4_arbitrary_constant
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ gen : SetGenerator ℕ,
      ¬ GuaranteesSetBasedUpperDensityUnderOmissionsOn gen
        (theoremSixFourFamily (1 - c))
        (theoremSixFourOrders (1 - c) (by linarith) (by linarith))
        c (1 - c + ε) := by
  intro ε hε gen hguarantee
  let p : ℝ := 1 - c
  have hp : 0 < p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  let stream := floorIncrementStream p
  have hinjective : Function.Injective stream :=
    floorIncrementStream_injective p hp hp1
  have hsmall := hguarantee false stream hinjective
    (floorIncrementStream_noNoise p hp hp1)
    (floorIncrementStream_omissionsAtMost_self p c hp hp1 hc0.le)
  have hlarge := hguarantee true stream hinjective
    (by intro n; simp [theoremSixFourFamily])
    (floorIncrementStream_exact_omissions_in_naturals
      p c hp hp1 rfl)
  have hobstruction :
      setBasedUpperDensity gen naturalOrder stream ≤ p := by
    calc
      setBasedUpperDensity gen naturalOrder stream ≤
          naturalOrder.lowerDensity (floorIncrementLanguage p) :=
        theorem_6_4_semantic_obstruction
          gen naturalOrder (floorIncrementLanguage p) stream
          (by
            simpa [p, theoremSixFourFamily, theoremSixFourOrders]
              using hsmall.1)
      _ = p := floorIncrementLanguage_lowerDensity p hp.le hp1
  have hdemand :
      p + ε ≤ setBasedUpperDensity gen naturalOrder stream := by
    simpa [p, theoremSixFourFamily, theoremSixFourOrders] using hlarge.2
  linarith

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
