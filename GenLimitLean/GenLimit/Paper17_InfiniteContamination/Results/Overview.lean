import GenLimit.Paper17_InfiniteContamination.AlgorithmFour
import GenLimit.Paper17_InfiniteContamination.AlgorithmFive
import GenLimit.Paper17_InfiniteContamination.AlgorithmSixSeven
import GenLimit.Paper17_InfiniteContamination.AlgorithmEight
import GenLimit.Paper17_InfiniteContamination.AlgorithmNine
import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationNecessity
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper17_InfiniteContamination.FiniteExpansionTransfer
import GenLimit.Paper17_InfiniteContamination.ProperSeparations
import GenLimit.Paper17_InfiniteContamination.SetDensityObstruction

/-!
# Paper 17: main-results overview

This module is the paper's public results facade.  It gives readers one stable
entry point and exposes thin, source-numbered wrappers around the canonical
theorems in the proof modules.  The wrappers do not duplicate proofs.

## Countable-collection interface

The source represents a countable collection as
`L = {L₁, L₂, ...}`, and Algorithms 5, 6, 7, and 9 operate explicitly on
these indices.  The corresponding Lean interface is therefore an indexed
family

```
family : ℕ → GenLimit.Generic.Language α
```

The source also assumes that every language is infinite and notes that its
countable universe may be identified with `ℕ`; the paper-facing Lean
theorems expose those assumptions directly.  Thus the source-level pattern
"for every countable collection `C`, there exists a generator" is represented
by a theorem quantified over an explicit enumeration `family`.

For every nonempty countable collection, classical choice supplies a
surjective enumeration; a finite collection can be enumerated by repeating
members.  Consequently, the indexed-family interface does not materially
weaken the mathematical result.  What most declarations named
`*_enumerated` do not additionally provide is a presentation-free wrapper
that accepts an abstract language class together with a proof of its
countability and constructs the enumeration internally.  This is an API
packaging qualification, not a missing direction of the formalized theorem.

## Fully represented results

* Examples 3.3--3.4:
  `example_3_3_single_noise_proper_separation` and
  `example_3_4_single_omission_proper_separation`.
* Lemma 4.1 and Corollary 4.2:
  `lemma_4_1_prefix_priority_stabilization` and the two
  `corollary_4_2_*` declarations.
* Theorem 5.1 for the explicit indexed-family interface:
  `theorem_5_1_algorithmFour`.
* Theorem 5.4 for an explicitly enumerated countable collection:
  `theorem_5_4_characterization_enumerated`.
* Theorem 6.1 for an explicitly indexed countable collection:
  `theorem_6_1_algorithmFive`, including Algorithm 5's literal finite-history
  generator and fall-back proof.
* Theorem 6.4: `theorem_6_4_arbitrary_constant`, including an explicit
  mechanical-word family of every density `1-c`, its canonical injective
  presentation, and the uniform two-target impossibility argument.
* Lemma 6.8, Lemma 6.9, and Theorem 6.5 for an explicitly indexed countable
  collection: `lemma_6_8_noiseless_setDensity`,
  `lemma_6_9_finiteContamination_sufficiency`, and
  `theorem_6_5_lowerDensity_characterization_enumerated`.
* Proposition 7.4 and Lemma 7.5:
  `proposition_7_4_boundedDisplacement_subset` and
  `lemma_7_5_change_of_density`.
* Theorem 6.11: `theorem_6_11_characterization_enumerated`, including the
  shared sparse presentation used for necessity and Algorithm 6 for
  sufficiency.
* Theorem 6.15, Corollary 6.16, and Claim 6.17:
  `theorem_6_15_algorithmEight`, `corollary_6_16`, and
  `claim_6_17_algorithmEight_rank`.
* Theorem 6.18: `theorem_6_18_finiteContamination_transfer` for the paper's
  finite-expansion reduction with ordering compatibility made explicit.
* Algorithm 9 / Theorem 7.8: `theorem_7_8_algorithmNine`, including the
  literal finite-history priority and stopping rules.

## Partial or specialized representations

* Lemma 4.3's element/set transfer is complete, and Algorithm 2's full coded
  finite-expansion family is reconstructed along the Lemma 6.9 path.
* Theorem 6.4 also retains `theorem_6_4_half_density_instance` as the simple
  even-number specialization of its arbitrary-constant construction.
* Theorem 6.14 is represented by
  `theorem_6_14_characterization_enumerated` for `0 < c < 1`. The source
  states `c ∈ (0,1]`, but at `c = 1` its sufficiency proof infers infinitely
  many target observations from a condition that permits all observations
  to be noise. That endpoint is therefore not claimed.
* Algorithm 8 uses `InheritsAmbientOrder` explicitly because the generic
  `OrderedLanguage` structure otherwise allows unrelated per-target orders.
* Algorithm 9 removes the observed finite sample from its selected
  intersection. The pseudocode omits this subtraction even though the
  paper's Definition 4 requires it; finite-deletion density invariance makes
  the repair semantics-preserving.

Within the paper map's current claim inventory through Theorem 7.8, the only
unresolved advertised case is Theorem 6.14's `c = 1` endpoint. See
`PaperMaps/Paper17_InfiniteContamination.md` for the claim matrix and source
qualifications.
-/

namespace GenLimit.InfiniteContamination.Results

open Filter
open GenLimit.Generic
open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback

/-! ## Generation under infinite contamination -/

/-- Theorem 5.1: every explicitly indexed countable family of infinite
languages is generatable under vanishing noise and arbitrary omissions. -/
theorem theorem_5_1
    (family : ℕ → GenLimit.Generic.Language α)
    (hfamily : ∀ i, (family i).Infinite) :
    ∃ gen : Generator α,
      ∀ target stream,
        VanishingNoiseArbitraryOmissionEnumeration
            stream (family target) →
          GeneratesElementInLimitOn gen (family target) stream :=
  GenLimit.InfiniteContamination.theorem_5_1_algorithmFour
    family hfamily

/-- Theorem 5.4: constant-noise generation is characterized by the paper's
finite-subcollection condition, for an explicit enumeration of the countable
collection. -/
theorem theorem_5_4
    (C : LanguageClass α) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (family : ℕ → GenLimit.Generic.Language α)
    (hfamilyInfinite : ∀ i, (family i).Infinite)
    (hfamilyC : ∀ i, family i ∈ C)
    (hcovers : ∀ L, L ∈ C → ∃ i, family i = L) :
    (∃ gen : Generator α,
        GeneratesUnderConstantNoise gen C c) ↔
      ConstantNoiseGenerationProperty C c :=
  GenLimit.InfiniteContamination.theorem_5_4_characterization_enumerated
    C c hc0 hc1 family hfamilyInfinite hfamilyC hcovers

/-! ## Set-based density -/

/-- Theorem 6.1: Algorithm 5 generates under finite noise and attains
set-based upper density at least `1 - c` under `c`-omissions. -/
theorem theorem_6_1
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = O.language i)
    (z : ℕ) (c : ℝ)
    {stream : Stream ℕ}
    (hinjective : Function.Injective stream)
    (hfiniteNoise : FiniteNoise stream (O.language z))
    (homissions : OmissionsAtMost stream (orders z) c) :
    GeneratesInfiniteSetInLimitOn
        (algorithmFiveGenerator
          (finiteExpansionOracleFamily O).language)
        (orders z).carrier stream ∧
      1 - c ≤ setBasedUpperDensity
        (algorithmFiveGenerator
          (finiteExpansionOracleFamily O).language)
        (orders z) stream :=
  GenLimit.InfiniteContamination.theorem_6_1_algorithmFive
    O orders hcarrier z c hinjective hfiniteNoise homissions

/-- Theorem 6.4: for every `c ∈ (0,1)`, an explicit two-language family
prevents any uniform upper-density guarantee strictly above `1 - c`. -/
theorem theorem_6_4
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ gen : SetGenerator ℕ,
      ¬ GuaranteesSetBasedUpperDensityUnderOmissionsOn gen
        (theoremSixFourFamily (1 - c))
        (theoremSixFourOrders (1 - c) (by linarith) (by linarith))
        c (1 - c + ε) :=
  GenLimit.InfiniteContamination.theorem_6_4_arbitrary_constant
    c hc0 hc1

/-- Theorem 6.5: set-based lower-density generation under finite noise and
finite omissions is equivalent to the pairwise finite-difference density
condition. -/
theorem theorem_6_5
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = O.language i)
    (c : ℝ) :
    (∃ gen : SetGenerator ℕ,
      IsInfiniteSetGenerator gen ∧
        ∀ z,
          GeneratesSetUnderFiniteContaminationOn
              gen (orders z).carrier ∧
            GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn
              gen (orders z) c) ↔
      ∀ i j,
        (O.language i \ O.language j).Finite →
          c ≤ (orders j).lowerDensity (O.language i) :=
  GenLimit.InfiniteContamination.theorem_6_5_lowerDensity_characterization_enumerated
    O orders hcarrier c

/-- Theorem 6.11: the vanishing-noise set-density characterization for an
explicit enumeration of the countable collection. -/
theorem theorem_6_11
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (ρ : ℝ) :
    (∃ gen : SetGenerator ℕ,
        GeneratesSetDensityUnderVanishingNoise gen family orders ρ) ↔
      VanishingNoiseDenseSetCondition family orders ρ :=
  GenLimit.InfiniteContamination.theorem_6_11_characterization_enumerated
    family hfamily orders hcarrier ρ

/-- Theorem 6.14 on the justified range `0 < c < 1`: the constant-noise
set-density characterization for an explicit enumeration.  The printed
`c = 1` endpoint is intentionally not claimed. -/
theorem theorem_6_14
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (c ρ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ : 0 < ρ) :
    (∃ gen : SetGenerator ℕ,
        GeneratesSetDensityUnderConstantNoise
          gen family orders c ρ) ↔
      ConstantNoiseDenseSetCondition family orders c ρ :=
  GenLimit.InfiniteContamination.theorem_6_14_characterization_enumerated
    family hfamily orders hcarrier c ρ hc0 hc1 hρ

/-! ## Element-based density -/

/-- Theorem 6.15: Algorithm 8 converts an eventually `ρ`-dense set
generator into a fresh element generator of lower density at least `ρ / 2`.
The ambient-order compatibility implicit in the paper is explicit here. -/
theorem theorem_6_15
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (target : ℕ) (stream : Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i))
    (hdensity : ∃ N, ∀ t, N ≤ t →
      ρ ≤ (orders target).lowerDensity (setOutput setGen stream t)) :
    GeneratesElementInLimitOn
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ)
        (family target) stream ∧
      ρ / 2 ≤ elementBasedLowerDensity
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ)
        (orders target) stream :=
  GenLimit.InfiniteContamination.theorem_6_15_algorithmEight
    setGen hinfinite family selection orders ρ hρ hinvariant
    hcarrier horder target stream hselected hdensity

/-- Corollary 6.16: every positive error allowance gives an element
generator with lower density at least `(ρ - ε) / 2`. -/
theorem corollary_6_16
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ ε : ℝ) (hε : 0 < ε)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (target : ℕ) (stream : Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i))
    (hsetDensity : ρ ≤
      setBasedLowerDensity setGen (orders target) stream) :
    ∃ gen : Generator ℕ,
      GeneratesElementInLimitOn gen (family target) stream ∧
        (ρ - ε) / 2 ≤
          elementBasedLowerDensity gen (orders target) stream :=
  GenLimit.InfiniteContamination.corollary_6_16
    setGen hinfinite family selection orders ρ ε hε hinvariant
    hcarrier horder target stream hselected hsetDensity

/-- Theorem 6.18: finite-expansion compilation preserves lower and upper
element-density guarantees under the paper's common ambient ordering. -/
theorem theorem_6_18
    (O : GenLimit.OracleFamily)
    (orders expansionOrders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = O.language i)
    (hexpansionCarrier : ∀ j,
      (expansionOrders j).carrier =
        (finiteExpansionOracleFamily O).language j)
    (hmeasure : ∀ j A,
      (expansionOrders j).lowerDensity A =
          (finiteExpansionMeasure orders j).lowerDensity A ∧
        (expansionOrders j).upperDensity A =
          (finiteExpansionMeasure orders j).upperDensity A)
    (gen : Generator ℕ)
    (ρlow ρup : ℝ)
    (hvanilla : ∀ j stream,
      Presents stream
          ((finiteExpansionOracleFamily O).language j) →
        GeneratesElementInLimitOn gen
            ((finiteExpansionOracleFamily O).language j) stream ∧
          ElementDensityGuaranteeOn
            gen (expansionOrders j) stream ρlow ρup) :
    ∀ z stream,
      FiniteNoiseFiniteOmissionEnumeration stream (O.language z) →
        GeneratesElementInLimitOn gen (O.language z) stream ∧
          ElementDensityGuaranteeOn
            gen (orders z) stream ρlow ρup :=
  GenLimit.InfiniteContamination.theorem_6_18_finiteContamination_transfer
    O orders expansionOrders hcarrier hexpansionCarrier hmeasure
    gen ρlow ρup hvanilla

/-! ## Bounded-displacement generation -/

/-- Proposition 7.4: a bounded-displacement guarantee is preserved when the
measured language is replaced by a subset in the same ambient ordering. -/
theorem proposition_7_4
    (K : OrderedLanguage)
    (stream : Stream ℕ)
    {L L' : Set ℕ} {M : ℝ}
    (hsub : L' ⊆ L)
    (hbounded : BoundedDisplacement K stream L M) :
    BoundedDisplacement K stream L' M :=
  GenLimit.InfiniteContamination.proposition_7_4_boundedDisplacement_subset
    K stream hsub hbounded

/-- Lemma 7.5: bounded displacement transfers empirical lower and upper
density to canonical ordered density. -/
theorem lemma_7_5
    (K : OrderedLanguage)
    (stream : Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (M : ℝ) (hM : 0 < M)
    (hbounded : BoundedDisplacement K stream K.carrier M) :
    ((1 / M) *
        liminf (empiricalTargetRatio stream L) atTop ≤
      K.lowerDensity L) ∧
    ((1 / M) *
        limsup (empiricalTargetRatio stream L) atTop ≤
      K.upperDensity L) :=
  GenLimit.InfiniteContamination.lemma_7_5_change_of_density
    K stream L hLK M hM hbounded

/-- Theorem 7.8: Algorithm 9 generates under vanishing noise and
`M`-bounded displacement with eventual set-based lower density
`(1 - ε) / M`. -/
theorem theorem_7_8
    (family : ℕ → Set ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (ε M : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hM : 0 < M)
    (target : ℕ) (stream : Stream ℕ)
    (hinjective : Function.Injective stream)
    (hnoise : VanishingNoise stream (family target))
    (hbounded : BoundedDisplacement
      (orders target) stream (orders target).carrier M) :
    GeneratesInfiniteSetInLimitOn
        (algorithmNineSetGenerator family orders ε M)
        (family target) stream ∧
      ∃ T, ∀ t, T ≤ t →
        (1 - ε) / M ≤
          (orders target).lowerDensity
            (setOutput
              (algorithmNineSetGenerator family orders ε M) stream t) :=
  GenLimit.InfiniteContamination.theorem_7_8_algorithmNine
    family hfamily orders hcarrier ε M hε0 hε1 hM target stream
    hinjective hnoise hbounded

end GenLimit.InfiniteContamination.Results
