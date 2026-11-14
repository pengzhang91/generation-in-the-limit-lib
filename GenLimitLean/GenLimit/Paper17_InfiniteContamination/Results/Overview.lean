import GenLimit.Paper17_InfiniteContamination.Results.Supporting

/-!
# Paper 17: main-results overview

This module states the formalized main theorems of Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination* (arXiv:2511.07417v1):
Theorems 5.1, 5.4, 6.1, 6.4, 6.5, 6.11, 6.14, 6.18, and 7.8. Each explicit
statement delegates to its canonical proof.

Countable collections are supplied by explicit natural-number enumerations,
matching the indices used by the paper's algorithms. Every nonempty countable
collection admits such an enumeration, with repetitions for finite collections.
The development is semantic and classical; it makes no computability claim.

Theorem 6.14 is stated only for `0 < c < 1`: the source's `c = 1` endpoint
permits every observation to be noise, so its sufficiency proof does not apply.
The element-density transfer constructs the canonical orderings and proves
density invariance under finite changes of the target.
Algorithm 9 removes the observed finite sample from its output to satisfy the
paper's freshness requirement; this finite deletion preserves density.

The supporting set-to-element conversion (Theorem 6.15), Corollary 6.16,
Proposition 7.4, and Lemma 7.5 are retained in `Results.Supporting`.
Main results without complete Lean statements, including the numerical
Corollary 6.20, Theorem 6.21, and Theorems 7.6--7.7 and 7.9--7.11, remain
tracked in `PaperMaps/Paper17_InfiniteContamination.md`.
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

/-- Theorem 6.18: finite-expansion compilation preserves lower and upper
element-density guarantees in the canonical orderings induced by the ambient
natural-number order. Density invariance under finite changes of the target
is proved internally, with no separate measure-compatibility assumption. -/
theorem theorem_6_18
    (O : GenLimit.OracleFamily)
    (gen : Generator ℕ)
    (ρlow ρup : ℝ)
    (hvanilla : ∀ j stream,
      Presents stream
          ((finiteExpansionOracleFamily O).language j) →
        GeneratesElementInLimitOn gen
            ((finiteExpansionOracleFamily O).language j) stream ∧
          ElementDensityGuaranteeOn gen
            (canonicalFamilyOrders (finiteExpansionOracleFamily O) j)
            stream ρlow ρup) :
    ∀ z stream,
      FiniteNoiseFiniteOmissionEnumeration stream (O.language z) →
        GeneratesElementInLimitOn gen (O.language z) stream ∧
          ElementDensityGuaranteeOn gen
            (canonicalFamilyOrders O z) stream ρlow ρup :=
  GenLimit.InfiniteContamination.theorem_6_18_finiteContamination_transfer
    O gen ρlow ρup hvanilla

/-! ## Bounded-displacement generation -/

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
