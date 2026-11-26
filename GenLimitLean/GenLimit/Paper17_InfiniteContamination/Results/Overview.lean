import GenLimit.Paper17_InfiniteContamination.MembershipGeneration
import GenLimit.Paper17_InfiniteContamination.BoundedIdentification
import GenLimit.Paper17_InfiniteContamination.BoundedObstruction
import GenLimit.Paper17_InfiniteContamination.DisplacementEndpoint
import GenLimit.Paper17_InfiniteContamination.FiniteClassThreshold
import GenLimit.Paper17_InfiniteContamination.Results.Supporting
import GenLimit.Paper17_InfiniteContamination.NumericalDensity
import GenLimit.Paper17_InfiniteContamination.ElementObstruction

/-!
# Paper 17: main-results overview

Main results of Mehrotra–Velegkas–Yu–Zhou for explicitly indexed language
families on natural numbers. Corollary 4.5 certifies a terminating membership
query program. Density bounds use the common ambient ordering. Theorem 6.14
includes the endpoint by a separate identity-stream argument. For Theorem
7.7 the printed displacement constant makes the adversary class empty. The
corrected obstruction also holds at displacement one. Theorems 6.15–6.16
are imported from the set-to-element conversion in `Results.Supporting`.
-/

namespace GenLimit.InfiniteContamination.Results

open Filter
open GenLimit.Generic
open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback

/-- Corollaries 1.2 and 4.5. One fixed membership-query algorithm tolerates finite noise and omissions. -/
theorem corollary_4_5 (O : OracleFamily) :
    ∃ h : boundedMembershipProgram.Terminates (GenLimit.HallucinationModeCollapse.generationOracle (membershipExpansion O)),
      let run := boundedMembershipProgram.run (GenLimit.HallucinationModeCollapse.generationOracle (membershipExpansion O)) h
      (∀ z s, FiniteNoiseFiniteOmissionEnumeration s (O.language z) →
        GeneratesElementInLimitOn (replayGenerator run) (O.language z) s) ∧
      (Computable₂ O.query → Computable (membershipReplay run)) :=
  GenLimit.InfiniteContamination.finiteContamination_membership_machine O

/-! ## Generation under infinite contamination -/

/-- Theorem 5.1: every explicitly indexed countable family of infinite
languages is generatable under vanishing noise and arbitrary omissions. -/
theorem theorem_5_1
    (family : Generic.LanguageFamily α)
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
    (family : Generic.LanguageFamily α)
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
    (family : LanguageFamily)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (ρ : ℝ) :
    (∃ gen : SetGenerator ℕ,
        GeneratesSetDensityUnderVanishingNoise gen family orders ρ) ↔
      VanishingNoiseDenseSetCondition family orders ρ :=
  GenLimit.InfiniteContamination.theorem_6_11_characterization_enumerated
    family hfamily orders hcarrier ρ

/-- Theorem 6.14, including the full-noise endpoint. -/
theorem theorem_6_14_including_one
    (family : LanguageFamily)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (c ρ : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hρ : 0 < ρ) :
    (∃ gen : SetGenerator ℕ,
        GeneratesSetDensityUnderConstantNoise
          gen family orders c ρ) ↔
      ConstantNoiseDenseSetCondition family orders c ρ :=
  GenLimit.InfiniteContamination.theorem_6_14_including_one
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

/-- Theorem 6.19. Both noiseless element-density bounds hold for the same generator. -/
theorem theorem_6_19 (O : GenLimit.OracleFamily) :
    ∃ gen : Generator ℕ, ∀ j s, GenLimit.Generic.Presents s (O.language j) →
      GeneratesElementInLimitOn gen (O.language j) s ∧
      ElementDensityGuaranteeOn gen (canonicalFamilyOrders O j) s (1/8) (1/2) :=
  noiseless_numerical_density O

/-- Corollary 6.20. Finite noise and omissions preserve the numerical bounds. -/
theorem corollary_6_20 (O : GenLimit.OracleFamily) :
    ∃ gen : Generator ℕ, ∀ j s, FiniteNoiseFiniteOmissionEnumeration s (O.language j) →
      GeneratesElementInLimitOn gen (O.language j) s ∧
      ElementDensityGuaranteeOn gen (canonicalFamilyOrders O j) s (1/8) (1/2) :=
  finite_contamination_numerical_density O

/-- Theorem 6.21. A stream with vanishing noise and no omissions for either target
forces zero upper density on the larger target if validity holds on the smaller one. -/
theorem theorem_6_21 :
    ∃ (small : Set ℕ) (large : OrderedLanguage) (s : Stream ℕ),
      small.Infinite ∧ small ⊂ large.carrier ∧
      VanishingNoiseEnumeration s small ∧ VanishingNoiseEnumeration s large.carrier ∧
      ∀ gen, GeneratesElementInLimitOn gen small s →
        elementBasedUpperDensity gen large s = 0 :=
  exists_zero_element_upperDensity

/-! ## Bounded-displacement generation -/

/-- Theorem 7.6. Exact bounded presentations still defeat identification. -/
theorem theorem_7_6 (M : ℝ) (hM : 1 < M) :
    ¬∃ A : List ℕ → Set ℕ, ∀ i s, Function.Injective s →
      Generic.Presents s (puncturedFamilyOrders i).carrier →
      BoundedDisplacement (puncturedFamilyOrders i) s (puncturedFamilyOrders i).carrier M →
      ∃ T, ∀ t ≥ T, A (textPrefix s t) = (puncturedFamilyOrders i).carrier :=
  GenLimit.InfiniteContamination.no_bounded_identifier M hM

/-- Theorem 7.7 as printed admits no adversarial stream for any k ≥ 2. -/
theorem theorem_7_7_printed_impossible (k : ℕ) (hk : 2 ≤ k)
    (K : OrderedLanguage) (s : Generic.Stream ℕ) (hinj : Function.Injective s)
    (hnoise : ConstantNoise s K.carrier (1 / k)) :
    ¬ BoundedDisplacement K s K.carrier (1 / k) :=
  GenLimit.InfiniteContamination.theorem_7_7_no_admissible_stream k hk K s hinj hnoise

/-- The corrected Theorem 7.7 holds for every displacement factor at least one. -/
theorem theorem_7_7_corrected (k : ℕ) (hk : 2 ≤ k) (M : ℝ) (hM : 1 ≤ M) :
    ∃ K : Fin k → OrderedLanguage, Function.Injective (fun i ↦ (K i).carrier) ∧
      ∃ s : Generic.Stream ℕ, (∀ i, ConstantNoiseEnumeration s (K i).carrier (1/k) ∧
        BoundedDisplacement (K i) s (K i).carrier M) ∧
        ¬∃ gen : Generic.Generator ℕ, ∀ i, GeneratesElementInLimitOn gen (K i).carrier s :=
  GenLimit.InfiniteContamination.finiteClass_bounded_obstruction k hk M hM

/-- Theorem 7.8: Algorithm 9 generates under vanishing noise and
`M`-bounded displacement with eventual set-based lower density
`(1 - ε) / M`. -/
theorem theorem_7_8
    (family : LanguageFamily)
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

/-- Theorem 7.9. The smaller target bounds set density on the larger target. -/
theorem theorem_7_9 (M : ℝ) (hM : 1 ≤ M) :
    ∃ (K : OrderedLanguage) (s : Generic.Stream ℕ),
      K.carrier ⊂ naturalOrder.carrier ∧ VanishingNoiseEnumeration s K.carrier ∧
      VanishingNoiseEnumeration s naturalOrder.carrier ∧ BoundedDisplacement K s K.carrier M ∧
      BoundedDisplacement naturalOrder s naturalOrder.carrier M ∧
      ∀ gen, GeneratesSetInLimitOn gen K.carrier s →
        setBasedUpperDensity gen naturalOrder s ≤ 1/M := by
  obtain ⟨K,s,hsub,hK,hN,hbK,hbN,hset,hel⟩ := bounded_obstruction_both M hM
  exact ⟨K,s,hsub,hK,hN,hbK,hbN,hset⟩

/-- Theorem 7.10. Conversion to element generation halves the set-density guarantee. -/
theorem theorem_7_10
    (family : LanguageFamily) (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage) (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (ε M : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hM : 0 < M) :
    ∃ gen : Generic.Generator ℕ, ∀ target stream, Function.Injective stream →
      VanishingNoise stream (family target) →
      BoundedDisplacement (orders target) stream (orders target).carrier M →
      GeneratesElementInLimitOn gen (family target) stream ∧
        (1 - ε) / (2 * M) ≤ elementBasedLowerDensity gen (orders target) stream :=
  boundedDisplacement_elementDensity family hfamily orders hcarrier horder ε M hε0 hε1 hM

/-- Theorem 7.11. The smaller target bounds element density on the larger target. -/
theorem theorem_7_11 (M : ℝ) (hM : 1 ≤ M) :
    ∃ (K : OrderedLanguage) (s : Generic.Stream ℕ),
      K.carrier ⊂ naturalOrder.carrier ∧ VanishingNoiseEnumeration s K.carrier ∧
      VanishingNoiseEnumeration s naturalOrder.carrier ∧ BoundedDisplacement K s K.carrier M ∧
      BoundedDisplacement naturalOrder s naturalOrder.carrier M ∧
      ∀ gen, GeneratesElementInLimitOn gen K.carrier s →
        elementBasedUpperDensity gen naturalOrder s ≤ 1/M := by
  obtain ⟨K,s,hsub,hK,hN,hbK,hbN,hset,hel⟩ := bounded_obstruction_both M hM
  exact ⟨K,s,hsub,hK,hN,hbK,hbN,hel⟩

/-- Theorem B.2. The priority-free Algorithm 10 tolerates vanishing noise. -/
theorem theorem_B_2 (family : LanguageFamily) (z : ℕ) (s : Generic.Stream ℕ)
    (hinj : Function.Injective s) (hnoise : VanishingNoise s (family z)) :
    GeneratesElementInLimitOn (activeCoreGenerator (algorithmTenCore family)) (family z) s :=
  GenLimit.InfiniteContamination.algorithmTen_generates family z s hinj hnoise

/-- Theorem B.3. Noise rate 1/k is the sharp threshold for k distinct languages. -/
theorem theorem_B_3 (k : ℕ) (hk : 2 ≤ k) (c : ℝ) :
    (1/k ≤ c → ∃ f : Fin k → Set ℕ, Function.Injective f ∧ (∀ i, (f i).Infinite) ∧
      ∃ s : Generic.Stream ℕ, (∀ i, ConstantNoiseEnumeration s (f i) c) ∧
        ¬∃ g : Generic.Generator ℕ, ∀ i, GeneratesElementInLimitOn g (f i) s) ∧
    (c < 1/k → ∀ f : Fin k → Set ℕ, ∃ g : Generic.Generator ℕ,
      ∀ i s, Function.Injective s → ConstantNoise s (f i) c → GeneratesElementInLimitOn g (f i) s) :=
  GenLimit.InfiniteContamination.finiteClass_threshold k hk c

/-- Theorem B.4. One generator works at every limiting noise rate below 1/k. -/
theorem theorem_B_4 (k : ℕ) (hk : 0 < k) (f : Fin k → Set ℕ) :
    ∃ gen : Generic.Generator ℕ, ∀ z s, Function.Injective s →
      limsup (empiricalNoiseRate s (f z)) atTop < 1/k →
      GeneratesElementInLimitOn gen (f z) s :=
  GenLimit.InfiniteContamination.finiteClass_limsup k hk f

end GenLimit.InfiniteContamination.Results
