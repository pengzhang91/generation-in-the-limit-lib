import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineBreadthConstruction

/-!
# Online Theorems 3.5, 3.7, and 3.9

The source-facing negative results retain pointwise decidable MOP and the
same semantic/Condition-2 identifiability boundary as Theorems 3.1, 3.6, and
3.8. They follow from stronger support-semantic obstructions, so no uniform
support decider or effective training is extracted from pointwise MOP.

Theorem 3.5's positive branch uses certified membership/tell-tale training
and an actual PMF sampler. Ordinary pointwise MOP requires computable family
membership; ordinary uniform sampling additionally requires computable
training. Separate effective biconditionals and impossibility corollaries
use the existing P00A EffectiveInferrable interface and uniform MOP explicitly.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit GenLimit.Support

theorem theorem_3_7 (C : Generic.LanguageFamily ℕ) (hnot : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (hstable : StatisticalStable G C) (_hMOP : DecidableMOP G) :
    ¬UnambiguousInLimit (statisticalSupportView G) C := by
  intro hU
  exact hnot (stable_unambiguousInLimit_implies_identifiableInLimit
    (hasDistinctLanguages_of_not_identifiable hnot) hstable hU)

theorem theorem_3_9 (C : Generic.LanguageFamily ℕ) (hnot : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (hstable : StatisticalStable G C) (_hMOP : DecidableMOP G) :
    ¬ApproximateBreadthInLimit (statisticalSupportView G) C := by
  intro hA
  exact hnot (stable_approximateBreadthInLimit_implies_identifiableInLimit hstable hA)

/-- Full online breadth separation in the explicit infinite-language oracle
model. The ordinary-MOP biconditionals state their computable-membership
hypothesis, rather than asserting decidability of an arbitrary oracle. -/
theorem theorem_3_5 (O : OracleFamily) :
    (¬IdentifiableInLimit O.language → ∀ G : StatisticalGenerator, DecidableMOP G →
      ¬FreshBreadthInLimit (statisticalSupportView G) O.language ∧
      ¬RepeatingBreadthInLimit (statisticalSupportView G) O.language) ∧
    (IdentifiableInLimit O.language → CertifiedOnlineBreadthPositiveBranch O) ∧
    (Computable₂ O.query →
      (IdentifiableInLimit O.language ↔ ∃ G : StatisticalGenerator, DecidableMOP G ∧
        FreshBreadthInLimit (statisticalSupportView G) O.language) ∧
      (IdentifiableInLimit O.language ↔ ∃ G : StatisticalGenerator, DecidableMOP G ∧
        RepeatingBreadthInLimit (statisticalSupportView G) O.language)) := by
  refine ⟨?_, certifiedOnlineBreadth_of_identifiable O, ?_⟩
  · intro hnot G _hMOP
    exact ⟨fun hF => hnot (freshBreadthInLimit_implies_identifiableInLimit hF),
      fun hR => hnot (repeatingBreadthInLimit_implies_identifiableInLimit hR)⟩
  · intro hO
    constructor
    · constructor
      · intro hID
        obtain ⟨emit, _hTell, hF, _hR, _hOF, _hOR, hordinary, _hcomp⟩ :=
          certifiedOnlineBreadth_of_identifiable O hID
        exact ⟨_, (hordinary hO).1, hF⟩
      · rintro ⟨G, _, hF⟩
        exact freshBreadthInLimit_implies_identifiableInLimit hF
    · constructor
      · intro hID
        obtain ⟨emit, _hTell, _hF, hR, _hOF, _hOR, hordinary, _hcomp⟩ :=
          certifiedOnlineBreadth_of_identifiable O hID
        exact ⟨_, (hordinary hO).2, hR⟩
      · rintro ⟨G, _, hR⟩
        exact repeatingBreadthInLimit_implies_identifiableInLimit hR

/-- Effective Theorem 3.5 with fresh output. Both training and support
membership are uniform ordinary computations. -/
theorem effective_identification_iff_fresh_breadth (F : GenLimit.Angluin.EffectiveIndexedFamily)
    (hinf : ∀ i, (F.language i).Infinite) :
    GenLimit.Angluin.EffectiveInferrable F ↔
      ∃ G : StatisticalGenerator, HasComputableSampler G ∧ UniformDecidableMOP G ∧
        FreshBreadthInLimit (statisticalSupportView G) F.language := by
  let O : OracleFamily := ⟨F.language, hinf, F.membership, F.membership_spec⟩
  constructor
  · rintro ⟨A, hcomp, hA⟩
    exact ⟨identifiedBreadth O A, identifiedBreadth_computableSampler O F.membership_computable A hcomp,
      identifiedBreadth_uniformMOP O F.membership_computable A hcomp, identifiedBreadth_online O A hA⟩
  · rintro ⟨G, _hsampler, ⟨Q, hQ, hspec⟩, hG⟩
    exact ⟨breadthIdentifier (familyMembership O) Q,
      breadthIdentifier_computable (familyMembership O) F.membership_computable Q hQ,
      breadthIdentifier_identifies_of_fresh (familyMembership O) G Q hspec hG⟩

/-- The ordinary effective biconditional also holds with repetitions. -/
theorem effective_identification_iff_repeating_breadth (F : GenLimit.Angluin.EffectiveIndexedFamily)
    (hinf : ∀ i, (F.language i).Infinite) :
    GenLimit.Angluin.EffectiveInferrable F ↔
      ∃ G : StatisticalGenerator, HasComputableSampler G ∧ UniformDecidableMOP G ∧
        RepeatingBreadthInLimit (statisticalSupportView G) F.language := by
  let O : OracleFamily := ⟨F.language, hinf, F.membership, F.membership_spec⟩
  constructor
  · rintro ⟨A, hcomp, hA⟩
    exact ⟨identifiedRepeatingBreadth O A,
      identifiedRepeatingBreadth_computableSampler O F.membership_computable A hcomp,
      identifiedRepeatingBreadth_uniformMOP O F.membership_computable A hcomp,
      identifiedRepeatingBreadth_online O A hA⟩
  · rintro ⟨G, _hsampler, ⟨Q, hQ, hspec⟩, hG⟩
    exact ⟨breadthIdentifier (familyMembership O) Q,
      breadthIdentifier_computable (familyMembership O) F.membership_computable Q hQ,
      breadthIdentifier_identifies_of_repeating (familyMembership O) G Q hspec hG⟩

theorem effectiveInferrable_of_no_distinctLanguages (F : GenLimit.Angluin.EffectiveIndexedFamily)
    (hC : ¬HasDistinctLanguages F.language) : GenLimit.Angluin.EffectiveInferrable F := by
  refine ⟨fun _ => 0, Computable.const 0, ?_⟩
  intro i stream _hP
  refine ⟨0, ?_, 0, fun _ _ => rfl⟩
  by_contra hne
  exact hC ⟨0, i, hne⟩

/-- Under uniform MOP, the reduction also contradicts failure of ordinary
effective identification, a different hypothesis from semantic non-ID. -/
theorem effective_nonidentifiable_no_stable_unambiguous (F : GenLimit.Angluin.EffectiveIndexedFamily)
    (hnot : ¬GenLimit.Angluin.EffectiveInferrable F) (G : StatisticalGenerator)
    (hMOP : UniformDecidableMOP G) (hstable : StatisticalStable G F.language) :
    ¬UnambiguousInLimit (statisticalSupportView G) F.language := by
  intro hU
  have hdist : HasDistinctLanguages F.language := by
    by_contra hn
    exact hnot (effectiveInferrable_of_no_distinctLanguages F hn)
  obtain ⟨Q, hQ, hspec⟩ := hMOP
  let O : MembershipOracle F.language := ⟨F.membership, fun {i x} => F.membership_spec i x⟩
  exact hnot ⟨boundedUnambiguousIdentifier O Q,
    boundedUnambiguousIdentifier_computable O F.membership_computable Q hQ,
    boundedUnambiguousIdentifier_identifies O G Q hspec hdist hstable hU⟩

theorem effective_nonidentifiable_no_stable_approximate (F : GenLimit.Angluin.EffectiveIndexedFamily)
    (hnot : ¬GenLimit.Angluin.EffectiveInferrable F) (G : StatisticalGenerator)
    (hMOP : UniformDecidableMOP G) (hstable : StatisticalStable G F.language) :
    ¬ApproximateBreadthInLimit (statisticalSupportView G) F.language := by
  intro hA
  obtain ⟨Q, hQ, hspec⟩ := hMOP
  let O : MembershipOracle F.language := ⟨F.membership, fun {i x} => F.membership_spec i x⟩
  exact hnot ⟨breadthIdentifier O Q,
    breadthIdentifier_computable O F.membership_computable Q hQ,
    breadthIdentifier_identifies_of_approximate O G Q hspec hstable hA⟩

end GenLimit.HallucinationModeCollapse
