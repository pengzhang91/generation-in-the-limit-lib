import GenLimit.Paper32_InfinitelyManyHallucinations.Results.Supporting
import GenLimit.Paper32_InfinitelyManyHallucinations.StrictExploration
import GenLimit.Paper32_InfinitelyManyHallucinations.PodCounterexample
import GenLimit.Paper32_InfinitelyManyHallucinations.ValidRepetition

/-! # Generating in the Limit with Infinitely Many Hallucinations

The existence statements for 3.5 and 4.8 use alternative constructions.
Algorithm 6 fails the α/3 clause of 4.8 on the full-input counterexample.
Theorem 4.9 verifies Algorithm 7 on its compressed consistency chains.
For the strict-novelty density bounds, target enumerations respect a common
ambient order. The generator receives the finite input history at each turn.
-/

namespace GenLimit.InfinitelyManyHallucinations.Results

open Set KleinbergWei KleinbergWei.DensityMeasures.OrderedFocus
open KleinbergWei.PartialEnumeration.Sharpness (natural)

theorem theorem_2_1
    (f : ℕ → ℕ) (L : Language) (guess : Exhaustion)
    (hguessInfinite : guess.limit.Infinite)
    (hguessBounded : guess.BoundedBy f) :
    bestBoundedLowerPrecision f L guess =
      lowerMembershipPrecision L guess :=
  GenLimit.InfinitelyManyHallucinations.theorem_2_1 f L guess hguessInfinite hguessBounded

theorem theorem_3_5 (O : ℕ → OrderedLanguage) (hc : Compatible O) :
    ∃ G : BatchGenerator, ∀ (A : Exhaustion) (z : ℕ),
      A.IsSingleStep → A.limit.Infinite → A.limit ⊆ (O z).carrier →
      let g := generatedExhaustion G A
      GeneratorNovel G A ∧ g.IsSingleStep ∧ g.limit.Infinite ∧
        lowerTailPrecision (O z).carrier g = 1 ∧
        lowerMembershipPrecision (O z).carrier g = 1 ∧
        lowerRecall (O z) A.limit / 2 ≤ lowerRecall (O z) g.limit :=
  singleStep_half_recall O hc

/-- The adversary presents the entire natural-order target, whose input
recall is one. Even upper output recall is at most one half. -/
theorem theorem_3_6 (G : BatchGenerator) :
    ∃ A : Exhaustion, A.IsSingleStep ∧ A.limit = Set.univ ∧
      (GeneratorNovel G A → (generatedExhaustion G A).IsSingleStep →
        upperRecall natural (generatedExhaustion G A).limit ≤ lowerRecall natural A.limit / 2) := by
  obtain ⟨A, hA, hfull, cap⟩ := BatchedRace.batched_full_upper 1 (by decide) G
  refine ⟨A, hA, hfull, fun hn hs => ?_⟩
  have one : lowerRecall natural A.limit = 1 :=
    lowerRecall_eq_one_of_target_subset natural (by rw [hfull]; exact Set.subset_univ _)
  rw [one]
  simpa [upperRecall] using cap hn hs

theorem theorem_4_3
    (target : GenLimit.KleinbergWei.OrderedLanguage)
    (L : Language) (f : ℕ → ℕ) :
    ∃ G : BatchGenerator, ∀ adversary : Exhaustion,
      adversary.limit.Infinite →
      adversary.limit ⊆ L →
      adversary.BoundedBy f →
      let guess := generatedExhaustion G adversary
      guess.BoundedBy f ∧
        lowerRecall target guess.limit = 1 ∧
        lowerMembershipPrecision L guess = 1 :=
  GenLimit.InfinitelyManyHallucinations.theorem_4_3 target L f

/-- The recall and precision guarantee of 4.8, achieved by a generator
using sparse replacement of safe proposals. -/
theorem theorem_4_8_existence (O : ℕ → OrderedLanguage) (hc : Compatible O) :
    ∃ G : BatchGenerator, ∀ (A : Exhaustion) (z : ℕ), A.IsSingleStep → A.limit.Infinite →
      A.limit ⊆ (O z).carrier →
      let g := generatedExhaustion G A
      GeneratorNovel G A ∧ g.IsEnumeration ∧ lowerMembershipPrecision (O z).carrier g = 1 ∧
        max (1-upperRecall (O z) A.limit) (lowerRecall (O z) A.limit / 3) ≤
          lowerRecall (O z) g.limit := by
  obtain ⟨G, hG⟩ := strict_sparse_recall O hc
  refine ⟨G, fun A z hs hi hA => ?_⟩
  obtain ⟨hn, he, hp, hr⟩ := hG A z hs hi hA
  refine ⟨hn, he, hp, (max_le_max_left _ ?_).trans hr⟩
  linarith [lowerRecall_nonneg (O z) A.limit]

/-- On the natural target, Algorithm 6 has zero lower recall even though the
input has recall one. This refutes the algorithm attribution in Theorem 4.8. -/
theorem theorem_4_8_counterexample (E : ExplorationSet) :
    let A := Pods.Counterexample.input
    let c := Pods.algorithm6 Pods.Counterexample.family E (fun u => u+1)
    A.IsSingleStep ∧ A.limit = univ ∧ lowerRecall natural A.limit = 1 ∧
      lowerRecall natural (generatedExhaustion c.rule.generator A).limit = 0 :=
  Pods.Counterexample.algorithm6_zero_recall E

/-- The finite-prefix novelty, recall and precision guarantees of Algorithm 7.
Any positive pod sizes suffice, including the source's growing sizes. -/
theorem theorem_4_9 (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (E : ExplorationSet) {γ : ℝ} (quota : E.GammaAdmissible γ)
    (size : ℕ → ℕ) (positive : ∀ u, 0 < size u) (scan : Equiv.Perm ℕ) (A : Exhaustion) {z : ℕ}
    (K : OrderedLanguage) (hin : A.limit.Infinite) (hs : A.limit ⊆ C z) :
    let g := generatedExhaustion (Pods.algorithm7 C E size scan).rule.generator A
    g.IsEnumeration ∧ GammaNovel γ A g ∧ lowerRecall K g.limit = 1 ∧
      lowerMembershipPrecision (C z) g = 1 :=
  Pods.theorem_4_9_algorithm7 C hi E quota size positive scan A K hin hs

/-- Theorem E.1. Without a novelty requirement, copying preserves the input batch
bound and recall guarantee and attains perfect membership and tail precision.
For each `α ∈ [0, 1]`, one single-step input witnesses tightness. Every generator
with a constant batch bound and perfect tail precision on the smaller target
has lower recall at most `α` on the full natural-number target. -/
theorem theorem_E_1 (α : ℝ) :
    (∀ (target : OrderedLanguage) (L : Language) (f : ℕ → ℕ) (A : Exhaustion),
      A.limit.Infinite → A.limit ⊆ L → A.BoundedBy f → α ≤ lowerRecall target A.limit →
      let g := generatedExhaustion parrotGenerator A
      g.BoundedBy f ∧ α ≤ lowerRecall target g.limit ∧
        lowerMembershipPrecision L g = 1 ∧ lowerTailPrecision L g = 1) ∧
    (α ∈ Icc 0 1 → ∃ A : Exhaustion,
      A.IsSingleStep ∧ A.limit.Infinite ∧ lowerRecall natural A.limit = α ∧
      ∀ (G : BatchGenerator) (c : ℕ),
        let g := generatedExhaustion G A
        g.BoundedBy (fun _ => c) → lowerTailPrecision A.limit g = 1 →
          lowerRecall natural g.limit ≤ α) :=
  ⟨fun target L f => valid_generation_without_novelty target L f α,
    theorem_E_1_I_3_upper⟩

/-- Theorem I.3. Repetition rounds recover all the revealed words. -/
theorem theorem_I_3 (C : LanguageFamily) {γ : ℝ} (hγ : γ < 1) :
    ∃ G : BatchGenerator, ∀ (A : Exhaustion) (z : ℕ) (K : OrderedLanguage),
      K.carrier = C z → A.IsSingleStep → A.limit.Infinite → A.limit ⊆ C z →
      let g := generatedExhaustion G A
      g.IsEnumeration ∧ GammaNovel γ A g ∧ lowerRecall K A.limit ≤ lowerRecall K g.limit ∧
        lowerMembershipPrecision (C z) g = 1 ∧ lowerTailPrecision (C z) g = 1 := by
  obtain ⟨G, run⟩ := perfect_tail_fractional C hγ
  refine ⟨G, fun A z K _ hs hi hA => ?_⟩
  obtain ⟨he, hn, cover, hp, ht⟩ := run A z hs hi hA
  exact ⟨he, hn, K.lowerDensity_mono cover, hp, ht⟩

/-- Corollary I.2, for full presentations. -/
theorem corollary_I_2 (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (E : ExplorationSet) {γ : ℝ} (quota : E.GammaAdmissible γ)
    (size : ℕ → ℕ) (positive : ∀ u, 0 < size u) (scan : Equiv.Perm ℕ) (A : Exhaustion) {z : ℕ}
    (K : OrderedLanguage) (hK : K.carrier = C z) (full : A.limit = C z) :
    let g := generatedExhaustion (Pods.algorithm7 C E size scan).rule.generator A
    g.IsEnumeration ∧ GammaNovel γ A g ∧ lowerRecall K g.limit = 1 ∧
      lowerMembershipPrecision K.carrier g = 1 := by
  rw [hK]
  exact theorem_4_9 C hi E quota size positive scan A K (full ▸ hi z) full.subset

/-- Corollary I.4, with the perfect-tail requirement on a full presentation. -/
theorem corollary_I_4 (C : LanguageFamily) {γ : ℝ} (hγ : γ < 1) :
    ∃ G : BatchGenerator, ∀ (A : Exhaustion) (z : ℕ) (K : OrderedLanguage),
      K.carrier = C z → A.IsSingleStep → A.limit = C z →
      let g := generatedExhaustion G A
      g.IsEnumeration ∧ GammaNovel γ A g ∧ lowerRecall K g.limit = 1 ∧
        lowerMembershipPrecision (C z) g = 1 ∧ lowerTailPrecision (C z) g = 1 := by
  obtain ⟨G, run⟩ := perfect_tail_fractional C hγ
  refine ⟨G, fun A z K hK hs hA => ?_⟩
  have hfull : A.limit = K.carrier := hA.trans hK.symm
  obtain ⟨he, hn, cover, hp, ht⟩ := run A z hs (hfull ▸ (K.range_enumeration ▸ Set.infinite_range_of_injective K.enumeration_injective)) hA.subset
  exact ⟨he, hn, lowerRecall_eq_one_of_target_subset K (hfull ▸ cover), hp, ht⟩

end GenLimit.InfinitelyManyHallucinations.Results
