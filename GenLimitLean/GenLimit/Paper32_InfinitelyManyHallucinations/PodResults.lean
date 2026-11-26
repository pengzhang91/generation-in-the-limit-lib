import GenLimit.Paper32_InfinitelyManyHallucinations.PodGenerator
import GenLimit.Paper32_InfinitelyManyHallucinations.ValidRepetition

/-! # The exploration and precision guarantees for the paper's pod generators -/
namespace GenLimit.InfinitelyManyHallucinations.Pods
open Set KleinbergWei
open scoped Classical

def algorithm7 (C : LanguageFamily) (E : ExplorationSet) (size : ℕ → ℕ)
    (scan : Equiv.Perm ℕ := Equiv.refl ℕ) : Config := ⟨C,E.carrier,true,size,scan⟩

def algorithm6 (C : LanguageFamily) (E : ExplorationSet) (size : ℕ → ℕ)
    (scan : Equiv.Perm ℕ := Equiv.refl ℕ) : Config := ⟨C,E.carrier,false,size,scan⟩

def algorithm2 (C : LanguageFamily) (size : ℕ → ℕ) : Config := ⟨C,∅,false,size,Equiv.refl _⟩

/-- The novelty and both precision clauses of Lemma 4.5 for Algorithm 2.
Every round is safe, and only finitely many early pods can supply an invalid word. -/
theorem algorithm2_precision (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (size : ℕ → ℕ) (positive : ∀ u, 0 < size u) (A : Exhaustion) {z : ℕ}
    (hin : A.limit.Infinite) (hs : A.limit ⊆ C z) :
    let G := (algorithm2 C size).rule.generator
    let g := generatedExhaustion G A
    GeneratorNovel G A ∧ g.IsEnumeration ∧
      lowerMembershipPrecision (C z) g = 1 ∧ lowerTailPrecision (C z) g = 1 := by
  let c := algorithm2 C size
  have safeAt (t : ℕ) : safe c.explore t := by simp [c, algorithm2, safe]
  have hR : (setOf (safe c.explore)).Infinite := Set.infinite_univ.mono (fun n _ => safeAt n)
  let r := c.rule.rounds (rule_causal c hR) (rule_fresh c) A
  obtain ⟨T,hT⟩ := eventual_safe_outputs c hR hi positive A hin hs
  have ev : EventuallyValid (C z) (generatedExhaustion c.rule.generator A) := by
    refine ⟨T+1, ?_⟩
    rintro (_|t) ht x hx
    · omega
    · rw [r.increment, Finset.coe_singleton, Set.mem_singleton_iff] at hx
      exact hx ▸ hT t (by omega) (safeAt t)
  have tail := eventuallyValid_implies_lowerTailPrecision_one ev
  refine ⟨?_, fun t => by rw [r.increment]; simp, appendix_lemma_D_1_of_limit_infinite r.infinite tail, tail⟩
  intro t
  rw [WordRule.generator_apply _ (rule_causal c hR)]
  exact Finset.disjoint_singleton_left.mpr (output_safe_fresh c A (safeAt t) _ _)

private theorem scan_covers {g : Exhaustion} (r : SingletonRounds g) (e : Equiv.Perm ℕ)
    {R : Set ℕ} (inf : R.Infinite) (x : ℕ)
    (step : x ∉ g.limit → ∀ t ∈ R, e.symm (r.word t) ≤ e.symm x) : x ∈ g.limit := by
  by_contra hx
  apply (inf.image (e.symm.injective.comp r.injective).injOn)
  apply (Set.finite_Iic (e.symm x)).subset
  exact fun _ ⟨t,ht,he⟩ => he ▸ step hx t ht

theorem theorem_4_9_algorithm7 (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (E : ExplorationSet) {γ : ℝ} (quota : E.GammaAdmissible γ)
    (size : ℕ → ℕ) (positive : ∀ u, 0 < size u) (scan : Equiv.Perm ℕ) (A : Exhaustion)
    {z : ℕ} (K : OrderedLanguage) (hin : A.limit.Infinite) (hs : A.limit ⊆ C z) :
    let g := generatedExhaustion (algorithm7 C E size scan).rule.generator A
    g.IsEnumeration ∧ GammaNovel γ A g ∧ lowerRecall K g.limit = 1 ∧
      lowerMembershipPrecision (C z) g = 1 := by
  let c := algorithm7 C E size scan
  let g := generatedExhaustion c.rule.generator A
  have hR : (setOf (safe c.explore)).Infinite := safe_infinite E
  let r := c.rule.rounds (rule_causal c hR) (rule_fresh c) A
  obtain ⟨T,hT⟩ := eventual_safe_outputs c hR hi positive A hin hs
  refine ⟨fun t => by rw [r.increment]; simp, r.fractional_novelty A E quota ?_,
    lowerRecall_eq_one_of_target_subset K (fun x _ => ?_), r.precision (T := T) E.prefixRatio_tendsto_zero ?_⟩
  · intro t ht hmem
    exact output_safe_fresh c A ht _ _ (Finset.mem_union_left _ hmem)
  · apply scan_covers r scan (exploration_steps_infinite E) x
    intro hx t ht
    have no : ¬safe c.explore t := fun h => h ht
    change scan.symm (c.output A t _ (g.stage t)) ≤ scan.symm x
    simp only [Config.output,if_neg no]
    exact scan_le scan _ (fun h => hx (g.stage_subset_limit _ h))
  · exact fun t ht he => hT t ht he

theorem algorithm6_precision_complement (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (E : ExplorationSet) (size : ℕ → ℕ) (positive : ∀ u, 0 < size u) (scan : Equiv.Perm ℕ) (A : Exhaustion)
    {z : ℕ} (K : OrderedLanguage) (hin : A.limit.Infinite) (hs : A.limit ⊆ C z) :
    let G := (algorithm6 C E size scan).rule.generator
    let g := generatedExhaustion G A
    GeneratorNovel G A ∧ g.IsEnumeration ∧ lowerMembershipPrecision (C z) g = 1 ∧
      1-upperRecall K A.limit ≤ lowerRecall K g.limit := by
  let c := algorithm6 C E size scan
  let g := generatedExhaustion c.rule.generator A
  have hR : (setOf (safe c.explore)).Infinite := safe_infinite E
  let r := c.rule.rounds (rule_causal c hR) (rule_fresh c) A
  obtain ⟨T,hT⟩ := eventual_safe_outputs c hR hi positive A hin hs
  refine ⟨?_,fun t => by rw [r.increment]; simp,
    r.precision (T := T) E.prefixRatio_tendsto_zero (fun t ht he => hT t ht he),lemma_4_7 K _ _ ?_⟩
  · intro t
    rw [WordRule.generator_apply _ (rule_causal c hR)]
    apply Finset.disjoint_singleton_left.mpr
    by_cases h : safe c.explore t
    · exact output_safe_fresh c A h _ _
    · simp only [Config.rule,Config.output,if_neg h]
      exact scan_fresh _ _
  · intro x hx
    apply scan_covers r scan (exploration_steps_infinite E) x
    intro hg t ht
    have no : ¬safe c.explore t := fun h => h ht
    change scan.symm (c.output A t _ (g.stage t)) ≤ scan.symm x
    simp only [Config.output,if_neg no]
    apply scan_le
    intro h
    rcases Finset.mem_union.mp h with ha|hb
    · exact hx.2 (A.stage_subset_limit _ ha)
    · exact hg (g.stage_subset_limit _ hb)

end GenLimit.InfinitelyManyHallucinations.Pods
