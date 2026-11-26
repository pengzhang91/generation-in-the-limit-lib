import GenLimit.Paper32_InfinitelyManyHallucinations.ScheduledExploration
import GenLimit.Paper32_InfinitelyManyHallucinations.SingleStepSafe
import GenLimit.Paper32_InfinitelyManyHallucinations.SparseReplacement

/-! # Strict novelty with sparse exploration

Simulate the single-step safe generator before deciding whether to explore.
The chosen exploration times displace a zero-density set of its proposals in
every target order. Unrevealed words are recovered by least-unused scanning.
This gives the numerical conclusion of Theorem 4.8 by an independent algorithm.
-/

namespace GenLimit.InfinitelyManyHallucinations
open Set Filter KleinbergWei KleinbergWei.DensityMeasures.OrderedFocus
open scoped Classical Topology

private noncomputable def visible (O : ℕ → OrderedLanguage) (A : Exhaustion) (t : ℕ) :=
  if (A.stage (t+1)).Nonempty then safeProposal O A t else 0

private theorem visible_prefix {O : ℕ → OrderedLanguage} {A B : Exhaustion} {t : ℕ}
    (h : ∀ i ≤ t+1, A.stage i = B.stage i) :
    ∀ j ≤ t, visible O A j = visible O B j := by
  intro j hj
  have hp : ∀ i ≤ j+1, A.stage i = B.stage i := fun i hi => h i (by omega)
  by_cases hn : (A.stage (j+1)).Nonempty
  · simp only [visible, ← hp _ le_rfl, if_pos hn, safeProposal_prefix hp hn]
  · simp [visible, ← hp _ le_rfl, hn]

private noncomputable def strictWord (O : ℕ → OrderedLanguage) : WordRule :=
  fun A t prev =>
    let w := visible O A
    let used := A.stage (t+1) ∪ prev
    if SparseReplacement.Marked O w t then PartialEnumeration.Sharpness.firstMissing used
    else if w t ∈ used then safeChoice (fun i => (O i).carrier) A t prev else w t

private theorem strictWord_causal (O : ℕ → OrderedLanguage) : (strictWord O).Causal := by
  intro A B t hp prev
  have hv := visible_prefix (O := O) hp
  simp only [strictWord, SparseReplacement.marked_prefix O hv, hv _ le_rfl,
    hp _ le_rfl, safeChoice_prefix hp]

private theorem strictWord_fresh (O : ℕ → OrderedLanguage) (A : Exhaustion) (t : ℕ)
    (prev : Finset ℕ) : strictWord O A t prev ∉ A.stage (t+1) ∪ prev := by
  dsimp only [strictWord]
  split
  · exact PartialEnumeration.Sharpness.firstMissing_notMem _
  · split
    · exact safeChoice_fresh _ _ _ _
    · assumption

/-- One strictly novel generator on the P32 batch interface, with perfect
precision and both complement recall and the half-recall safe guarantee. -/
theorem strict_sparse_recall (O : ℕ → OrderedLanguage) (hc : Compatible O) :
    ∃ G : BatchGenerator, ∀ (A : Exhaustion) (z : ℕ), A.IsSingleStep → A.limit.Infinite →
      A.limit ⊆ (O z).carrier →
      let g := generatedExhaustion G A
      GeneratorNovel G A ∧ g.IsEnumeration ∧ lowerMembershipPrecision (O z).carrier g = 1 ∧
        max (1-upperRecall (O z) A.limit) (lowerRecall (O z) A.limit / 2) ≤
          lowerRecall (O z) g.limit := by
  let p := strictWord O
  refine ⟨p.generator, ?_⟩
  intro A z single hi hs
  let g := generatedExhaustion p.generator A
  let r := p.rounds (strictWord_causal O)
    (fun a t prev h => strictWord_fresh O a t prev (Finset.mem_union_right _ h)) A
  let w := visible O A
  let marked := SparseReplacement.Marked O w
  have word (t) : r.word t = strictWord O A t (g.stage t) := rfl
  have hp := Exhaustion.inputWord_presents single hi.nonempty
  obtain ⟨⟨V,hV⟩, density⟩ := Bridge.Paper39ToPaper15.theorem_1_6 O hc hp hi hs le_rfl
  obtain ⟨x,m,hm⟩ := hi.nonempty
  let B := max V m
  have actual (t : ℕ) (ht : m ≤ t) : w t = safeProposal O A t :=
    if_pos (show (A.stage (t+1)).Nonempty from ⟨x,A.monotone_stage (by omega) hm⟩)
  have distinct (a b : ℕ) (ha : B ≤ a) (hab : a < b) : w a ≠ w b := by
    rw [actual a (by dsimp [B] at ha; omega), actual b (by dsimp [B] at ha; omega)]
    exact (hV b (by dsimp [B] at ha; omega)).2.2 a hab
  have avoid (F : Finset ℕ) : ∀ᶠ t in atTop, w t ∉ F := by
    let f (n : ℕ) := w (B+n)
    have hf : Function.Injective f := by
      intro i j h
      rcases lt_trichotomy i j with hl|he|hl
      · exact (distinct _ _ (by omega) (by omega : B+i < B+j) h).elim
      · exact he
      · exact (distinct _ _ (by omega) (by omega : B+j < B+i) h.symm).elim
    have hfinite := F.finite_toSet.preimage hf.injOn
    obtain ⟨N,hN⟩ := hfinite.bddAbove
    filter_upwards [eventually_ge_atTop (B+N+1)] with t ht
    intro htF
    have hm : t-B ∈ f ⁻¹' (F : Set ℕ) := by simpa [f, show B+(t-B)=t by omega] using htF
    have := hN hm
    omega
  have inf := SparseReplacement.marked_infinite O w avoid
  have fresh (t) : r.word t ∉ A.stage (t+1) ∪ g.stage t := strictWord_fresh O A t (g.stage t)
  have round (t) (h : marked t) : r.word t =
      PartialEnumeration.Sharpness.firstMissing (A.stage (t+1) ∪ g.stage t) := by
    rw [word, strictWord, if_pos h]
  have covered : (O z).carrier \ A.limit ⊆ g.limit := by
    intro y hy
    apply r.covers inf
    intro hnot t ht
    rw [round t ht]
    apply PartialEnumeration.Sharpness.firstMissing_le
    intro h
    rcases Finset.mem_union.mp h with hA | hG
    · exact hy.2 (A.stage_subset_limit _ hA)
    · exact hnot (g.stage_subset_limit _ hG)
  obtain ⟨S,hS⟩ := safeChoice_eventual (C := fun i => (O i).carrier) single hi hs
  have precision : lowerMembershipPrecision (O z).carrier g = 1 := by
    apply r.precision (T := max S B) (SparseReplacement.sparse_time O w)
    intro t ht hsafe
    have hn : ¬marked t := fun h => hsafe ((SparseReplacement.mem_round ..).mpr h)
    rw [word]
    change (if marked t then _ else if w t ∈ _ then _ else w t) ∈ _
    rw [if_neg hn]
    split
    · exact hS t (by omega) _
    · rw [actual t (by dsimp [B] at ht; omega)]
      exact (hV t (by dsimp [B] at ht; omega)).1
  have hnov : GeneratorNovel p.generator A := by
    intro t
    rw [WordRule.generator_apply p (strictWord_causal O)]
    exact Finset.disjoint_singleton_left.mpr (fresh t)
  refine ⟨hnov, fun t => by rw [r.increment]; simp, precision,
    max_le (lemma_4_7 _ _ _ covered) ?_⟩
  let early := Set.range (fun i : Fin B => safeProposal O A i)
  let virtual := Set.range (safeProposal O A) \ early
  let D := SparseReplacement.discarded O w
  have hsub : virtual ⊆ g.limit ∪ D := by
    rintro y ⟨⟨t,rfl⟩,he⟩
    have ht : B ≤ t := le_of_not_gt (fun h => he ⟨⟨t,h⟩,rfl⟩)
    have eqn := actual t ((le_max_right ..).trans ht)
    rw [← eqn]
    by_cases hmark : marked t
    · exact Or.inr ⟨t,hmark,rfl⟩
    · left
      by_cases prev : w t ∈ g.stage t
      · exact g.stage_subset_limit _ prev
      have hav : w t ∉ A.stage (t+1) := by
        rintro h
        obtain ⟨j,hj,hh⟩ := Exhaustion.stage_mem_inputWord single t _ h
        exact (hV t ((le_max_left ..).trans ht)).2.1 j hj (hh.trans eqn)
      have fr : w t ∉ A.stage (t+1) ∪ g.stage t := by simpa using And.intro hav prev
      have hw : r.word t = w t := by
        rw [word, strictWord, if_neg hmark, if_neg fr]
      apply g.stage_subset_limit (t+1)
      rw [r.step, hw]
      exact Finset.mem_insert_self _ _
  have hden := (O z).lowerDensity_div_le_of_eventually_prefixRatio_le virtual g.limit 1
    (by norm_num) _ (SparseReplacement.sparse_ranks O w z) (Eventually.of_forall fun n => by
      simpa only [one_mul] using ((O z).prefixRatio_mono hsub n).trans
        ((O z).prefixRatio_union_le g.limit D n))
  have hearly : early.Finite := Set.finite_range _
  simp only [virtual, (O z).lowerDensity_diff_finite _ hearly, div_one] at hden
  exact density.trans hden

end GenLimit.InfinitelyManyHallucinations
