import GenLimit.Paper32_InfinitelyManyHallucinations.ScheduledExploration
import GenLimit.Paper32_InfinitelyManyHallucinations.NoNovelty
import GenLimit.Paper32_InfinitelyManyHallucinations.ExhaustionOperations

/-! # Perfect tail precision with a fractional novelty requirement (E.1, I.3–4)

At repetition times copy the least revealed word that has not been output.
When none is waiting, take a safe fresh step. The same input transcript can
serve as full evidence for a smaller language or partial evidence for a
larger language; this gives the tight upper bound.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Set Filter KleinbergWei
open scoped Classical

private noncomputable def repetitionWord (C : LanguageFamily) (E : ExplorationSet) : WordRule :=
  fun A t prev => let waiting := A.stage (t+1) \ prev
    if h : t+1 ∈ E.carrier ∧ waiting.Nonempty then waiting.min' h.2
    else safeChoice C A t prev

private theorem repetition_causal (C : LanguageFamily) (E : ExplorationSet) :
    (repetitionWord C E).Causal := by
  intro A B t h prev
  simp only [repetitionWord, h _ le_rfl, safeChoice_prefix h]

private theorem repetition_fresh (C : LanguageFamily) (E : ExplorationSet)
    (A : Exhaustion) (t : ℕ) (prev : Finset ℕ) : repetitionWord C E A t prev ∉ prev := by
  dsimp only [repetitionWord]
  split
  · exact (Finset.mem_sdiff.mp (Finset.min'_mem _ _)).2
  · exact fun h => safeChoice_fresh C A t prev (Finset.mem_union_right _ h)

/-- Achievability in I.3. The same generator covers the entire adversarial
limit and achieves perfect tail precision for every target in its family. -/
theorem perfect_tail_fractional (C : LanguageFamily) {γ : ℝ} (hγ : γ < 1) :
    ∃ G : BatchGenerator, ∀ (A : Exhaustion) (z : ℕ),
      A.IsSingleStep → A.limit.Infinite → A.limit ⊆ C z →
      let g := generatedExhaustion G A
      g.IsEnumeration ∧ GammaNovel γ A g ∧ A.limit ⊆ g.limit ∧
        lowerMembershipPrecision (C z) g = 1 ∧ lowerTailPrecision (C z) g = 1 := by
  obtain ⟨E,quota⟩ := exists_gammaAdmissible_explorationSet hγ
  let p := repetitionWord C E
  refine ⟨p.generator, ?_⟩
  intro A z single hi hs
  let g := generatedExhaustion p.generator A
  let r := p.rounds (repetition_causal C E) (repetition_fresh C E) A
  have word (t) : r.word t = repetitionWord C E A t (g.stage t) := rfl
  obtain ⟨T,hT⟩ := safeChoice_eventual single hi hs
  have eventuallyValid : EventuallyValid (C z) g := by
    refine ⟨T+1, ?_⟩
    rintro (_|t) ht x hx
    · omega
    · rw [r.increment, Finset.coe_singleton, Set.mem_singleton_iff] at hx
      subst x
      rw [word]
      dsimp only [repetitionWord]
      split
      · exact hs (A.stage_subset_limit _ (Finset.mem_sdiff.mp (Finset.min'_mem _ _)).1)
      · exact hT t (by omega) _
  have tail := eventuallyValid_implies_lowerTailPrecision_one eventuallyValid
  refine ⟨fun t => by rw [r.increment]; simp, r.fractional_novelty A E quota ?_, ?_,
    appendix_lemma_D_1_of_limit_infinite r.infinite tail, tail⟩
  · intro t ht hm
    rw [word] at hm
    simp only [repetitionWord,ht,false_and,dif_neg,not_false_eq_true] at hm
    exact safeChoice_fresh _ _ _ _ (Finset.mem_union_left _ hm)
  · rintro x ⟨m,hm⟩
    have hR := (exploration_steps_infinite E).diff (Set.finite_Iio m)
    apply r.covers hR
    intro hx t ht
    have he : t+1 ∈ E.carrier := ht.1
    have hmt : m ≤ t := le_of_not_gt ht.2
    have hw : x ∈ A.stage (t+1) \ g.stage t := Finset.mem_sdiff.mpr
      ⟨A.monotone_stage (by omega) hm,fun h => hx (g.stage_subset_limit t h)⟩
    rw [word]
    dsimp only [repetitionWord]
    rw [dif_pos ⟨he, ⟨x,hw⟩⟩]
    exact Finset.min'_le _ x hw

/-- With bounded increments, perfect tail precision leaves finitely many
distinct errors over the complete run. -/
theorem bounded_tail_finite_errors (G : BatchGenerator) (A : Exhaustion)
    {c : ℕ} (hc : (generatedExhaustion G A).BoundedBy (fun _ => c))
    (htail : lowerTailPrecision A.limit (generatedExhaustion G A) = 1) :
    ((generatedExhaustion G A).limit \ A.limit).Finite := by
  let g := generatedExhaustion G A
  obtain ⟨N,_,hN⟩ := proposition_2_4_constantStep (L := A.limit) hc
  have ev : EventuallyValid A.limit g := (proposition_3_3 A.limit g).mpr
    ⟨N, fun n hn => le_antisymm (stepTailPrecision_le_one _ _ _)
      (htail ▸ hN n hn)⟩
  obtain ⟨T,hT⟩ := ev
  have sub (n : ℕ) : (g.stage n : Set ℕ) ⊆ ↑(g.stage T) ∪ A.limit := by
    induction n with
    | zero => simp [g.stage_zero]
    | succ n ih =>
      by_cases h : n+1 ≤ T
      · exact fun x hx => Or.inl (g.monotone_stage h hx)
      · intro x hx
        by_cases ho : x ∈ g.stage n
        · exact ih ho
        · exact Or.inr (hT (n+1) (by omega) (Finset.mem_sdiff.mpr ⟨hx,ho⟩))
  have hsub : g.limit \ ↑(g.stage T) ⊆ A.limit := by
    rintro x ⟨⟨n,hn⟩,hx⟩
    exact (sub n hn).resolve_left hx
  apply (g.stage T).finite_toSet.subset
  rintro x ⟨hx, outside⟩
  by_contra hxT
  exact outside (hsub ⟨hx, hxT⟩)

/-- The sharpness argument common to E.1 and I.3. Perfect tail precision
on the smaller target leaves only finitely many guesses outside it. On the
identical input for any larger target, recall is therefore at most that of
the revealed language. -/
theorem bounded_tail_recall_upper (G : BatchGenerator) (A : Exhaustion) (K : OrderedLanguage)
    {c : ℕ} (hc : (generatedExhaustion G A).BoundedBy (fun _ => c))
    (htail : lowerTailPrecision A.limit (generatedExhaustion G A) = 1) :
    lowerRecall K (generatedExhaustion G A).limit ≤ lowerRecall K A.limit := by
  let g := generatedExhaustion G A
  have finite := bounded_tail_finite_errors G A hc htail
  have sub : g.limit \ (g.limit \ A.limit) ⊆ A.limit := by
    intro x hx
    by_contra h
    exact hx.2 ⟨hx.1,h⟩
  have bound := K.lowerDensity_mono sub
  rw [K.lowerDensity_diff_finite _ finite] at bound
  exact bound

end GenLimit.InfinitelyManyHallucinations
