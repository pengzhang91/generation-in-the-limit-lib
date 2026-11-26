import GenLimit.Paper32_InfinitelyManyHallucinations.SafeChoice
import GenLimit.Paper32_InfinitelyManyHallucinations.SingletonRounds
import GenLimit.Paper15_PartialEnumeration.Sharpness

/-! # A causal sparse-exploration generator for fractional novelty, Theorem 4.9

A safe round draws from the currently selected infinite intersection. On an
exploration round the generator emits the first word it has never emitted.
Thus every exploration increases coverage and costs at most one unit of the
finite-prefix novelty allowance.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Set KleinbergWei
open scoped Classical

abbrev WordRule := Exhaustion → ℕ → Finset ℕ → ℕ

def WordRule.Causal (p : WordRule) : Prop := ∀ (A B : Exhaustion) t,
  (∀ i ≤ t+1, A.stage i = B.stage i) → ∀ prev, p A t prev = p B t prev

private def singletonRule (p : WordRule) : StageRule
  | _, 0, _ => ∅
  | A, t+1, prev => {p A t prev}

noncomputable def WordRule.generator (p : WordRule) : BatchGenerator := (singletonRule p).toBatch

theorem WordRule.generator_apply (p : WordRule) (hc : p.Causal) (A : Exhaustion) (t : ℕ)
    (prev : Finset ℕ) :
    p.generator (t+1) (fun i => A.stage i) prev = {p A t prev} := by
  apply StageRule.toBatch_apply (R := singletonRule p)
  intro A B n h prev
  cases n with
  | zero => rfl
  | succ t => exact congrArg (fun x : ℕ => ({x} : Finset ℕ)) (hc A B t h prev)

noncomputable def WordRule.rounds (p : WordRule) (hc : p.Causal)
    (fresh : ∀ A t prev, p A t prev ∉ prev) (A : Exhaustion) :
    SingletonRounds (generatedExhaustion p.generator A) where
  word t := p A t (generatedStages p.generator A t)
  fresh t := fresh A t _
  step t := by
    change generatedStages p.generator A (t+1) = _
    rw [generatedStages, p.generator_apply hc]
    simp [generatedExhaustion]

private noncomputable def gammaWord (C : LanguageFamily) (E : ExplorationSet) : WordRule :=
  fun A t prev => if t+1 ∈ E.carrier then
    PartialEnumeration.Sharpness.firstMissing prev else safeChoice C A t prev

private theorem gammaWord_causal (C : LanguageFamily) (E : ExplorationSet) :
    (gammaWord C E).Causal := by
  intro A B t h prev
  simp only [gammaWord, safeChoice_prefix h]

private theorem gammaWord_fresh (C : LanguageFamily) (E : ExplorationSet)
    (A : Exhaustion) (t : ℕ) (prev : Finset ℕ) : gammaWord C E A t prev ∉ prev := by
  unfold gammaWord
  split
  · exact PartialEnumeration.Sharpness.firstMissing_notMem _
  · exact fun h => safeChoice_fresh C A t prev (Finset.mem_union_right _ h)

theorem exploration_steps_infinite (E : ExplorationSet) : {t : ℕ | t+1 ∈ E.carrier}.Infinite := by
  have hinf := (E.infinite'.diff (Set.finite_singleton 0)).image
    (f := Nat.pred) (show Set.InjOn Nat.pred (E.carrier \ {0}) from by
      intro a ha b hb he
      have ha0 : a ≠ 0 := ha.2
      have hb0 : b ≠ 0 := hb.2
      simp only [Nat.pred_eq_sub_one] at he
      omega)
  apply hinf.mono
  rintro _ ⟨t,ht,rfl⟩
  have h0 : t ≠ 0 := ht.2
  change t.pred + 1 ∈ E.carrier
  change t.pred.succ ∈ E.carrier
  simpa only [Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)] using ht.1

/-- Theorem 4.9. One generator for the whole family works on all infinite
single-step partial inputs. It produces one new word every round. -/
theorem fractional_perfect_recall (C : LanguageFamily) {γ : ℝ} (hγ : γ < 1) :
    ∃ G : BatchGenerator, ∀ (A : Exhaustion) (z : ℕ) (K : OrderedLanguage),
      K.carrier = C z → A.IsSingleStep → A.limit.Infinite → A.limit ⊆ C z →
      let g := generatedExhaustion G A
      g.IsEnumeration ∧ GammaNovel γ A g ∧ lowerRecall K g.limit = 1 ∧
        lowerMembershipPrecision (C z) g = 1 := by
  obtain ⟨E,hE⟩ := exists_gammaAdmissible_explorationSet hγ
  let p := gammaWord C E
  refine ⟨p.generator, ?_⟩
  intro A z K _ single hi hs
  let g := generatedExhaustion p.generator A
  let r := p.rounds (gammaWord_causal C E) (gammaWord_fresh C E) A
  have choice (t) : r.word t = gammaWord C E A t (g.stage t) := rfl
  obtain ⟨T,hT⟩ := safeChoice_eventual single hi hs
  refine ⟨fun t => by rw [r.increment]; simp, r.fractional_novelty A E hE ?_,
    lowerRecall_eq_one_of_target_subset K (fun x _ => ?_), r.precision (T := T) E.prefixRatio_tendsto_zero ?_⟩
  · intro t ht hm
    rw [choice, gammaWord, if_neg ht] at hm
    exact safeChoice_fresh _ _ _ _ (Finset.mem_union_left _ hm)
  · apply r.covers (exploration_steps_infinite E) x
    intro hx t ht
    change t+1 ∈ E.carrier at ht
    rw [choice, gammaWord, if_pos ht]
    exact PartialEnumeration.Sharpness.firstMissing_le (fun h => hx (g.stage_subset_limit _ h))
  · intro t ht he
    rw [choice, gammaWord, if_neg he]
    exact hT t ht _

end GenLimit.InfinitelyManyHallucinations
