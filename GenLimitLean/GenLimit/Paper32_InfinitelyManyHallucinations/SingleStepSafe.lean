import GenLimit.Bridges.Paper39ToPaper15
import GenLimit.Paper32_InfinitelyManyHallucinations.SingleStepInput
import GenLimit.Paper32_InfinitelyManyHallucinations.TailPrecision

/-! # A strictly novel, single-step generator with the sharp half-recall guarantee

Apply the P15 partial-text generator to a causal reconstruction of the input
stream. Suppression of an unavailable proposal enforces novelty on every
round. Only finitely many proposals can be suppressed on any legal run.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Set KleinbergWei KleinbergWei.DensityMeasures.OrderedFocus

noncomputable def safeProposal (O : ℕ → OrderedLanguage) (A : Exhaustion) (t : ℕ) :=
  Bridge.Paper39ToPaper15.generate O A.inputWord t

theorem safeProposal_prefix {O : ℕ → OrderedLanguage} {A B : Exhaustion} {t : ℕ}
    (h : ∀ i ≤ t+1, A.stage i = B.stage i) (ha : (A.stage (t+1)).Nonempty) :
    safeProposal O A t = safeProposal O B t :=
  Bridge.Paper39ToPaper15.generate_prefix _ _ _ _ (Exhaustion.inputWord_prefix h ha)

private noncomputable def proposalRule (O : ℕ → OrderedLanguage) : StageRule
  | _, 0, _ => ∅
  | A, t+1, prev => if (A.stage (t+1)).Nonempty then
      {safeProposal O A t} \ (A.stage (t+1) ∪ prev) else ∅

private theorem proposalRule_causal (O : ℕ → OrderedLanguage) : (proposalRule O).Causal := by
  intro A B n h prev
  cases n with
  | zero => rfl
  | succ t =>
    by_cases ha : (A.stage (t+1)).Nonempty
    · simp only [proposalRule, h _ le_rfl, safeProposal_prefix h ha]
    · simp [proposalRule, ← h _ le_rfl, ha]

noncomputable def safeGenerator (O : ℕ → OrderedLanguage) := (proposalRule O).toBatch

private theorem safeBatch (O : ℕ → OrderedLanguage) (A : Exhaustion) (t : ℕ) (prev : Finset ℕ) :
    safeGenerator O (t+1) (fun i => A.stage i) prev = if (A.stage (t+1)).Nonempty then
      {safeProposal O A t} \ (A.stage (t+1) ∪ prev) else ∅ :=
  StageRule.toBatch_apply (proposalRule_causal O) A (t+1) prev

private theorem safe_novel (O : ℕ → OrderedLanguage) (A : Exhaustion) :
    GeneratorNovel (safeGenerator O) A := by
  intro t
  rw [safeBatch]
  split
  · exact Finset.disjoint_left.mpr (fun _ h => (Finset.mem_sdiff.mp h).2)
  · simp

private theorem safe_stage_outputs (O : ℕ → OrderedLanguage) (A : Exhaustion) (t : ℕ) :
    ∀ x ∈ generatedStages (safeGenerator O) A t, ∃ i < t, safeProposal O A i = x := by
  induction t with
  | zero => simp [generatedStages]
  | succ t ih =>
    intro x hx
    rw [generatedStages,safeBatch] at hx
    rcases Finset.mem_union.mp hx with old | new
    · obtain ⟨i,hi,he⟩ := ih x old
      exact ⟨i,by omega,he⟩
    · split at new
      · exact ⟨t,by omega, (Finset.mem_singleton.mp (Finset.mem_sdiff.mp new).1).symm⟩
      · simp at new

private theorem safe_single (O : ℕ → OrderedLanguage) (A : Exhaustion) :
    (generatedExhaustion (safeGenerator O) A).IsSingleStep := by
  intro t
  change ((generatedStages _ A (t+1)) \ generatedStages _ A t).card ≤ 1
  rw [generatedStages,safeBatch]
  split
  · apply (Finset.card_le_card (show _ ⊆ {safeProposal O A t} from ?_)).trans (by simp)
    intro x hx
    exact (Finset.mem_sdiff.mp ((Finset.mem_union.mp (Finset.mem_sdiff.mp hx).1).resolve_left
      (Finset.mem_sdiff.mp hx).2)).1
  · simp

/-- Theorem 3.5 at P32's finite-batch interface, including empty input
increments and the raw requirement to avoid every previous output. -/
theorem singleStep_half_recall (O : ℕ → OrderedLanguage) (hc : Compatible O) :
    ∃ G : BatchGenerator, ∀ (A : Exhaustion) (z : ℕ),
      A.IsSingleStep → A.limit.Infinite → A.limit ⊆ (O z).carrier →
      let g := generatedExhaustion G A
      GeneratorNovel G A ∧ g.IsSingleStep ∧ g.limit.Infinite ∧
        lowerTailPrecision (O z).carrier g = 1 ∧
        lowerMembershipPrecision (O z).carrier g = 1 ∧
        lowerRecall (O z) A.limit / 2 ≤ lowerRecall (O z) g.limit := by
  refine ⟨safeGenerator O, ?_⟩
  intro A z hA hi hs
  let g := generatedExhaustion (safeGenerator O) A
  let w := safeProposal O A
  have hp := Exhaustion.inputWord_presents hA hi.nonempty
  obtain ⟨⟨V,hV⟩, hd⟩ := Bridge.Paper39ToPaper15.theorem_1_6 O hc hp hi hs le_rfl
  obtain ⟨x,m,hm⟩ := hi.nonempty
  let B := max V m
  have accepted (t : ℕ) (ht : B ≤ t) :
      w t ∈ g.stage (t+1) := by
    obtain ⟨_,hinput,hout⟩ := hV t ((le_max_left ..).trans ht)
    have nonempty : (A.stage (t+1)).Nonempty :=
      ⟨x,A.monotone_stage (by dsimp [B] at ht; omega) hm⟩
    change w t ∈ generatedStages _ A (t+1)
    rw [generatedStages,safeBatch,if_pos nonempty]
    apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_singleton_self _, ?_⟩
    intro hn
    rcases Finset.mem_union.mp hn with hin | hg
    · obtain ⟨j,hj,he⟩ := Exhaustion.stage_mem_inputWord hA t _ hin
      exact hinput j hj he
    · obtain ⟨j,hj,he⟩ := safe_stage_outputs O A t _ hg
      exact hout j hj he
  have eventual : EventuallyValid (O z).carrier g := by
    refine ⟨V+1,?_⟩
    rintro (_ | t) ht y hy
    · omega
    · change y ∈ generatedStages _ A (t+1) \ generatedStages _ A t at hy
      rw [generatedStages,safeBatch] at hy
      have hnew := (Finset.mem_union.mp (Finset.mem_sdiff.mp hy).1).resolve_left (Finset.mem_sdiff.mp hy).2
      split at hnew
      · obtain rfl := Finset.mem_singleton.mp (Finset.mem_sdiff.mp hnew).1
        exact (hV t (by omega)).1
      · simp at hnew
  have inj : Function.Injective (fun n : ℕ => w (B+n)) := by
    intro a b h
    rcases lt_trichotomy a b with hl | he | hg
    · exact False.elim ((hV (B+b) (by dsimp [B]; omega)).2.2 (B+a) (by omega) h)
    · exact he
    · exact False.elim ((hV (B+a) (by dsimp [B]; omega)).2.2 (B+b) (by omega) h.symm)
  have hinf : g.limit.Infinite := (Set.infinite_range_of_injective inj).mono (by
    rintro _ ⟨n,rfl⟩
    exact g.stage_subset_limit _ (accepted _ (by omega)))
  have htail := eventuallyValid_implies_lowerTailPrecision_one eventual
  refine ⟨safe_novel O A, safe_single O A, hinf, htail,
    appendix_lemma_D_1_of_limit_infinite hinf htail, ?_⟩
  let early := Set.range (fun i : Fin B => w i)
  have hsub : Set.range w \ early ⊆ g.limit := by
    rintro y ⟨⟨t,rfl⟩,he⟩
    by_cases ht : B ≤ t
    · exact g.stage_subset_limit _ (accepted t ht)
    · exact False.elim (he ⟨⟨t,by omega⟩,rfl⟩)
  have hle := (O z).lowerDensity_mono hsub
  rw [(O z).lowerDensity_diff_finite _ (Set.finite_range _)] at hle
  exact hd.trans hle

end GenLimit.InfinitelyManyHallucinations
