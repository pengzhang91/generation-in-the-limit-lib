import GenLimit.Paper32_InfinitelyManyHallucinations.PodBlockLoss
import GenLimit.Paper32_InfinitelyManyHallucinations.PodResults

/-! # Counterexamples to the recall clauses for Algorithms 2 and 6
The full target is presented once in descending blocks. At most the pool
present at the beginning of a block, its first few pods, and the exploratory
outputs can meet that block's target prefix. Once the block is exhausted
strict novelty prevents recovery of any further prefix members.
-/
namespace GenLimit.InfinitelyManyHallucinations.Pods.Counterexample
open Set Filter KleinbergWei KleinbergWei.PartialEnumeration.Sharpness
open scoped Classical Topology

private def config (R : Set ℕ) : Config := ⟨family,R,false,(fun u => u+1),Equiv.refl _⟩
private noncomputable abbrev state (R : Set ℕ) (t : ℕ) := (config R).run input t
private noncomputable abbrev guess (R : Set ℕ) := generatedExhaustion (config R).rule.generator input

private noncomputable def inside (R : Set ℕ) (n t : ℕ) :=
  ((state R t).pool ∪ (state R t).words) ∩ Finset.range (border (n+1))

private theorem pool_bound (R : Set ℕ) (t : ℕ) : (state R t).pool.card ≤ t*t := by
  induction t with
  | zero => simp [state,Config.run]
  | succ t ih =>
    change ((config R).nextPool input t _ _).card ≤ _
    unfold Config.nextPool
    split
    · have h := Finset.card_union_le (s := (state R t).pool)
        (t := (config R).newPod input t (state R t).pool (state R t).words)
      have card := (newPod_spec (config R) family_infinite input t (state R t).pool (state R t).words).1
      change _ = Nat.count (safe R) t + 1 at card
      have : Nat.count (safe R) t ≤ t := Nat.count_le _
      nlinarith
    · exact ih.trans (Nat.mul_le_mul (Nat.le_succ t) (Nat.le_succ t))

private theorem early_bound (R : Set ℕ) (hR : (setOf (safe R)).Infinite) (n : ℕ) :
    (inside R n (border n+6)).card ≤ (border n+8)^2 := by
  let t := border n+6
  let c := config R
  let r := c.rule.rounds (rule_causal c hR) (rule_fresh c) input
  have hwords : (state R t).words.card = t := (stage_run c hR input t) ▸ r.card t
  have h := Finset.card_le_card (Finset.inter_subset_left :
    inside R n t ⊆ (state R t).pool ∪ (state R t).words)
  have hu := Finset.card_union_le (s := (state R t).pool) (t := (state R t).words)
  have hp := pool_bound R t
  apply h.trans (hu.trans ?_)
  rw [hwords]
  apply (Nat.add_le_add_right hp t).trans
  dsimp [t]
  nlinarith

private theorem safe_step {R : Set ℕ} (near : ∀ t, safe R t ∨ safe R (t+1))
    (hR : (setOf (safe R)).Infinite) {n t : ℕ} (lo : border n+6 ≤ t) (hi : t < border (n+1))
    (ht : safe R t) : inside R n (t+1) ⊆ inside R n t := by
  let c := config R
  let old := state R t
  let next := c.nextPool input t old.pool old.words
  have out : c.output input t old.pool old.words ∈ next :=
    output_safe_mem c family_infinite (fun _ => by dsimp [c,config]; omega) input t ht _ _
  intro x hx
  obtain ⟨mem,small⟩ := Finset.mem_inter.mp hx
  change x ∈ next ∪ insert (c.output input t old.pool old.words) old.words at mem
  have fromNext (h : x ∈ next) : x ∈ old.pool := by
    change x ∈ c.nextPool input t old.pool old.words at h
    rw [Config.nextPool,if_pos (show safe c.explore t from ht)] at h
    rcases Finset.mem_union.mp h with ho|hn
    · exact ho
    · obtain ⟨hm,hfresh⟩ := (newPod_spec c family_infinite input t old.pool old.words).2 x hn
      have seen := late_pod_outside near hR lo hi ht (Finset.mem_range.mp small) hm
      exact (hfresh (Finset.mem_union_right _ (Finset.mem_union_left _ seen))).elim
  refine Finset.mem_inter.mpr ⟨?_,small⟩
  rcases Finset.mem_union.mp mem with h|h
  · exact Finset.mem_union_left _ (fromNext h)
  · rcases Finset.mem_insert.mp h with h|h
    · exact Finset.mem_union_left _ (fromNext (h ▸ out))
    · exact Finset.mem_union_right _ h

private theorem explore_step {R : Set ℕ} {t : ℕ} (ht : ¬safe R t) (n : ℕ) :
    (inside R n (t+1)).card ≤ (inside R n t).card + 1 := by
  let c := config R
  let old := state R t
  let y := c.output input t old.pool old.words
  apply le_trans (Finset.card_le_card (t := insert y (inside R n t)) ?_) (Finset.card_insert_le ..)
  intro x hx
  obtain ⟨mem,small⟩ := Finset.mem_inter.mp hx
  change x ∈ c.nextPool input t old.pool old.words ∪ insert y old.words at mem
  rw [Config.nextPool,if_neg (show ¬safe c.explore t from ht)] at mem
  rcases Finset.mem_union.mp mem with h|h
  · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h,small⟩)
  · rcases Finset.mem_insert.mp h with eq|ho
    · exact Finset.mem_insert.mpr (.inl eq)
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ ho,small⟩)

private theorem end_pool_bound {R : Set ℕ} (near : ∀ t, safe R t ∨ safe R (t+1))
    (hR : (setOf (safe R)).Infinite) (n : ℕ) :
    (inside R n (border (n+1))).card ≤ (border n+8)^2 + explorationCount R (border (n+1)) := by
  have bound (t : ℕ) (lo : border n+6 ≤ t) (hi : t ≤ border (n+1)) :
      (inside R n t).card ≤ (border n+8)^2 + explorationCount R t := by
    induction t,lo using Nat.le_induction with
    | base => exact (early_bound R hR n).trans (Nat.le_add_right ..)
    | succ t lo ih =>
      have before := ih (by omega)
      rw [explorationCount_succ]
      by_cases ht : t+1 ∈ R
      · rw [if_pos ht]
        have := explore_step (R := R) (t := t) (fun h => h ht) n
        omega
      · rw [if_neg ht,Nat.add_zero]
        exact (Finset.card_le_card (safe_step near hR lo (by omega) ht)).trans before
  exact bound _ (by have := border_step n; omega) le_rfl

private theorem fresh {R : Set ℕ} (t : ℕ) : (config R).rule input t ((guess R).stage t) ∉
    input.stage (t+1) ∪ (guess R).stage t := by
  by_cases ht : safe R t
  · exact output_safe_fresh _ _ ht _ _
  · change (config R).output input t _ _ ∉ _
    rw [Config.output,if_neg (show ¬safe (config R).explore t from ht)]
    exact scan_fresh _ _

private theorem prefix_bound {R : Set ℕ} (near : ∀ t, safe R t ∨ safe R (t+1))
    (hR : (setOf (safe R)).Infinite) (n : ℕ) :
    natural.prefixCount (guess R).limit (border (n+1)) ≤
      (border n+8)^2 + explorationCount R (border (n+1)) := by
  let N := border (n+1)
  let g := guess R
  let c := config R
  let r := c.rule.rounds (rule_causal c hR) (rule_fresh c) input
  have closed {x : ℕ} (hx : x < N) (t : ℕ) (h : x ∈ g.stage t) : x ∈ g.stage N := by
    induction t with
    | zero => simp [Exhaustion.stage_zero] at h
    | succ t ih =>
      by_cases ht : t+1 ≤ N
      · exact g.monotone_stage ht h
      · rw [r.step] at h
        rcases Finset.mem_insert.mp h with he|ho
        · have seen := input.monotone_stage (by omega : N ≤ t+1) (block_complete _ hx)
          exact (fresh t (Finset.mem_union_left _ (he ▸ seen))).elim
        · exact ih ho
  apply le_trans (Finset.card_le_card (t := inside R n N) ?_) (end_pool_bound near hR n)
  intro x hx
  obtain ⟨small,⟨t,h⟩⟩ := Finset.mem_filter.mp hx
  have done := closed (Finset.mem_range.mp small) t h
  rw [stage_run c hR] at done
  exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ done,small⟩

/-- At the ends of infinitely many descending blocks the output density
tends to zero. This holds for every sparse, nonconsecutive exploration
schedule, and also for the generator which never explores. -/
theorem zero_recall {R : Set ℕ} (near : ∀ t, safe R t ∨ safe R (t+1))
    (hR : (setOf (safe R)).Infinite)
    (sparse : Tendsto (fun n : ℕ => (explorationCount R n : ℝ)/n) atTop (𝓝 0)) :
    lowerRecall natural (guess R).limit = 0 := by
  let g := guess R
  let endAt (n : ℕ) := border (n+1)
  have cofinal : Tendsto endAt atTop atTop := (border_strict.comp (fun _ _ h => Nat.succ_lt_succ h)).tendsto_atTop
  have bound (n : ℕ) : natural.prefixRatio g.limit (endAt n) ≤
      1/(n+1 : ℕ) + (explorationCount R (endAt n) : ℝ)/endAt n := by
    have pos : 0 < endAt n := by have := border_step n; dsimp [endAt]; omega
    rw [OrderedLanguage.prefixRatio,if_neg pos.ne']
    have card : (natural.prefixCount g.limit (endAt n) : ℝ) ≤
        ((border n : ℝ)+8)^2 + explorationCount R (endAt n) := by exact_mod_cast prefix_bound near hR n
    have den : (endAt n : ℝ) = (n+1 : ℕ)*((border n : ℝ)+8)^2 := by
      dsimp [endAt]; rw [border]; push_cast; ring
    calc
      _ ≤ (((border n : ℝ)+8)^2 + explorationCount R (endAt n)) / endAt n :=
        div_le_div_of_nonneg_right card (by positivity)
      _ = _ := by rw [add_div,den]; push_cast; field_simp
  have one : Tendsto (fun n : ℕ => 1/(n+1 : ℕ) : ℕ → ℝ) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 1)
  have limit : Tendsto (fun n => natural.prefixRatio g.limit (endAt n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => natural.prefixRatio_nonneg _ _) bound
    simpa using one.add (sparse.comp cofinal)
  refine le_antisymm ?_ (lowerRecall_nonneg ..)
  change liminf (natural.prefixRatio g.limit) atTop ≤ 0
  rw [← limit.liminf_eq]
  change _ ≤ liminf (natural.prefixRatio g.limit) (map endAt atTop)
  exact liminf_le_liminf_of_le cofinal (isBoundedUnder_of ⟨0,natural.prefixRatio_nonneg _⟩)
    (isCoboundedUnder_ge_of_le _ (fun n => natural.prefixRatio_le_one _ n))

theorem input_recall : lowerRecall natural input.limit = 1 :=
  lowerRecall_eq_one_of_target_subset _ (by rw [input_full]; exact Set.subset_univ _)

/-- Lemma 4.5 fails for the printed Algorithm 2, with the suggested pod sizes
1,2,..., even when the full target is revealed one word at a time. -/
theorem algorithm2_zero_recall :
    input.IsSingleStep ∧ input.limit = univ ∧ lowerRecall natural input.limit = 1 ∧
    lowerRecall natural (generatedExhaustion (algorithm2 family (fun u => u+1)).rule.generator input).limit = 0 := by
  refine ⟨input_single,input_full,input_recall,zero_recall (R := ∅) (fun _ => Or.inl (by simp [safe])) ?_ ?_⟩
  · exact Set.infinite_univ.mono (fun _ _ => by simp [safe])
  · simp [explorationCount]

/-- The same legal input violates the proposed bound for every allowed batch cap. -/
theorem lemma_4_5_counterexample (k : ℕ) (hk : 2 ≤ k) :
    input.BoundedBy (fun _ => k) ∧ input.limit = univ ∧
      lowerRecall natural (generatedExhaustion (algorithm2 family (fun u => u+1)).rule.generator input).limit <
        lowerRecall natural input.limit / (k+1) := by
  obtain ⟨single,full,one,zero⟩ := algorithm2_zero_recall
  refine ⟨fun n => (single n).trans (show 1 ≤ k by omega), full, ?_⟩
  rw [zero, one]
  positivity

/-- The α/3 clause of Theorem 4.8 fails for the printed Algorithm 6 for
every admissible exploration set. Here α=β=1. -/
theorem algorithm6_zero_recall (E : ExplorationSet) :
    input.IsSingleStep ∧ input.limit = univ ∧ lowerRecall natural input.limit = 1 ∧
    lowerRecall natural (generatedExhaustion (algorithm6 family E (fun u => u+1)).rule.generator input).limit = 0 := by
  refine ⟨input_single,input_full,input_recall,zero_recall (R := E.carrier) ?_ (safe_infinite E)
    E.prefixRatio_tendsto_zero⟩
  intro t
  by_cases h : t+1 ∈ E.carrier
  · exact Or.inr (E.nonconsecutive _ h)
  · exact Or.inl h

end GenLimit.InfinitelyManyHallucinations.Pods.Counterexample
