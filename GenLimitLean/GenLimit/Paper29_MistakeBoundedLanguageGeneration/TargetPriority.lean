import GenLimit.Paper29_MistakeBoundedLanguageGeneration.ModifiedGreedy
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.WorstCase
import GenLimit.Paper02_LearningTheory.Common.FiniteHistory
import GenLimit.Support.Fresh

/-! # Target priority and the pointwise lower bound in Theorem 6.4

A finite initial modification of Modified-Greedy preserves its asymptotic
last-mistake guarantee. During this prefix the generator can give absolute
priority to any one specified target. After its cutoff Modified-Greedy
already succeeds on that target. Thus its worst-case number of mistakes can
be zero at a prescribed index, even for the class in the existential claim.
-/
namespace GenLimit.MistakeBounded
open Generic LiRamanTewari.Common

/-- The exact finite maximum in Definition 5. Infinite intersections
contribute zero to the maximum by the convention for natural cardinality. -/
noncomputable def prefixComplexity (L : ℕ → Set α) (i : ℕ) : ℕ :=
  (Finset.range i).powerset.sup fun J => (modifiedGreedyFiniteIntersection L i J).ncard

theorem prefixComplexity_bound (L : ℕ → Set α) (i : ℕ) :
    NonuniformComplexityAtMost L i (prefixComplexity L i) := by
  intro J hJ _
  unfold prefixComplexity
  exact Finset.le_sup (f := fun J => (modifiedGreedyFiniteIntersection L i J).ncard) (Finset.mem_powerset.mpr hJ)

private theorem prefixCandidates (L : ℕ → Set α) (s : ℕ → α) (t : ℕ) [Nonempty α] (k : ℕ) :
    modifiedGreedyCandidates L (extendHistory (fun j : Fin t => s j)) t k =
      modifiedGreedyCandidates L s t k := by
  induction k with
  | zero => simp only [modifiedGreedyCandidates_zero, sample_extendHistory_stream_eq (stream := s) (t := t) le_rfl]
  | succ k ih =>
    have hc : modifiedGreedyConsistent L (extendHistory (fun j : Fin t => s j)) t k ↔
        modifiedGreedyConsistent L s t k := by
      unfold modifiedGreedyConsistent
      exact forall_congr' fun j => forall_congr' fun hj =>
        by rw [extendHistory_apply_of_lt _ hj]
    rw [modifiedGreedyCandidates_succ, modifiedGreedyCandidates_succ]
    split_ifs <;> simp_all

private theorem choose_same_set {S T : Set α} (hs : S.Nonempty) (ht : T.Nonempty)
    (eq : S = T) : Classical.choose hs = Classical.choose ht := by
  cases eq
  rfl

/-- A single causal generator on the source's generator-first interface. -/
noncomputable def priorityGenerator [Infinite α] (L : ℕ → Set α)
    (p : ℕ) (hp : (L p).Infinite) : Generic.Generator α :=
  fun t xs =>
    if t < max p (prefixComplexity L p + 1) then
      Support.freshFromInfinite _ hp (sequenceSample xs)
    else modifiedGreedyGenerated L (extendHistory xs) t

private theorem priority_after [Infinite α] (L : ℕ → Set α) (p : ℕ)
    (hp : (L p).Infinite) (s : ℕ → α) (t : ℕ) (ht : max p (prefixComplexity L p + 1) ≤ t) :
    Generic.output (priorityGenerator L p hp) s t = modifiedGreedyGenerated L s t := by
  simp only [Generic.output, priorityGenerator, if_neg (Nat.not_lt.mpr ht)]
  exact choose_same_set _ _ (prefixCandidates L s t (t+1))

/-- Runs include every exact injective presentation, and also allow arbitrary
injective positive streams as in the upper bound of Lemma 6.3. -/
abbrev PositiveRun (K : Set α) := {s : ℕ → α // Function.Injective s ∧ ∀ t, s t ∈ K}

/-- One-based index and exact nonuniform complexity in the Big-O premise. -/
noncomputable def paperTimeScale (L : ℕ → Set α) (i : ℕ) := max (i+1) (prefixComplexity L i)

/-- For every family and every prescribed target, one causal fresh generator
obeys one common multiplicative last-mistake bound at all indices and makes
zero mistakes on every presentation of the prescribed target. -/
theorem priority_zero_mistakes [Infinite α] (L : ℕ → Set α)
    (p : ℕ) (hp : (L p).Infinite) :
    ∃ G : Generic.Generator α,
      (∀ t xs, G t xs ∉ sequenceSample xs) ∧
      (∃ C : ℕ, ∀ i (s : PositiveRun (L i)),
        LastMistakeBefore (countableTargetTrace L (Generic.output G s.val) i)
          (C * paperTimeScale L i)) ∧
      worstCaseMistakes (fun s : PositiveRun (L p) =>
        countableTargetTrace L (Generic.output G s.val) p) = 0 := by
  classical
  let K := max p (prefixComplexity L p + 1)
  let G := priorityGenerator L p hp
  have after (i : ℕ) (s : PositiveRun (L i)) (t : ℕ)
      (hk : K ≤ t) (hi : i ≤ t) (hm : prefixComplexity L i < t) :
      Generic.output G s.val t ∈ L i := by
    rw [show G = priorityGenerator L p hp from rfl, priority_after _ _ _ _ _ hk]
    exact modifiedGreedyGenerated_mem_target_after_complexity L s.val s.property.1
      i _ s.property.2 (prefixComplexity_bound L i) t hi hm
  refine ⟨G, ?_, ⟨K + 2, ?_⟩, ?_⟩
  · intro t xs
    change (if _ then _ else _) ∉ _
    split
    · exact Support.freshFromInfinite_not_mem _ _ _
    · simpa only [sample_extendHistory_full] using
        modifiedGreedyGenerated_not_mem_sample L (extendHistory xs) t
  · intro i s t ht
    let b := paperTimeScale L i
    have hi : i + 1 ≤ b := Nat.le_max_left ..
    have hm : prefixComplexity L i ≤ b := Nat.le_max_right ..
    have hb : 1 ≤ b := by omega
    have h := Nat.mul_le_mul_left K hb
    change (K + 2) * b ≤ t at ht
    have hbound := after i s t (by nlinarith) (by nlinarith) (by nlinarith)
    simp [countableTargetTrace, hbound]
  · apply le_antisymm _ bot_le
    apply (worstCaseMistakes_le_iff _ 0).mpr
    intro s n
    have hgood (t : ℕ) : Generic.output G s.val t ∈ L p := by
      by_cases ht : t < K
      · change (if t < K then _ else _) ∈ _
        rw [if_pos ht]
        exact Support.freshFromInfinite_mem _ _ _
      · have hk := Nat.le_of_not_gt ht
        exact after p s t hk ((Nat.le_max_left ..).trans hk)
          ((Nat.le_max_right ..).trans hk)
    simp [mistakeCount, countableTargetTrace, hgood]

end GenLimit.MistakeBounded
