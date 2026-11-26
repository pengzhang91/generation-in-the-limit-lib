import GenLimit.Paper29_MistakeBoundedLanguageGeneration.NoisyFinite

/-! # Lemma B.2: reducing language generation to learning from demonstrations

The context at each round is the observed prefix. A language rewards exactly
its fresh members. A learner that predicts an already-seen point earns zero
reward for every comparator, so a fresh replacement preserves its bound.
-/
namespace GenLimit.MistakeBounded
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev DemonstrationLearner (X Y : Type*) :=
  ∀ t : ℕ, (Fin t → X × Y) → X → Y

def demonstrationReward (K : Set α) (ctx : List α) (x : α) : Bool :=
  decide (x ∈ K ∧ x ∉ ctx)

def demonstrationErrors (K : Set α) (contexts : ℕ → List α) (actions : ℕ → α) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, if demonstrationReward K (contexts t) (actions t) then 0 else 1

def demonstratedAction (A : DemonstrationLearner X Y) (x : ℕ → X) (y : ℕ → Y) (t : ℕ) :=
  A t (fun i => (x i.val,y i.val)) (x t)

private def rawGeneration (A : DemonstrationLearner (List α) α) : Generic.Generator α :=
  fun t h => A t (fun i => ((List.ofFn h).take i.val,h i)) (List.ofFn h)

private theorem rawGeneration_output (A : DemonstrationLearner (List α) α) (s : ℕ → α) (t : ℕ) :
    Generic.output (rawGeneration A) s t = demonstratedAction A (textPrefix s) s t := by
  unfold Generic.output rawGeneration demonstratedAction
  rw [← textPrefix_eq_ofFn]
  congr 1
  funext i
  congr 1
  apply List.ext_getElem
  · simp [textPrefix_length]
  · intro j hj _
    simp [textPrefix]

private def freshened [Infinite α] (A : DemonstrationLearner (List α) α) : Generic.Generator α := by
  classical
  exact fun t h => if rawGeneration A t h ∈ (List.ofFn h).toFinset then
    Classical.choose (exists_fresh_of_infinite (List.ofFn h).toFinset) else rawGeneration A t h

/-- Every reward-loss guarantee on arbitrary demonstration histories yields
the same comparator-wise mistake bound on injective language streams. -/
theorem generation_of_demonstrations [Infinite α] (L : ι → Set α)
    (A : DemonstrationLearner (List α) α) (M : ι → ℕ → ℕ → ℝ)
    (guarantee : ∀ ctx s i T, (demonstrationErrors (L i) ctx (demonstratedAction A ctx s) T : ℝ)
      ≤ M i T (demonstrationErrors (L i) ctx s T)) :
    ∃ G : Generic.Generator α, (∀ t h (j : Fin t), G t h ≠ h j) ∧
      ∀ s, Function.Injective s → ∀ i T,
        (membershipErrors (L i) (Generic.output G s) T : ℝ) ≤ M i T (membershipErrors (L i) s T) := by
  classical
  refine ⟨freshened A,?_,?_⟩
  · intro t h j eq
    have mem : h j ∈ (List.ofFn h).toFinset := by simp
    rw [← eq] at mem
    unfold freshened at mem
    split at mem
    · exact Classical.choose_spec (exists_fresh_of_infinite _) mem
    · contradiction
  · intro s hs i T
    have orig := guarantee (textPrefix s) s i T
    have noise : demonstrationErrors (L i) (textPrefix s) s T = membershipErrors (L i) s T := by
      apply Finset.sum_congr rfl
      intro t _
      have unseen : s t ∉ textPrefix s t := by
        simp only [textPrefix,List.mem_map,List.mem_range]
        rintro ⟨j,hj,eq⟩
        exact hj.ne (hs eq)
      simp [demonstrationReward,unseen]
    rw [noise] at orig
    apply le_trans _ orig
    apply Nat.cast_le.mpr
    apply Finset.sum_le_sum
    intro t _
    rw [← rawGeneration_output]
    dsimp only [Generic.output,freshened]
    rw [textPrefix_eq_ofFn]
    by_cases seen : rawGeneration A t (fun j : Fin t => s j) ∈ List.ofFn (fun j : Fin t => s j)
    · simp only [List.mem_toFinset,demonstrationReward,seen,not_true_eq_false,
        and_false,decide_false,Bool.false_eq_true,if_false]
      repeat' split <;> simp_all
    · simp [demonstrationReward,seen]

end
end GenLimit.MistakeBounded
