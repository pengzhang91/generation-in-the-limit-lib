import GenLimit.NoRegretLanguageGeneration.Capacity

namespace PredictionToGeneration

open scoped ENNReal

/-- Sum over leaves of the largest weight compatible with that leaf's path. -/
noncomputable def weightedLeaves (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞) :
    {n : Nat} → QueryTree X n → ℝ≥0∞
  | 0, .leaf => sSup (w '' {h | H h})
  | _+1, .node x l r => weightedLeaves (restrict H x false) w l + weightedLeaves (restrict H x true) w r

theorem weightedLeaves_le_capacity (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    {n : Nat} (tree : QueryTree X n) : weightedLeaves H w tree ≤ capacity H w n := by
  induction tree generalizing H with
  | leaf => exact le_rfl
  | node x l r ihl ihr =>
    exact (add_le_add (ihl _) (ihr _)).trans (capacity_split_le H w _ x)

instance queryTree_nonempty [Nonempty X] (n : Nat) : Nonempty (QueryTree X n) := by
  induction n with
  | zero => exact ⟨.leaf⟩
  | succ n ih =>
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨t⟩ := ih
    exact ⟨.node x t t⟩

/-- The recursive capacity is exactly the manuscript's supremum over all
adaptive binary query trees. The domain is nonempty under nonempty UUS. -/
theorem capacity_eq_iSup_weightedLeaves [Nonempty X] (H : HypothesisClass X)
    (w : Hypothesis X → ℝ≥0∞) (n : Nat) :
    capacity H w n = ⨆ tree : QueryTree X n, weightedLeaves H w tree := by
  apply le_antisymm
  · induction n generalizing H with
    | zero => exact le_iSup (fun tree : QueryTree X 0 => weightedLeaves H w tree) .leaf
    | succ n ih =>
      apply iSup_le
      intro x
      apply (add_le_add (ih (restrict H x false)) (ih (restrict H x true))).trans
      apply ENNReal.iSup_add_iSup_le
      intro l r
      exact le_iSup (fun tree : QueryTree X (n+1) => weightedLeaves H w tree) (.node x l r)
  · exact iSup_le (weightedLeaves_le_capacity H w)

theorem weightedLeaves_one (H : HypothesisClass X) {n : Nat} (tree : QueryTree X n) :
    weightedLeaves H (fun _ => 1) tree = (leafCount H tree : ℝ≥0∞) := by
  classical
  induction tree generalizing H with
  | leaf =>
    by_cases hh : ∃ h, H h
    · obtain ⟨h,hh⟩ := hh
      have he : (fun _ : Hypothesis X => (1 : ℝ≥0∞)) '' {h | H h} = {1} := by
        ext v
        simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨_,_,rfl⟩; rfl
        · intro hv; exact ⟨h,hh,hv.symm⟩
      simp [weightedLeaves,leafCount,he,show ∃ h, H h from ⟨h,hh⟩]
    · have he : {h | H h} = (∅ : Set (Hypothesis X)) := by ext h; simp; exact fun hh' => hh ⟨h,hh'⟩
      simp [weightedLeaves,leafCount,he,hh]
  | node x l r ihl ihr => simp only [weightedLeaves,leafCount,ihl,ihr,Nat.cast_add]

end PredictionToGeneration
