import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.RepresentativeInsertion
import Mathlib.Data.List.Sort

/-! # The Section 5 representative scan
A compatible language enters exactly when all selected languages share a
common fresh representative distribution. Before a due target, sortedness
ensures that every selected index has also passed its deadline. -/
namespace GenLimit.ParetoGeneration.Representative
open RepresentativeGeneration
open scoped ENNReal
variable {α : Type*} [DecidableEq α]

def accepts (F : ℕ → Set α) (g : ℕ → Set α) (ε : ℝ) (S : Finset α)
    (W : Finset ℕ) (j : ℕ) : Prop :=
  (↑S : Set α) ⊆ F j ∧ Feasible F g ε S (insert j W)

/-- Process older indices in the order resulting from the previous
insertion. A new coordinate precedes older coordinates with the same score. -/
def scoreOrder (d : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n+1 => (scoreOrder d n).orderedInsert (fun a b ↦ d a ≤ d b) n

theorem mem_scoreOrder (d : ℕ → ℕ) (n i : ℕ) : i ∈ scoreOrder d n ↔ i < n := by
  induction n with
  | zero => simp [scoreOrder]
  | succ n ih => rw [scoreOrder,List.mem_orderedInsert,ih]; omega

theorem sorted_scoreOrder (d : ℕ → ℕ) (n : ℕ) :
    (scoreOrder d n).Pairwise (fun a b ↦ d a ≤ d b) := by
  let r : ℕ → ℕ → Prop := fun a b ↦ d a ≤ d b
  letI : IsTrans ℕ r := ⟨fun _ _ _ ↦ Nat.le_trans⟩
  letI : IsTotal ℕ r := ⟨fun a b ↦ Nat.le_total (d a) (d b)⟩
  induction n with
  | zero => simp [scoreOrder]
  | succ n ih => exact List.Sorted.orderedInsert (r := r) n _ ih

theorem scan_includes_due (F : ℕ → Set α) (g : ℕ → Set α) (ε : ℝ)
    (hb : BoundedObstructions F g ε) (S : Finset α) (hs : S.Nonempty) (i : ℕ)
    (ht : complexity F g ε i < S.card) (hc : (↑S : Set α) ⊆ F i) (l : List ℕ)
    (hl : l.Pairwise (fun a b ↦ complexity F g ε a ≤ complexity F g ε b)) (hi : i ∈ l)
    (W : Finset ℕ) (hw : ∀ j ∈ W, complexity F g ε j < S.card ∧ (↑S : Set α) ⊆ F j) :
    i ∈ greedyListScanBy (accepts F g ε S) W l := by
  classical
  induction l generalizing W with
  | nil => simp at hi
  | cons a l ih =>
    obtain ⟨hfirst,hrest⟩ := List.pairwise_cons.mp hl
    rcases List.mem_cons.mp hi with he | hmem
    · subst a
      have hacc : accepts F g ε S W i := ⟨hc,feasible_due F g ε hb S hs _ (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨ht,hc⟩
        · exact hw j hj)⟩
      simp only [greedyListScanBy,greedyListStepBy,if_pos hacc]
      exact greedyListScanBy_initial_subset _ _ _ (Finset.mem_insert_self _ _)
    · apply ih hrest hmem
      intro j hj
      unfold greedyListStepBy at hj
      split at hj
      next ha =>
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨(hfirst i hmem).trans_lt ht,ha.1⟩
        · exact hw j hj
      next => exact hw j hj

/-- All selected languages stay compatible and the final set admits a common output. -/
theorem scan_valid (F : ℕ → Set α) (g : ℕ → Set α) (ε : ℝ) (S : Finset α)
    (hs : S.Nonempty) (l : List ℕ) :
    let W := greedyListScanBy (accepts F g ε S) ∅ l
    Feasible F g ε S W ∧ ∀ j ∈ W, (↑S : Set α) ⊆ F j := by
  classical
  apply greedyListScanBy_invariant (accepts F g ε S)
    (fun W ↦ Feasible F g ε S W ∧ ∀ j ∈ W, (↑S : Set α) ⊆ F j)
  · intro W i h
    unfold greedyListStepBy
    split
    next ha =>
      exact ⟨ha.2,fun j hj ↦ (Finset.mem_insert.mp hj).elim (fun he ↦ he ▸ ha.1) (h.2 j)⟩
    next => exact h
  · exact ⟨⟨empiricalPointDistribution S hs,by rw [empiricalPointDistribution_distance_zero]; exact bot_le,
      by simp⟩,by simp⟩

end GenLimit.ParetoGeneration.Representative
