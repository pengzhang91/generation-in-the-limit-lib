import GenLimit.NoRegretLanguageGeneration.Capacity
import GenLimit.NoRegretLanguageGeneration.SauerBinomial

namespace PredictionToGeneration
open scoped ENNReal

theorem capacity_restrict_le (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (n : Nat) (x : X) (b : Bool) : capacity (restrict H x b) w n ≤ capacity H w (n+1) := by
  cases b
  · exact (le_add_right le_rfl).trans (capacity_split_le H w n x)
  · exact (le_add_left le_rfl).trans (capacity_split_le H w n x)

theorem capacity_partition_le (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (n : Nat) (x : X) :
    capacity H w n ≤ capacity (restrict H x false) w n + capacity (restrict H x true) w n := by
  have he : H = (fun h => restrict H x false h ∨ restrict H x true h) := by
    funext h; apply propext; cases hx : h x <;> simp [restrict, hx]
  conv_lhs => rw [he]
  exact capacity_union_le _ _ w n

theorem capacity_restrict_comm (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (n : Nat) (x z : X) (a b : Bool) :
    capacity (restrict (restrict H x a) z b) w n =
      capacity (restrict (restrict H z b) x a) w n := by
  apply capacity_congr (hw := fun _ _ => rfl)
  intro h
  simp [restrict, and_assoc, and_comm, and_left_comm]

/-- Weighted-capacity version of the sequential Sauer bound. -/
theorem capacity_sauer (H : HypothesisClass X) (d : Nat) (hd : LdimLE H d) (n : Nat) :
    capacity H (fun _ => 1) n ≤ (sauer n d : ℝ≥0∞) := by
  induction n generalizing H d with
  | zero =>
    apply sSup_le
    rintro _ ⟨h, _, rfl⟩
    simp [sauer]
  | succ n ih =>
    apply iSup_le
    intro x
    have h0 := ldimLE_restrict H d hd x false
    have h1 := ldimLE_restrict H d hd x true
    cases d with
    | zero =>
      have sn : sauer n 0 = 1 := by cases n <;> rfl
      by_cases he : ∃ h, restrict H x false h
      · have empty1 : ∀ h, ¬ restrict H x true h := by
          intro h hh
          exact hd ⟨x, he, ⟨h, hh⟩⟩
        rw [capacity_empty _ _ empty1]
        simpa [sn, sauer] using ih _ 0 h0
      · have empty0 : ∀ h, ¬ restrict H x false h := fun h hh => he ⟨h, hh⟩
        rw [capacity_empty _ _ empty0]
        simpa [sn, sauer] using ih _ 0 h1
    | succ d =>
      obtain hl | hr := dimension_drop H d hd x
      · have ht := add_le_add (ih _ d hl) (ih _ (d+1) h1)
        simpa [sauer, Nat.cast_add, add_comm] using ht
      · have ht := add_le_add (ih _ (d+1) h0) (ih _ d hr)
        simpa [sauer, Nat.cast_add] using ht

theorem capacity_sauer_binomial (H : HypothesisClass X) (d : Nat) (hd : LdimLE H d) (n : Nat) :
    capacity H (fun _ => 1) n ≤
      ((∑ i ∈ Finset.range (min d n + 1), n.choose i : Nat) : ℝ≥0∞) := by
  rw [← sauer_eq_truncated_choose]
  exact capacity_sauer H d hd n

/-- Nonnegative weighted form of `lem:app-realizable-capacity`. -/
theorem capacity_realizable_update (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (n : Nat) (z x : X)
    (hmax : capacity (restrict H x true) w (n+1) ≤ capacity (restrict H z true) w (n+1)) :
    capacity (restrict H x true) (fun h => if h z then w h else 2 * w h) n ≤ capacity H w (n+2) := by
  let A := restrict (restrict H x true) z false
  let B := restrict (restrict H x true) z true
  have ha : capacity A (fun h => if h z then w h else 2 * w h) n = 2 * capacity A w n := by
    rw [← capacity_homogeneous A w 2 n]
    apply capacity_congr (fun _ => Iff.rfl)
    intro h hh
    simp [show h z = false from hh.2]
  have hb : capacity B (fun h => if h z then w h else 2 * w h) n = capacity B w n := by
    apply capacity_congr (fun _ => Iff.rfl)
    intro h hh
    simp [show h z = true from hh.2]
  have hu : capacity (restrict H x true) (fun h => if h z then w h else 2*w h) n ≤
      2 * capacity A w n + capacity B w n := by
    have ht := capacity_partition_le (restrict H x true) (fun h => if h z then w h else 2*w h) n z
    change _ ≤ capacity A _ n + capacity B _ n at ht
    rwa [ha, hb] at ht
  have hleft : capacity A w n ≤ capacity (restrict H z false) w (n+1) := by
    dsimp [A]
    rw [capacity_restrict_comm]
    exact capacity_restrict_le _ _ n x true
  have hright : capacity A w n + capacity B w n ≤ capacity (restrict H z true) w (n+1) :=
    (capacity_split_le (restrict H x true) w n z).trans hmax
  apply hu.trans
  calc
    _ = capacity A w n + (capacity A w n + capacity B w n) := by rw [two_mul, add_assoc]
    _ ≤ _ := add_le_add hleft hright
    _ ≤ capacity H w (n+2) := capacity_split_le H w (n+1) z

end PredictionToGeneration

