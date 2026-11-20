import GenLimit.NoRegretLanguageGeneration.Littlestone
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finite.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Weighted sequential capacity. The extended nonnegative reals make empty
suprema zero and permit the recursion before proving boundedness. -/

namespace PredictionToGeneration

open scoped ENNReal

noncomputable def capacity (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞) : Nat → ℝ≥0∞
  | 0 => sSup (w '' {h | H h})
  | n + 1 => ⨆ x : X, capacity (restrict H x false) w n + capacity (restrict H x true) w n

theorem capacity_zero_le (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (h : Hypothesis X) (hh : H h) : w h ≤ capacity H w 0 :=
  le_sSup ⟨h, hh, rfl⟩

theorem capacity_split_le (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (n : Nat) (x : X) :
    capacity (restrict H x false) w n + capacity (restrict H x true) w n ≤ capacity H w (n+1) :=
  le_iSup (fun x => capacity (restrict H x false) w n + capacity (restrict H x true) w n) x

theorem capacity_mono {H K : HypothesisClass X} {w v : Hypothesis X → ℝ≥0∞}
    (hsub : ∀ h, H h → K h) (hw : ∀ h, H h → w h ≤ v h) (n : Nat) :
    capacity H w n ≤ capacity K v n := by
  induction n generalizing H K with
  | zero =>
    apply sSup_le
    rintro _ ⟨h, hh, rfl⟩
    exact (hw h hh).trans (capacity_zero_le K v h (hsub h hh))
  | succ n ih =>
    apply iSup_le
    intro x
    apply le_trans _ (capacity_split_le K v n x)
    exact add_le_add (ih (fun h hh => ⟨hsub h hh.1, hh.2⟩) (fun h hh => hw h hh.1))
      (ih (fun h hh => ⟨hsub h hh.1, hh.2⟩) (fun h hh => hw h hh.1))

theorem capacity_congr {H K : HypothesisClass X} {w v : Hypothesis X → ℝ≥0∞}
    (hHK : ∀ h, H h ↔ K h) (hw : ∀ h, H h → w h = v h) (n : Nat) :
    capacity H w n = capacity K v n := by
  apply le_antisymm
  · exact capacity_mono (fun h => (hHK h).mp) (fun h hh => (hw h hh).le) n
  · exact capacity_mono (fun h => (hHK h).mpr)
      (fun h hh => (hw h ((hHK h).mpr hh)).ge) n

theorem capacity_empty (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (he : ∀ h, ¬ H h) (n : Nat) : capacity H w n = 0 := by
  induction n generalizing H with
  | zero =>
    have hs : {h | H h} = (∅ : Set (Hypothesis X)) := by ext h; simp [he h]
    simp [capacity, hs]
  | succ n ih =>
    simp only [capacity]
    have h0 : ∀ x, capacity (restrict H x false) w n = 0 :=
      fun x => ih _ (fun h hh => he h hh.1)
    have h1 : ∀ x, capacity (restrict H x true) w n = 0 :=
      fun x => ih _ (fun h hh => he h hh.1)
    simp [h0, h1]

theorem capacity_homogeneous (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (c : ℝ≥0∞) (n : Nat) : capacity H (fun h => c * w h) n = c * capacity H w n := by
  induction n generalizing H with
  | zero => simp only [capacity, sSup_image, ENNReal.mul_iSup]
  | succ n ih => simp only [capacity, ih, mul_add, ENNReal.mul_iSup]

theorem capacity_union_le (H K : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞) (n : Nat) :
    capacity (fun h => H h ∨ K h) w n ≤ capacity H w n + capacity K w n := by
  induction n generalizing H K with
  | zero =>
    apply sSup_le
    rintro _ ⟨h, hh | hh, rfl⟩
    · exact (capacity_zero_le H w h hh).trans (le_add_right le_rfl)
    · exact (capacity_zero_le K w h hh).trans (le_add_left le_rfl)
  | succ n ih =>
    apply iSup_le
    intro x
    have hsplit (b : Bool) : restrict (fun h => H h ∨ K h) x b =
        (fun h => restrict H x b h ∨ restrict K x b h) := by
      funext h; apply propext; simp [restrict, or_and_right]
    rw [hsplit false, hsplit true]
    calc
      _ ≤ (capacity (restrict H x false) w n + capacity (restrict K x false) w n) +
          (capacity (restrict H x true) w n + capacity (restrict K x true) w n) :=
        add_le_add (ih _ _) (ih _ _)
      _ = (capacity (restrict H x false) w n + capacity (restrict H x true) w n) +
          (capacity (restrict K x false) w n + capacity (restrict K x true) w n) := by simp only [add_assoc, add_left_comm]
      _ ≤ _ := add_le_add (capacity_split_le H w n x) (capacity_split_le K w n x)

private theorem sSup_in_palette {s p : Set ℝ≥0∞} (hp : p.Finite) (hsub : s ⊆ p) :
    sSup s ∈ insert 0 p := by
  by_cases hs : s.Nonempty
  · exact Set.mem_insert_of_mem _ (hsub (hs.csSup_mem (hp.subset hsub)))
  · have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    simp [he]

/-- Finite-range weights give finitely many capacity values at each depth,
even as the hypothesis class ranges over all subclasses. -/
theorem capacity_finite_range (w : Hypothesis X → ℝ≥0∞) (hw : (Set.range w).Finite)
    (n : Nat) : (Set.range (fun H : HypothesisClass X => capacity H w n)).Finite := by
  induction n with
  | zero =>
    apply (hw.insert 0).subset
    rintro _ ⟨H, rfl⟩
    apply sSup_in_palette hw
    rintro _ ⟨h, _, rfl⟩
    exact ⟨h, rfl⟩
  | succ n ih =>
    let p : Set ℝ≥0∞ := (fun t : ℝ≥0∞ × ℝ≥0∞ => t.1 + t.2) ''
      (Set.range (fun H : HypothesisClass X => capacity H w n) ×ˢ
        Set.range (fun H : HypothesisClass X => capacity H w n))
    have hp : p.Finite := (ih.prod ih).image _
    apply (hp.insert 0).subset
    rintro _ ⟨H, rfl⟩
    apply sSup_in_palette hp
    rintro _ ⟨x, rfl⟩
    exact ⟨(_, _), ⟨⟨restrict H x false, rfl⟩, ⟨restrict H x true, rfl⟩⟩, rfl⟩

/-- The argmax used by the manuscript exists on every nonempty legal-output set. -/
theorem capacity_maximizer (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (hw : (Set.range w).Finite) (n : Nat) (D : Set X) (hD : D.Nonempty) :
    ∃ z ∈ D, ∀ x ∈ D, capacity (restrict H x true) w n ≤ capacity (restrict H z true) w n := by
  let f : X → ℝ≥0∞ := fun x => capacity (restrict H x true) w n
  have hf : (f '' D).Finite := (capacity_finite_range w hw n).subset (by
    rintro _ ⟨x, _, rfl⟩; exact ⟨restrict H x true, rfl⟩)
  have hn : (f '' D).Nonempty := hD.image f
  obtain ⟨z, hz, heq⟩ := hn.csSup_mem hf
  refine ⟨z, hz, ?_⟩
  intro x hx
  change f x ≤ f z
  rw [heq]
  exact le_sSup ⟨x, hx, rfl⟩

end PredictionToGeneration




