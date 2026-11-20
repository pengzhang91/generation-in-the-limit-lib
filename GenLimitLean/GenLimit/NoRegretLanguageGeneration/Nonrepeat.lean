import GenLimit.NoRegretLanguageGeneration.Blocks

namespace PredictionToGeneration
open Classical

private noncomputable def freshOutside [Infinite X] (xs : List X) : X :=
  Classical.choose (Finset.exists_notMem xs.toFinset)

private theorem freshOutside_spec [Infinite X] (xs : List X) : freshOutside xs ∉ xs := by
  simpa [freshOutside] using Classical.choose_spec (Finset.exists_notMem xs.toFinset)

private noncomputable def nonrepeatOutputs [Infinite X] : List X → List X
  | [] => []
  | _::xs => freshOutside (xs ++ nonrepeatOutputs xs) :: nonrepeatOutputs xs

/-- A strongly total generator avoiding both earlier demonstrations and earlier outputs. -/
noncomputable def nonrepeatGenerator (X : Type) [Infinite X] : Generator X where
  output xs := freshOutside (xs ++ nonrepeatOutputs xs)
  fresh xs := by
    have := freshOutside_spec (xs ++ nonrepeatOutputs xs)
    simp only [List.mem_append, not_or] at this
    exact this.1

private theorem nonrepeatOutputs_nodup [Infinite X] (xs : List X) :
    (nonrepeatOutputs xs).Nodup := by
  induction xs with
  | nil => simp [nonrepeatOutputs]
  | cons x xs ih =>
    have hf := freshOutside_spec (xs ++ nonrepeatOutputs xs)
    simp only [List.mem_append, not_or] at hf
    exact List.nodup_cons.mpr ⟨hf.2, ih⟩

theorem nonrepeatGenerator_outputs (X : Type) [Infinite X] (xs : List X) :
    (((nonrepeatGenerator X).play xs).map Prod.fst).Nodup := by
  have he : ((nonrepeatGenerator X).play xs).map Prod.fst = nonrepeatOutputs xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change _ :: (((nonrepeatGenerator X).play xs).map Prod.fst) = _ :: nonrepeatOutputs xs
      rw [ih]
      rfl
  rw [he]
  exact nonrepeatOutputs_nodup xs

theorem cofinite_mistakes_filter (R : Finset X) (τ : Trajectory X) :
    mistakes (Blocks.cofiniteHypothesis R) τ =
      ((τ.map Prod.fst).filter (fun x => decide (x ∈ R))).length := by
  classical
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    by_cases hp : p.1 ∈ R <;>
      simp [mistakes, loss, Blocks.cofiniteHypothesis, hp, ih, Nat.add_comm]

/-- Distinct outputs incur at most one mistake per invalid point. -/
theorem cofinite_mistakes_le_card (R : Finset X) (τ : Trajectory X)
    (hn : (τ.map Prod.fst).Nodup) : mistakes (Blocks.cofiniteHypothesis R) τ ≤ R.card := by
  classical
  rw [cofinite_mistakes_filter]
  have hd := hn.filter (fun x => decide (x ∈ R))
  rw [← List.toFinset_card_of_nodup hd]
  apply Finset.card_le_card
  intro x hx
  simpa using (List.mem_filter.mp (List.mem_toFinset.mp hx)).2

theorem nonrepeatGenerator_cofinite_bound (X : Type) [Infinite X] (R : Finset X) (xs : List X) :
    mistakes (Blocks.cofiniteHypothesis R) ((nonrepeatGenerator X).play xs) ≤ R.card :=
  cofinite_mistakes_le_card R _ (nonrepeatGenerator_outputs X xs)

end PredictionToGeneration
