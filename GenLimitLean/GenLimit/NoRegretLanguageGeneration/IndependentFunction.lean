import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace PredictionToGeneration
open Classical

private theorem functional_independent_extend (f : Nat → Nat)
    (hf : ∀ y, Set.Finite {x | f x = y}) (F : Finset Nat) :
    ∃ x, x ∉ F ∧ ∀ y ∈ F, f x ≠ y ∧ f y ≠ x := by
  let bad : Set Nat := (F : Set Nat) ∪ f '' (F : Set Nat) ∪ ⋃ y ∈ (F : Set Nat), {x | f x = y}
  have hbad : bad.Finite := (F.finite_toSet.union (F.finite_toSet.image f)).union
    (F.finite_toSet.biUnion (fun y _ => hf y))
  obtain ⟨x, hx⟩ := hbad.exists_notMem
  refine ⟨x, ?_, ?_⟩
  · intro hm
    exact hx (Or.inl (Or.inl hm))
  · intro y hy
    constructor
    · intro he
      apply hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, he⟩⟩)
    · intro he
      exact hx (Or.inl (Or.inr ⟨y, hy, he⟩))

private noncomputable def independentStage (f : Nat → Nat)
    (hf : ∀ y, Set.Finite {x | f x = y}) : Nat → Finset Nat
  | 0 => ∅
  | n+1 => insert (Classical.choose (functional_independent_extend f hf (independentStage f hf n)))
      (independentStage f hf n)

private theorem independentStage_subset (f : Nat → Nat)
    (hf : ∀ y, Set.Finite {x | f x = y}) {i j : Nat} (hij : i ≤ j) :
    independentStage f hf i ⊆ independentStage f hf j := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | @step j hij ih => exact ih.trans (Finset.subset_insert _ _)

private theorem independentStage_card (f : Nat → Nat)
    (hf : ∀ y, Set.Finite {x | f x = y}) (n : Nat) :
    (independentStage f hf n).card = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [independentStage, Finset.card_insert_of_notMem
      (Classical.choose_spec (functional_independent_extend f hf (independentStage f hf n))).1, ih]

private theorem independentStage_independent (f : Nat → Nat)
    (hf : ∀ y, Set.Finite {x | f x = y}) (n : Nat) :
    ∀ x ∈ independentStage f hf n, ∀ y ∈ independentStage f hf n, x ≠ y → f x ≠ y := by
  induction n with
  | zero => simp [independentStage]
  | succ n ih =>
    let z := Classical.choose (functional_independent_extend f hf (independentStage f hf n))
    have hz := (Classical.choose_spec (functional_independent_extend f hf (independentStage f hf n))).2
    intro x hx y hy hxy
    change x ∈ insert z _ at hx
    change y ∈ insert z _ at hy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact False.elim (hxy rfl)
    · exact (hz y hy).1
    · exact (hz x hx).2
    · exact ih x hx y hy hxy

/-- Every functional directed graph on N has an infinite independent set.
This avoids any assumption that the class of targets is countable. -/
theorem infinite_independent_for_function (f : Nat → Nat) :
    ∃ S : Set Nat, S.Infinite ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x ≠ y := by
  classical
  by_cases hf : ∀ y, Set.Finite {x | f x = y}
  · let S : Set Nat := {x | ∃ n, x ∈ independentStage f hf n}
    have hinf : S.Infinite := by
      intro hs
      let N := hs.toFinset.card + 1
      have hsub : independentStage f hf N ⊆ hs.toFinset := by
        intro x hx
        exact hs.mem_toFinset.mpr ⟨N, hx⟩
      have hcard := Finset.card_le_card hsub
      rw [independentStage_card] at hcard
      dsimp [N] at hcard
      omega
    refine ⟨S, hinf, ?_⟩
    rintro x ⟨i, hi⟩ y ⟨j, hj⟩ hxy
    exact independentStage_independent f hf (max i j) x
      (independentStage_subset f hf (Nat.le_max_left _ _) hi) y
      (independentStage_subset f hf (Nat.le_max_right _ _) hj) hxy
  · push_neg at hf
    obtain ⟨y, hy⟩ := hf
    have hy' : Set.Infinite {x | f x = y} := hy
    refine ⟨{x | f x = y} \ {y}, hy'.diff (Set.finite_singleton y), ?_⟩
    intro x hx z hz _ he
    have hfx : f x = y := hx.1
    exact hz.2 (by simpa using he.symm.trans hfx)

end PredictionToGeneration
