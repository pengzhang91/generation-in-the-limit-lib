import GenLimit.Core.GenericGeneration
import Mathlib.Logic.Denumerable

/-!
# Enumeration progress for infinite countable sets

This module contains the paper-independent mechanism for fixing a
repetition-free enumeration of an infinite set and measuring how far a finite
sample has progressed through that enumeration.
-/

namespace GenLimit.Support

/-- A fixed equivalence between `ℕ` and an infinite subset of a countable
type. -/
noncomputable def infiniteSetEquiv [Countable α]
    (C : Set α) (hC : C.Infinite) : ℕ ≃ C := by
  letI : Infinite C := Set.Infinite.to_subtype hC
  exact (@Denumerable.eqv C
    (Classical.choice (nonempty_denumerable C))).symm

/-- A fixed repetition-free enumeration of an infinite countable set. -/
noncomputable def infiniteEnumeration [Countable α]
    (C : Set α) (hC : C.Infinite) : ℕ → α :=
  fun k ↦ (infiniteSetEquiv C hC k).1

theorem infiniteEnumeration_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (k : ℕ) :
    infiniteEnumeration C hC k ∈ C :=
  (infiniteSetEquiv C hC k).2

theorem infiniteEnumeration_injective [Countable α]
    (C : Set α) (hC : C.Infinite) :
    Function.Injective (infiniteEnumeration C hC) := by
  intro k l hkl
  apply (infiniteSetEquiv C hC).injective
  apply Subtype.ext
  exact hkl

theorem infiniteEnumeration_surjective [Countable α]
    (C : Set α) (hC : C.Infinite) {x : α} (hx : x ∈ C) :
    ∃ k, infiniteEnumeration C hC k = x := by
  refine ⟨(infiniteSetEquiv C hC).symm ⟨x, hx⟩, ?_⟩
  simp [infiniteEnumeration]

theorem enumeration_misses_finset [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    ∃ k, infiniteEnumeration C hC k ∉ S := by
  by_contra hall
  push_neg at hall
  have hrange : Set.range (infiniteEnumeration C hC) ⊆ (↑S : Set α) := by
    rintro x ⟨k, rfl⟩
    exact hall k
  exact (Set.infinite_range_of_injective
    (infiniteEnumeration_injective C hC))
      (S.finite_toSet.subset hrange)

/-- The first enumerated point of `C` not yet present in `S`. -/
noncomputable def progress [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) : ℕ := by
  classical
  exact Nat.find (enumeration_misses_finset C hC S)

theorem progress_spec [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    infiniteEnumeration C hC (progress C hC S) ∉ S := by
  classical
  exact Nat.find_spec (enumeration_misses_finset C hC S)

theorem mem_of_lt_progress [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) {k : ℕ}
    (hk : k < progress C hC S) :
    infiniteEnumeration C hC k ∈ S := by
  classical
  unfold progress at hk
  by_contra hnot
  exact Nat.find_min (enumeration_misses_finset C hC S) hk hnot

theorem progress_le_of_not_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) {k : ℕ}
    (hk : infiniteEnumeration C hC k ∉ S) :
    progress C hC S ≤ k := by
  classical
  exact Nat.find_min' (enumeration_misses_finset C hC S) hk

end GenLimit.Support
