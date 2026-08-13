import GenLimit.Support.EnumerationProgress

/-!
# Enumeration progress for #02 Learning Theory

Compatibility wrappers for the paper-independent enumeration-progress
mechanism in `GenLimit.Support`.
-/

namespace GenLimit.LiRamanTewari.Common

/-- A fixed equivalence between `ℕ` and an infinite subset of a countable
example space. -/
noncomputable def infiniteSetEquiv [Countable α]
    (C : Set α) (hC : C.Infinite) : ℕ ≃ C :=
  GenLimit.Support.infiniteSetEquiv C hC

/-- A fixed repetition-free enumeration of an infinite countable set. -/
noncomputable def infiniteEnumeration [Countable α]
    (C : Set α) (hC : C.Infinite) : ℕ → α :=
  GenLimit.Support.infiniteEnumeration C hC

theorem infiniteEnumeration_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (k : ℕ) :
    infiniteEnumeration C hC k ∈ C :=
  GenLimit.Support.infiniteEnumeration_mem C hC k

theorem infiniteEnumeration_injective [Countable α]
    (C : Set α) (hC : C.Infinite) :
    Function.Injective (infiniteEnumeration C hC) :=
  GenLimit.Support.infiniteEnumeration_injective C hC

theorem infiniteEnumeration_surjective [Countable α]
    (C : Set α) (hC : C.Infinite) {x : α} (hx : x ∈ C) :
    ∃ k, infiniteEnumeration C hC k = x :=
  GenLimit.Support.infiniteEnumeration_surjective C hC hx

theorem enumeration_misses_finset [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    ∃ k, infiniteEnumeration C hC k ∉ S :=
  GenLimit.Support.enumeration_misses_finset C hC S

/-- The first enumerated point of `C` not yet present in `S`. -/
noncomputable def progress [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) : ℕ :=
  GenLimit.Support.progress C hC S

theorem progress_spec [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    infiniteEnumeration C hC (progress C hC S) ∉ S :=
  GenLimit.Support.progress_spec C hC S

theorem progress_le_of_not_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) {k : ℕ}
    (hk : infiniteEnumeration C hC k ∉ S) :
    progress C hC S ≤ k :=
  GenLimit.Support.progress_le_of_not_mem C hC S hk

end GenLimit.LiRamanTewari.Common
