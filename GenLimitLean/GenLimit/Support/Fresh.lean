import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Countable

/-!
# Fresh selection from infinite sets

One paper-independent choice used throughout generation proofs: an infinite
set contains a point outside every finite set.
-/

namespace GenLimit.Support

/-- Choose a point of an infinite set outside a finite forbidden set. -/
noncomputable def freshFromInfinite
    (C : Set α) (hC : C.Infinite) (seen : Finset α) : α :=
  Classical.choose (hC.diff seen.finite_toSet).nonempty

theorem freshFromInfinite_mem
    (C : Set α) (hC : C.Infinite) (seen : Finset α) :
    freshFromInfinite C hC seen ∈ C :=
  (Classical.choose_spec (hC.diff seen.finite_toSet).nonempty).1

theorem freshFromInfinite_not_mem
    (C : Set α) (hC : C.Infinite) (seen : Finset α) :
    freshFromInfinite C hC seen ∉ seen :=
  (Classical.choose_spec (hC.diff seen.finite_toSet).nonempty).2

end GenLimit.Support
