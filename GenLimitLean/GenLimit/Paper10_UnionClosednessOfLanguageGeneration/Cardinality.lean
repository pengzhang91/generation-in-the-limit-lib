import GenLimit.Support.Uncountability

/-!
# Cardinality helpers for the Union-Closedness constructions

The constructions supporting overview Theorem 3.1 and detailed Theorem 4.3
both encode an arbitrary subset of a countably infinite one-sided universe.
This module isolates the shared Cantor diagonal used to turn those encodings
into uncountability proofs.
-/

namespace GenLimit.UnionClosedness

/-- The powerset of an infinite countable type is not countable.  This
elementary diagonal form avoids adding a cardinal-arithmetic dependency to
the paper-facing modules. -/
theorem powerSet_not_countable (β : Type*)
    [Infinite β] [Countable β] :
    ¬Countable (Set β) :=
  GenLimit.Support.powerSet_not_countable β

end GenLimit.UnionClosedness
