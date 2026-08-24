import Mathlib.Data.Set.Countable

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
    ¬Countable (Set β) := by
  intro hcountable
  letI : Countable (Set β) := hcountable
  let den : Denumerable β :=
    Classical.choice (nonempty_denumerable β)
  let e : ℕ ≃ β := (@Denumerable.eqv β den).symm
  obtain ⟨f, hf⟩ :=
    (countable_iff_exists_surjective (α := Set β)).mp hcountable
  let diagonal : Set β := {p | p ∉ f (e.symm p)}
  obtain ⟨n, hn⟩ := hf diagonal
  let p : β := e n
  have hdiag : p ∈ diagonal ↔ p ∉ diagonal := by
    have hep : e.symm p = n := by simp [p]
    constructor
    · intro hp
      change p ∉ f (e.symm p) at hp
      rw [hep, hn] at hp
      exact hp
    · intro hp
      change p ∉ f (e.symm p)
      rw [hep, hn]
      exact hp
  by_cases hp : p ∈ diagonal
  · exact (hdiag.mp hp) hp
  · exact hp (hdiag.mpr hp)

end GenLimit.UnionClosedness
