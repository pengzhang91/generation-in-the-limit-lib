import Mathlib.Data.Set.Countable

/-!
# Countable-universe cardinality helpers

Paper-independent Cantor diagonal facts used to certify that classes
parameterized by arbitrary subsets of an infinite countable type are
uncountable.
-/

namespace GenLimit.Support

/-- The powerset of an infinite countable type is not countable. -/
theorem powerSet_not_countable (beta : Type*)
    [Infinite beta] [Countable beta] :
    ¬Countable (Set beta) := by
  intro hcountable
  letI : Countable (Set beta) := hcountable
  let den : Denumerable beta :=
    Classical.choice (nonempty_denumerable beta)
  let e : ℕ ≃ beta := (@Denumerable.eqv beta den).symm
  obtain ⟨f, hf⟩ :=
    (countable_iff_exists_surjective (α := Set beta)).mp hcountable
  let diagonal : Set beta := {p | p ∉ f (e.symm p)}
  obtain ⟨n, hn⟩ := hf diagonal
  let p : beta := e n
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

end GenLimit.Support
