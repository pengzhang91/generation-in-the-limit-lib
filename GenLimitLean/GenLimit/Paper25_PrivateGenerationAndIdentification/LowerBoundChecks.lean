import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum

/-! Checks on the scope of the sample-complexity lower bound in Theorem 1.3
and the use of the Sperner family after equation (6) in Appendix C.2. -/

namespace GenLimit.PrivateLimit

/-- Every subcollection of a singleton infinite language has infinite closure.
Definition 2 therefore assigns the singleton closure dimension −1. -/
theorem singleton_all_closures_infinite {X : Type*} {L : Set X} (infinite : L.Infinite)
    (S : Set (Set X)) (sub : S ⊆ {L}) : (⋂₀ S).Infinite := by
  apply infinite.mono
  intro x hx
  apply Set.mem_sInter.mpr
  intro K hK
  exact (Set.mem_singleton_iff.mp (sub hK)) ▸ hx

/-- In the paper's k = 6 family the observed column is {0,1,2}. Release one
of the three columns obtained by replacing element j with 3, uniformly in j.
Each column denotes infinitely many fresh words in the source construction. -/
private def replacementColumn (j : Fin 3) : Finset (Fin 6) :=
  insert 3 (Finset.univ.filter fun i : Fin 6 => i.val < 3 ∧ i.val ≠ j.val)

/-- Of three equiprobable outcomes, exactly two are valid for each possible
target and zero are valid for all targets. Each released column is itself
a 3-subset of the six indices, as required by the actual hard family. -/
theorem sperner_marginals_do_not_bound_intersection :
    (∀ j, (replacementColumn j).card = 3) ∧
    (∀ i : Fin 3, (Finset.univ.filter fun j : Fin 3 =>
      (⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ : Fin 6) ∈ replacementColumn j).card = 2) ∧
    (Finset.univ.filter fun j : Fin 3 => ∀ i : Fin 3,
      (⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ : Fin 6) ∈ replacementColumn j).card = 0 := by
  decide

end GenLimit.PrivateLimit
