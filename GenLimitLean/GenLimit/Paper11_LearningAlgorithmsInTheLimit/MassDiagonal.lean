import GenLimit.Paper11_LearningAlgorithmsInTheLimit.CharacteristicSets
import Mathlib.Computability.PartrecCode

/-! # Characteristic data must pay for the length of observed outputs
Definition 8 charges the length of each full input/output/side-information
example. Kleene's recursion theorem gives a constant-valued teacher whose
output length exceeds a proposed bound on its characteristic data. Its
output also differs from the fixed empty-data guess. This argument applies
to arbitrary side information and uses only total constant-valued teachers. -/
namespace GenLimit.LearningAlgorithmsLimit.MassDiagonal
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- The fixed point prints a word longer than the proposed budget for its
own representation. The second summand can exceed the empty-data guess. -/
theorem constant_fixed_point (β : Code → ℕ) (hb : Computable β) (pad : ℕ) :
    ∃ c : Code, ∀ x, eval c x = Part.some (β c + pad + 1) := by
  let f (c : Code) := Code.const (β c + pad + 1)
  have hf : Computable f :=
    primrec_const.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp hb (Computable.const pad)) (Computable.const 1))
  obtain ⟨c,h⟩ := fixed_point hf
  exact ⟨c,fun x ↦ (congrFun h x).symm.trans (eval_const _ _)⟩

/-- It suffices to embed programs that are constant on all inputs. The
budget is computed on the concrete representation sent to the learner. -/
theorem no_bound_of_compiler [Nonempty X] (compile : Code → M) (β : M → ℕ)
    (hb : Computable (fun c ↦ β (compile c))) (size : Y → ℕ)
    (sem : M → X → Option Y)
    (realizes : ∀ c n, (∀ x, eval c x = Part.some n) → ∃ y,
      n ≤ size y ∧ ∀ x, sem (compile c) x = some y)
    (rep : R → X → Option Y) (A : Set (X × O) → R) (obs : M → X → O) :
    ¬ (∀ c n, (∀ x, eval c x = Part.some n) → ∃ S : Finset X,
      IsCharacteristicSet A obs sem rep Set.univ (compile c) (↑S : Set X) ∧
      ∀ x ∈ S, ∀ y, sem (compile c) x = some y → size y ≤ β (compile c)) := by
  classical
  intro all
  let x₀ : X := Classical.choice inferInstance
  let guess := rep (A ∅) x₀
  let pad := (guess.map size).getD 0
  obtain ⟨c,hc⟩ := constant_fixed_point _ hb pad
  obtain ⟨y,hy,hval⟩ := realizes _ _ hc
  obtain ⟨S,hS,hbudget⟩ := all _ _ hc
  by_cases hn : S.Nonempty
  · obtain ⟨x,hx⟩ := hn
    have := hbudget x hx y (hval x)
    omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    subst S
    have hh := hS.2 ∅ (by simp) (Set.empty_subset _) x₀ (Set.mem_univ _)
    have hg : guess = some y := by simpa [guess,exampleSet,hval] using hh
    have : pad = size y := by simp [pad,hg]
    omega

/-- Partial recursive program codes, interpreted with unary word output.
No restriction is placed on the side information provided to the learner. -/
noncomputable def unarySem (c : Code) (x : ℕ) : Option (List Unit) := by
  classical
  exact (eval c x).toOption.map (fun n ↦ List.replicate n ())

theorem no_computable_mass_bound (β : Code → ℕ) (hb : Computable β)
    (A : Set (ℕ × O) → R) (rep : R → ℕ → Option (List Unit)) (obs : Code → ℕ → O)
    (cost : Code → ℕ → ℕ) (pays : ∀ c x y, unarySem c x = some y → y.length ≤ cost c x) :
    ¬ (∀ c n, (∀ x, eval c x = Part.some n) → ∃ S : Finset ℕ,
      IsCharacteristicSet A obs unarySem rep Set.univ c (↑S : Set ℕ) ∧
      ∑ x ∈ S, cost c x ≤ β c) := by
  apply fun h ↦ no_bound_of_compiler id β hb List.length unarySem (by
    intro c n hc
    exact ⟨List.replicate n (),by simp,fun x ↦ by simp [unarySem,hc]⟩) rep A obs ?_
  intro c n hc
  obtain ⟨S,hS,hm⟩ := h c n hc
  exact ⟨S,hS,fun x hx y hy ↦ (pays c x y hy).trans
    ((Finset.single_le_sum (fun i _ ↦ Nat.zero_le (cost c i)) hx).trans hm)⟩

end GenLimit.LearningAlgorithmsLimit.MassDiagonal
