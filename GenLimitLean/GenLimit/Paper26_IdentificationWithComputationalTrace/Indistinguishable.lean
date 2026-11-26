import GenLimit.Paper00_LanguageIdentification.Text.Superfinite
import Mathlib.Data.Finset.Lattice.Fold

/-! # A common corrupted trace for a chain of target machines

A finite initial segment and its infinite union can have the same noisy
observation on every input they share. Pulling hypotheses back to the example
indices then gives a positive-text learner ruled out by Gold's locking theorem.
-/
namespace GenLimit.ComputationalTrace

def extent : Option ℕ → Set ℕ
  | none => Set.univ
  | some i => Set.Iic i

theorem common_noise_obstruction {X C H : Type*}
    (word : ℕ → X) (noise : ℕ → C) (denote : H → Set X)
    (learner : List (X × C) → H) :
    ¬ (∀ (i : Option ℕ) (s : ℕ → ℕ), Set.range s = extent i →
      ∃ g : H, (∀ n, word n ∈ denote g ↔ n ∈ extent i) ∧
        ∃ T, ∀ t ≥ T, learner (textPrefix (fun j => (word (s j),noise (s j))) t) = g) := by
  intro h
  let F : Set Language := Set.range extent
  let project : Gold.Text.TextLearner Language := fun xs =>
    word ⁻¹' denote (learner (xs.map fun n => (word n, noise n)))
  have hp : Gold.Text.SemanticallyIdentifiesClass project F := by
    rintro _ ⟨i,rfl⟩ s hs
    obtain ⟨g,hg,T,hT⟩ := h i s hs
    refine ⟨extent i, rfl, T, fun t ht => ?_⟩
    have hmap : (textPrefix s t).map (fun n => (word n,noise n)) =
        textPrefix (fun j => (word (s j),noise (s j))) t := by simp [textPrefix,Function.comp_def]
    ext n
    change word n ∈ denote (learner ((textPrefix s t).map _)) ↔ _
    rw [hmap,hT t ht]
    exact hg n
  have hu : Set.univ ∈ F := ⟨none,rfl⟩
  obtain ⟨D,hD⟩ := Gold.Text.finite_tellTale_of_semantic_identification hp hu Set.infinite_univ
  let m := D.sup id
  have heq := hD.2 (extent (some m)) ⟨some m,rfl⟩
    (fun n hn => (show n ≤ m from Finset.le_sup (f := id) hn)) (Set.subset_univ _)
  have hf : m + 1 ∈ extent (some m) := heq.symm ▸ Set.mem_univ _
  exact Nat.not_succ_le_self m hf

end GenLimit.ComputationalTrace
