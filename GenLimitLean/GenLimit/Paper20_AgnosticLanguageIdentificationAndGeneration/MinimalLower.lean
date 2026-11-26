import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model
import GenLimit.Support.FullSupportDistribution

/-! # Failure of minimal identification outside the supported tell-tale condition

Theorem 2.5 asks for an optimal language to exist. A descending family can
have an attained optimum at every index and no inclusion-minimal optimum.
Each language has a positive marker for its proper sublanguages. All markers
lie outside one infinite common support.
-/
namespace GenLimit.AgnosticLanguage
open Generic DiscreteIID Filter
open scoped Classical
noncomputable section

theorem risk_eq_zero_iff (p : PMF α) (L : Set α) :
    risk p L = 0 ↔ p.support ⊆ L := by
  unfold risk probability
  rw [ENNReal.toReal_eq_zero_iff, or_iff_left (event_ne_top p Lᶜ), PMF.toOuterMeasure_apply_eq_zero_iff]
  exact Set.disjoint_compl_right_iff_subset

private def tailFamily (i : ℕ) : Set (Bool × ℕ) := {x | x.1 = false ∨ i ≤ x.2}

private theorem tailFamily_strict (i : ℕ) : tailFamily (i+1) ⊂ tailFamily i := by
  constructor
  · intro x hx
    exact hx.imp_right (Nat.le_trans (Nat.le_succ i))
  · intro h
    have hx := h (show (true,i) ∈ tailFamily i from Or.inr le_rfl)
    simp [tailFamily] at hx

/-- Theorem 2.5, with infinite languages and an infinite-support distribution.
In this example the error is one for every sample size and every kernel. -/
theorem minimal_identification_obstruction :
    ∃ (C : Generic.LanguageFamily (Bool × ℕ)) (p : PMF (Bool × ℕ)),
      (∀ i, (C i).Infinite ∧ ∃ T, IsFiniteTellTale (Set.range C) (C i) T) ∧
      p.support.Infinite ∧ (∃ i, Optimal C p i) ∧ ¬ HasSupportedTellTale C p ∧
      ∀ (A : Identifier (Bool × ℕ)) n, idP C A p n = 1 := by
  let emb := Prod.mk false (β := ℕ)
  have hi : Function.Injective emb := fun _ _ h ↦ congrArg Prod.snd h
  let p := positiveGeometric.map emb
  have hs : p.support = Set.range emb := by
    ext x
    rw [PMF.mem_support_map_iff]
    exact ⟨fun ⟨j,_,h⟩ ↦ ⟨j,h⟩,fun ⟨j,h⟩ ↦ ⟨j,positiveGeometric_support j,h⟩⟩
  have hinf := Set.infinite_range_of_injective hi
  have hsub (i) : p.support ⊆ tailFamily i := by
    rw [hs]; rintro _ ⟨j,rfl⟩; exact Or.inl rfl
  have ho (i) : Optimal tailFamily p i := (optimal_iff ..).mpr fun j ↦ by
    rw [(risk_eq_zero_iff ..).mpr (hsub i), (risk_eq_zero_iff ..).mpr (hsub j)]
  refine ⟨tailFamily,p,fun i ↦ ⟨hinf.mono (hs ▸ hsub i), {(true,i)}, ?_⟩, hs ▸ hinf, ⟨0,ho 0⟩, ?_, ?_⟩
  · constructor
    · simpa using (show (true,i) ∈ tailFamily i from Or.inr le_rfl)
    · rintro _ ⟨j,rfl⟩ hmem hji
      have hm := hmem (show (true,i) ∈ (↑({(true,i)} : Finset _) : Set _) by simp)
      have hle : j ≤ i := hm.resolve_left (by simp)
      exact Set.Subset.antisymm hji (fun _ hx ↦ hx.imp_right (Nat.le_trans hle))
  · rintro ⟨i,_,T,hT,hTs⟩
    exact (tailFamily_strict i).ne (hT.2 _ ⟨i+1,rfl⟩ (hTs.trans (hsub _)) (tailFamily_strict i).le)
  · intro A n
    have he : {j | ¬ MinimalOptimal tailFamily p j} = Set.univ :=
      Set.eq_univ_of_forall fun j h ↦ h.2 _ (ho (j+1)) (tailFamily_strict j)
    simp [idP,he]

end
end GenLimit.AgnosticLanguage
