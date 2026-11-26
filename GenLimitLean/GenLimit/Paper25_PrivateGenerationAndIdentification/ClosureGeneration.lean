import GenLimit.Paper02_LearningTheory.Closure

/-! The nonprivate sample bound in the last sentence of Theorem 1.3.
Definition 2 ranges over subcollections, including the empty subcollection. -/

namespace GenLimit.PrivateLimit

open Generic Set

/-- A natural upper bound in Definition 2. This also allows the source's
dimension −1 case, where every subcollection has infinite intersection. -/
def SubcollectionClosureBound {X : Type*} (C : Set (Set X)) (d : ℕ) : Prop :=
  ∀ S ⊆ C, (⋂₀ S).Finite → (⋂₀ S).ncard ≤ d

theorem closureBound_of_subcollections {X : Type*} {C : Set (Set X)} {d : ℕ}
    (bound : SubcollectionClosureBound C d) : Generic.ClosureDimensionAtMost C d := by
  intro S large _ finite
  have sub : versionSpace C S ⊆ C := fun _ h => h.1
  have core : ⋂₀ versionSpace C S = commonCore C S := rfl
  have card := bound (versionSpace C S) sub (core ▸ finite)
  rw [core] at card
  have le := Set.ncard_le_ncard (Generic.sample_subset_commonCore (H := C) (S := S)) finite
  rw [Set.ncard_coe_finset] at le
  omega

/-- One nonprivate generator works for every target after any d+1 distinct
observations, including on presentations that do not exhaust the target. -/
theorem nonprivate_generation_after_closure_bound {X : Type*} [Nonempty X]
    (C : Set (Set X)) {d : ℕ} (bound : SubcollectionClosureBound C d) :
    ∃ G : Generic.Generator X, ∀ K ∈ C, ∀ n, d < n → ∀ xs : Fin n → X,
      Function.Injective xs → Set.range xs ⊆ K → G n xs ∈ K \ Set.range xs := by
  let h := closureBound_of_subcollections bound
  refine ⟨LiRamanTewari.closureGenerator C d h, ?_⟩
  intro K hk n large xs inj target
  have sample : (↑(sequenceSample xs) : Set X) = range xs := by
    ext x
    exact Generic.mem_sequenceSample_iff
  have consistent : K ∈ versionSpace C (sequenceSample xs) := ⟨hk,sample ▸ target⟩
  have valid := LiRamanTewari.closureGenerator_spec h xs
    ((sequenceSample_card_of_injective xs inj).symm ▸ large) ⟨K,consistent⟩
  exact ⟨valid.1 K consistent, sample ▸ valid.2⟩

end GenLimit.PrivateLimit
