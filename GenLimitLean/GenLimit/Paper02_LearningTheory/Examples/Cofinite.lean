import GenLimit.Paper02_LearningTheory.Closure
import Mathlib.Data.Set.Countable

/-!
# The cofinite language class

Appendix A and Appendix C of #02 use the same class of cofinite languages for
different separations.  This file records the shared witness and its closure
properties; prediction- and EUC-specific conclusions remain in their native
modules.
-/

namespace GenLimit.LiRamanTewari

/-- All cofinite subsets of `α`. -/
def cofiniteLanguageClass (α : Type*) : GenLimit.Generic.LanguageClass α :=
  {L | ∃ A : Set α, A.Finite ∧ L = Set.univ \ A}

theorem cofiniteLanguageClass_countable [Countable α] :
    (cofiniteLanguageClass α).Countable := by
  have hfinite : {A : Set α | A.Finite}.Countable :=
    Set.Countable.setOf_finite
  have himage := hfinite.image (fun A : Set α ↦ Set.univ \ A)
  apply himage.mono
  rintro L ⟨A, hA, rfl⟩
  exact ⟨A, hA, rfl⟩

theorem cofiniteLanguageClass_uus [Infinite α] :
    UUS (cofiniteLanguageClass α) := by
  intro L hL
  obtain ⟨A, hA, rfl⟩ := hL
  exact Set.infinite_univ.diff hA

theorem commonCore_cofiniteLanguageClass_eq (S : Finset α) :
    commonCore (cofiniteLanguageClass α) S = (↑S : Set α) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxS
    let L : Set α := Set.univ \ {x}
    have hLClass : L ∈ cofiniteLanguageClass α :=
      ⟨{x}, Set.finite_singleton x, rfl⟩
    have hSL : (↑S : Set α) ⊆ L := by
      intro y hy
      refine ⟨Set.mem_univ y, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hyx
      apply hxS
      rw [← hyx]
      exact hy
    have hxL := hx L ⟨hLClass, hSL⟩
    exact hxL.2 (Set.mem_singleton x)
  · exact sample_subset_commonCore

theorem cofiniteLanguageClass_infiniteClosure [Infinite α] :
    HasInfiniteClosureDimension (cofiniteLanguageClass α) := by
  intro d
  obtain ⟨S, _hS, hcard⟩ :=
    (Set.infinite_univ : (Set.univ : Set α).Infinite).exists_subset_card_eq d
  refine ⟨S, ?_, ?_⟩
  · omega
  · constructor
    · refine ⟨Set.univ, ?_, Set.subset_univ _⟩
      exact ⟨∅, Set.finite_empty, by simp⟩
    · have hcore :
          GenLimit.Generic.commonCore (cofiniteLanguageClass α) S =
            (↑S : Set α) :=
        commonCore_cofiniteLanguageClass_eq S
      rw [hcore]
      exact S.finite_toSet

theorem cofiniteLanguageClass_not_uniform [Infinite α] [Countable α] :
    ¬UniformlyGeneratable (cofiniteLanguageClass α) :=
  closure_dimension_necessity cofiniteLanguageClass_uus
    cofiniteLanguageClass_infiniteClosure

end GenLimit.LiRamanTewari
