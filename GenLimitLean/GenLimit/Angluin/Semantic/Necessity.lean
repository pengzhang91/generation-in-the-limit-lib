import GenLimit.Angluin.Semantic.Definitions
import GenLimit.Gold.Text.Superfinite
import Mathlib.Data.Countable.Defs

/-!
# Semantic necessity of Angluin's tell-tale condition

This module derives Angluin's semantic finite-tell-tale necessity from the
already formalized Gold positive-text theorem.  A surjection `ℕ → α` pulls an
indexed family over a countable domain back to a family of languages over
`ℕ`; Gold supplies a finite tell-tale there, and its finite image is a
tell-tale for the original family.

The reduction deliberately reuses `GenLimit.Gold.Text` instead of maintaining
a second locking-sequence diagonal in the Angluin development.  Angluin's
effective predicates and source-facing Condition 1/Condition 2 statements
remain separate.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

noncomputable local instance semanticNecessityDecidableEq : DecidableEq α :=
  Classical.decEq α

/-! ## Pulling a countable domain back to Gold's natural-number universe -/

private def pullbackFamily
    (enumerate : ℕ → α) (C : GenLimit.Generic.LanguageFamily α) :
    GenLimit.LanguageFamily :=
  fun i => enumerate ⁻¹' C i

private def pullbackLearner
    (enumerate : ℕ → α) (M : SemanticIdentifier α) :
    GenLimit.Gold.Text.TextLearner ℕ :=
  fun history => M (history.map enumerate)

private theorem pullbackLearner_textPrefix
    (enumerate : ℕ → α) (M : SemanticIdentifier α)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    pullbackLearner enumerate M (GenLimit.textPrefix stream t) =
      M (GenLimit.textPrefix (fun n => enumerate (stream n)) t) := by
  simp [pullbackLearner, GenLimit.textPrefix, List.map_map, Function.comp_def]

private theorem map_presents_of_pullback_presents
    {enumerate : ℕ → α} (henumerate : Function.Surjective enumerate)
    {C : GenLimit.Generic.LanguageFamily α} {z : ℕ}
    {stream : GenLimit.Generic.Stream ℕ}
    (hP : GenLimit.Presents stream (pullbackFamily enumerate C z)) :
    GenLimit.Generic.Presents (fun n => enumerate (stream n)) (C z) := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    have hn : stream n ∈ pullbackFamily enumerate C z := by
      rw [← hP]
      exact ⟨n, rfl⟩
    exact hn
  · intro x hx
    obtain ⟨n, hn⟩ := henumerate x
    have hnPullback : n ∈ pullbackFamily enumerate C z := by
      change enumerate n ∈ C z
      simpa [hn] using hx
    rw [← hP] at hnPullback
    obtain ⟨t, ht⟩ := hnPullback
    exact ⟨t, by simpa [ht] using hn⟩

private theorem pullbackLearner_identifiesFamily
    {enumerate : ℕ → α} (henumerate : Function.Surjective enumerate)
    {C : GenLimit.Generic.LanguageFamily α}
    {M : SemanticIdentifier α} (hM : SemanticallyIdentifies M C) :
    GenLimit.Gold.Text.IdentifiesFamily
      (pullbackFamily enumerate C) (pullbackLearner enumerate M) := by
  intro z stream hP
  obtain ⟨j, hj, T, hT⟩ :=
    hM z (fun n => enumerate (stream n))
      (map_presents_of_pullback_presents henumerate hP)
  refine ⟨j, ?_, T, ?_⟩
  · change pullbackFamily enumerate C j = pullbackFamily enumerate C z
    ext n
    change enumerate n ∈ C j ↔ enumerate n ∈ C z
    rw [hj]
  · intro t ht
    change pullbackLearner enumerate M (GenLimit.textPrefix stream t) = j
    rw [pullbackLearner_textPrefix]
    exact hT t ht

private theorem pullbackLearner_semanticallyIdentifiesRange
    {enumerate : ℕ → α} (henumerate : Function.Surjective enumerate)
    {C : GenLimit.Generic.LanguageFamily α}
    {M : SemanticIdentifier α} (hM : SemanticallyIdentifies M C) :
    GenLimit.Gold.Text.SemanticallyIdentifiesClass
      (GenLimit.Gold.Text.semanticLearner
        (GenLimit.Gold.Text.familyNaming (pullbackFamily enumerate C))
        (pullbackLearner enumerate M))
      (Set.range (pullbackFamily enumerate C)) := by
  apply GenLimit.Gold.Text.identifiesClass_semanticLearner
  intro L hL
  obtain ⟨z, rfl⟩ := hL
  exact pullbackLearner_identifiesFamily henumerate hM z

private theorem image_isTellTale_of_pullback_isTellTale
    {enumerate : ℕ → α} (henumerate : Function.Surjective enumerate)
    {C : GenLimit.Generic.LanguageFamily α} {z : ℕ} {D : Finset ℕ}
    (hD : GenLimit.Gold.Text.IsTellTale
      (Set.range (pullbackFamily enumerate C))
      (pullbackFamily enumerate C z) D) :
    IsTellTale C z (D.image enumerate) := by
  classical
  constructor
  · intro x hx
    obtain ⟨n, hnD, rfl⟩ := Finset.mem_image.mp hx
    exact hD.1 hnD
  · intro j hDj hjz
    have hDpreimage : (↑D : Set ℕ) ⊆ pullbackFamily enumerate C j := by
      intro n hnD
      exact hDj (Finset.mem_image.mpr ⟨n, hnD, rfl⟩)
    have hpreimageSubset :
        pullbackFamily enumerate C j ⊆ pullbackFamily enumerate C z := by
      intro n hn
      exact hjz hn
    have heq : pullbackFamily enumerate C j = pullbackFamily enumerate C z :=
      hD.2 (pullbackFamily enumerate C j) ⟨j, rfl⟩
        hDpreimage hpreimageSubset
    intro x hx
    obtain ⟨n, hn⟩ := henumerate x
    have hnTarget : n ∈ pullbackFamily enumerate C z := by
      change enumerate n ∈ C z
      simpa [hn] using hx
    have hnCandidate : n ∈ pullbackFamily enumerate C j := by
      rw [heq]
      exact hnTarget
    change x ∈ C j
    rw [← hn]
    exact hnCandidate

/-! ## Angluin's semantic necessity result -/

theorem conditionTwo_of_semanticallyIdentifiable
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (hID : ∃ M : SemanticIdentifier α, SemanticallyIdentifies M C) :
    ConditionTwo C := by
  classical
  obtain ⟨M, hM⟩ := hID
  obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat α
  let Cn := pullbackFamily enumerate C
  let Mn := pullbackLearner enumerate M
  have hclass : GenLimit.Gold.Text.SemanticallyIdentifiesClass
      (GenLimit.Gold.Text.semanticLearner
        (GenLimit.Gold.Text.familyNaming Cn) Mn)
      (Set.range Cn) := by
    exact pullbackLearner_semanticallyIdentifiesRange henumerate hM
  intro z
  by_cases hfinite : (Cn z).Finite
  · let D : Finset ℕ := hfinite.toFinset
    have hDtoSet : (↑D : Set ℕ) = Cn z := by
      ext n
      simp [D]
    have hTell : GenLimit.Gold.Text.IsTellTale
        (Set.range Cn) (Cn z) D := by
      constructor
      · rw [hDtoSet]
      · intro K _hK hDK hKz
        apply Set.Subset.antisymm hKz
        rw [← hDtoSet]
        exact hDK
    exact ⟨D.image enumerate,
      image_isTellTale_of_pullback_isTellTale henumerate hTell⟩
  · have hinfinite : (Cn z).Infinite := hfinite
    obtain ⟨D, hTell⟩ :=
      GenLimit.Gold.Text.finite_tellTale_of_semantic_identification
        hclass ⟨z, rfl⟩ hinfinite
    exact ⟨D.image enumerate,
      image_isTellTale_of_pullback_isTellTale henumerate hTell⟩

end GenLimit.Angluin
