import GenLimit.FiniteWitness.Characterization
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackInnerCovers
import GenLimit.Core.Identification
import GenLimit.Core.SetGeneration
import GenLimit.Paper02_LearningTheory.CountableUnionSeparation

/-!
# Infinite-set generation from finite witnesses

For P27 Theorem 3.9 we use the finite-witness characterization of Li, Han,
Jiang and Gao (arXiv:2609.10525v2). At a finite sample, intersect all
consistent targets whose witnesses have already appeared, then discard the
sample. This gives a globally infinite output. Once the true target is
active, the whole output lies in it.
-/

namespace GenLimit.FeedbackQueries

open Generic FiniteWitness

theorem noFeedback_generation_iff_set_generation [Countable α] [Infinite α]
    (H : LanguageClass α) (hH : UUS H) :
    SetGeneratableInLimit H ↔ GeneratableInLimit H := by
  classical
  refine ⟨setGeneratableInLimit_implies_generatableInLimit, ?_⟩
  intro hgen
  obtain ⟨T, hT, hcore⟩ := (ordinary_iff_finiteWitnesses H hH).mp hgen
  let fresh (S : Finset α) := activeCore H T S \ (↑S : Set α)
  refine ⟨fun _ xs => fresh (sequenceSample xs), ?_, ?_⟩
  · intro t xs
    let S := sequenceSample xs
    change (activeCore H T S \ (↑S : Set α)).Infinite
    apply Set.Infinite.diff _ S.finite_toSet
    by_cases ha : (active H T S).Nonempty
    · exact hcore S ha
    · apply Set.infinite_univ.mono
      intro x _ L hL
      exact (ha ⟨L, hL⟩).elim
  · intro L hL stream hp
    obtain ⟨t, ht⟩ := finset_eventually_subset_sample hp (T L) (hT L hL)
    refine ⟨t, ?_⟩
    intro n hn
    have ha : L ∈ active H T (Generic.sample stream n) :=
      ⟨hL, ht.trans (Generic.sample_mono hn), fun _ hx => Generic.mem_language_of_mem_sample_of_presents hp hx⟩
    simp only [SetCorrectAt, setOutput, sequenceSample_prefix]
    refine ⟨fun _ hx => hx.1 L ha, ?_⟩
    apply Set.disjoint_left.mpr
    intro x hx hseen
    exact hx.2 hseen

/-- The range of globally infinite set outputs gives the cover in A.10. -/
theorem theorem_A_10 [Countable α] [Infinite α] {H : LanguageClass α}
    (hH : UUS H) (hg : GeneratableInLimit H) : HasCountableInnerCover H := by
  classical
  obtain ⟨G, hinf, hG⟩ := (noFeedback_generation_iff_set_generation H hH).mpr hg
  refine ⟨CountableInnerCover.ofCountableFamily
    (fun w : List α => G w.length w.get) (fun w => hinf _ _) ?_⟩
  intro L hL
  haveI : Nonempty L := (hH L hL).nonempty.to_subtype
  obtain ⟨s, hs⟩ := exists_surjective_nat L
  let stream (n : ℕ) : α := (s n).val
  have hp : Generic.Presents stream L := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact (s n).property
    · intro hx
      obtain ⟨n, hn⟩ := hs ⟨x,hx⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  obtain ⟨t, ht⟩ := hG L hL stream hp
  refine ⟨textPrefix stream t, ?_⟩
  change learnerOfFiniteHistory G (textPrefix stream t) ⊆ L
  rw [learnerOfFiniteHistory_textPrefix]
  exact (ht t le_rfl).1

/-- The countable union of cones in P02 already has an explicit inner cover,
while its exact presentations defeat every no-feedback generator (A.11). -/
theorem theorem_A_11 :
    ∃ H : LanguageClass LiRamanTewari.CountableUnionUniverse,
      UUS H ∧ HasCountableInnerCover H ∧ ¬GeneratableInLimit H := by
  refine ⟨LiRamanTewari.countableUnionHardClass, ?_, ?_,
    LiRamanTewari.countableUnionHardClass_not_generatable_in_limit⟩
  · intro L hL
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hL
    exact LiRamanTewari.countableUnionClasses_uus n L hn
  · refine ⟨⟨LiRamanTewari.countableUnionCore, LiRamanTewari.countableUnionCore_infinite, ?_⟩⟩
    intro L hL
    exact Set.mem_iUnion.mp hL

end GenLimit.FeedbackQueries
