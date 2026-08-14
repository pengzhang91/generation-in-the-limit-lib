import GenLimit.Paper02_LearningTheory.NonuniformCharacterization
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Results.Overview

/-!
# #02 Learning Theory to #04 Exploring Facets

The two papers use slightly different presentations of uniform and
non-uniform generation.  #04 quantifies over exact presentations and uses a
lower bound on the current number of distinct samples; #02's shared Core
predicate quantifies over every positive stream and starts from an exact-size
crossing.  On a countable universe and for nonempty indexed languages, the
notions are equivalent.
-/

namespace GenLimit.Bridge.Paper02ToPaper04

/-- P04 Definition 2 is equivalent to P02's class-valued non-uniform
generation predicate on the range of the indexed family. -/
theorem nonuniformlyGeneratable_iff
    [Countable α] (C : GenLimit.Generic.LanguageFamily α)
    (hNonempty : ∀ i, (C i).Nonempty) :
    GenLimit.CharikarPabbaraju.NonuniformlyGeneratable C ↔
      GenLimit.LiRamanTewari.NonuniformlyGeneratable (Set.range C) :=
  GenLimit.CharikarPabbaraju.nonuniformlyGeneratable_iff_generic hNonempty

/-- P04 Definition 3 is equivalent to P02's class-valued uniform generation
predicate on the range of the indexed family. -/
theorem uniformlyGeneratable_iff
    [Countable α] (C : GenLimit.Generic.LanguageFamily α)
    (hNonempty : ∀ i, (C i).Nonempty) :
    GenLimit.CharikarPabbaraju.UniformlyGeneratable C ↔
      GenLimit.LiRamanTewari.UniformlyGeneratable (Set.range C) :=
  GenLimit.CharikarPabbaraju.uniformlyGeneratable_iff_generic hNonempty

/-- P04 overview Theorem 1 follows from P02 Corollary 3.6 after translating
the indexed exact-presentation interface to the shared class interface. -/
theorem theorem_1_from_paper02_corollary_3_6
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (hInfinite : ∀ i, (C i).Infinite) :
    GenLimit.CharikarPabbaraju.NonuniformlyGeneratable C := by
  apply (nonuniformlyGeneratable_iff C
    (fun i ↦ (hInfinite i).nonempty)).mpr
  apply GenLimit.LiRamanTewari.countable_classes_are_nonuniformly_generatable
  · rintro L ⟨i, rfl⟩
    exact hInfinite i
  · exact Set.countable_range C

end GenLimit.Bridge.Paper02ToPaper04
