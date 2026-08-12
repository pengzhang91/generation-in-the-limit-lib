import GenLimit.Bridges.BasicToGeneric
import GenLimit.Paper01_LanguageGeneration.SetInterface
import GenLimit.Paper02_LearningTheory

/-!
# #01 KM generation to #02 Learning Theory

KM's semantic set interface and #02 use the same eventual validity/freshness
criterion but package generator inputs differently.  This module supplies the
adapter and records that #02's countable-class theorem strengthens the KM
route by first obtaining non-uniform generation.
-/

namespace GenLimit.KM.SetInterface

/-- KM's observed-set generator as a #02 finite-history generator. -/
noncomputable def genericGenerator
    (O : GenLimit.OracleFamily) : GenLimit.Generic.Generator ℕ :=
  GenLimit.Bridge.generatorOfObservedSet (generator O)

@[simp] theorem output_genericGenerator
    (O : GenLimit.OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    GenLimit.Generic.output (genericGenerator O) stream t =
      generator O (GenLimit.sample stream t) :=
  GenLimit.Bridge.output_generatorOfObservedSet (generator O) stream t

/-- The KM set-interface theorem is exactly a #02 limit generator on the
extensional range of the indexed family. -/
theorem genericGenerator_isLimitGenerator
    (O : GenLimit.OracleFamily) :
    GenLimit.Generic.IsLimitGenerator (genericGenerator O)
      (Set.range O.language) := by
  intro L hL stream hPresentation
  obtain ⟨z, rfl⟩ := hL
  have hP : GenLimit.Presents stream (O.language z) :=
    (GenLimit.Bridge.basicPresents_iff_genericPresents _ _).mpr hPresentation
  obtain ⟨T, hT⟩ :=
    kleinbergMullainathan_set_interface_with_repetitions O hP
  refine ⟨T, ?_⟩
  intro t ht
  have hout := hT t ht
  constructor
  · simpa [genericGenerator] using hout.1
  · simpa [genericGenerator,
      GenLimit.Bridge.genericSample_eq_basicSample] using hout.2

/-- KM Theorem 2.1 in the extensional #02 class interface. -/
theorem range_generatableInLimit
    (O : GenLimit.OracleFamily) :
    GenLimit.Generic.GeneratableInLimit (Set.range O.language) :=
  ⟨genericGenerator O, genericGenerator_isLimitGenerator O⟩

/-- For the same indexed KM family, P02's Corollary 3.6 proves the stronger
intermediate non-uniform conclusion before recovering limit generation. -/
theorem range_nonuniformlyGeneratable_via_paper02
    (O : GenLimit.OracleFamily) :
    GenLimit.Generic.NonuniformlyGeneratable (Set.range O.language) := by
  exact
    GenLimit.LiRamanTewari.countable_classes_are_nonuniformly_generatable
      (fun _ hL => by
        obtain ⟨i, rfl⟩ := hL
        exact O.infinite' i)
      (Set.countable_range O.language)

/-- The two proof routes to limit generation: directly by KM, or through
P02's stronger non-uniform result and the shared hierarchy. -/
theorem range_limit_generation_two_routes
    (O : GenLimit.OracleFamily) :
    GenLimit.Generic.GeneratableInLimit (Set.range O.language) ∧
      GenLimit.Generic.NonuniformlyGeneratable (Set.range O.language) :=
  ⟨range_generatableInLimit O,
    range_nonuniformlyGeneratable_via_paper02 O⟩

end GenLimit.KM.SetInterface
