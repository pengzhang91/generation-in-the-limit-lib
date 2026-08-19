import GenLimit.Paper12_NoiseLossAndFeedback.Repetitions
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Definitions
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.WithoutAdversaryInput
import GenLimit.Support.Renaming

/-!
# Relationships to earlier generation semantics

The no-sample schedules of Bai--Panigrahi--Zhang are exactly the autonomous
no-adversary schedules used in Paper11.  The two developments also use the
same injective exact presentations, with a one-step difference between
Paper12's inclusive time and Core's exclusive-prefix time.

This module records those facts as bridges.  It also transports the Paper11
predicates along a bijective renaming of the example universe, allowing the
integer witnesses to be reused over Paper12's canonical universe `ℕ`.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## No samples versus no adversary input -/

theorem uniformlyGeneratableWithoutSamples_iff_withoutAdversaryInput
    (C : LanguageClass α) :
    UniformlyGeneratableWithoutSamples C ↔
      GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput C := by
  constructor
  · rintro ⟨gen, T, hgen⟩
    exact ⟨gen.output, T, gen.injective', hgen⟩
  · rintro ⟨outputs, T, hinjective, houtputs⟩
    exact ⟨⟨outputs, hinjective⟩, T, houtputs⟩

theorem generatableInLimitWithoutSamples_iff_withoutAdversaryInput
    (C : LanguageClass α) :
    GeneratableInLimitWithoutSamples C ↔
      GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput C := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact ⟨gen.output, gen.injective', hgen⟩
  · rintro ⟨outputs, hinjective, houtputs⟩
    exact ⟨⟨outputs, hinjective⟩, houtputs⟩

/-! ## Without samples implies generation with samples -/

/-- Core's distinct-sample uniform guarantee specializes to the paper's
raw-time guarantee on an injective exact presentation. -/
theorem uniformlyGeneratableWithoutRepetitions_of_generic
    {C : LanguageClass α}
    (h : GenLimit.Generic.UniformlyGeneratable C) :
    UniformlyGeneratableWithoutRepetitions C := by
  classical
  obtain ⟨gen, d, hgen⟩ := h
  refine ⟨gen, d, ?_⟩
  intro L hLC stream hstream t ht
  apply (correctAt_iff_generic_succ gen L stream t).mpr
  apply hgen L hLC stream (streamIn_of_presents hstream.2) d
  · unfold GenLimit.Generic.sample
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact hstream.1 hij
  · omega

/-- Core's target-dependent distinct-sample guarantee similarly specializes
to the paper's non-uniform raw-time guarantee. -/
theorem nonuniformlyGeneratableWithoutRepetitions_of_generic
    {C : LanguageClass α}
    (h : GenLimit.Generic.NonuniformlyGeneratable C) :
    NonuniformlyGeneratableWithoutRepetitions C := by
  classical
  obtain ⟨gen, hgen⟩ := h
  refine ⟨gen, ?_⟩
  intro L hLC
  obtain ⟨d, hd⟩ := hgen L hLC
  refine ⟨d, ?_⟩
  intro stream hstream t ht
  apply (correctAt_iff_generic_succ gen L stream t).mpr
  apply hd stream (streamIn_of_presents hstream.2) d
  · unfold GenLimit.Generic.sample
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact hstream.1 hij
  · omega

/-- An autonomous uniform generator also gives a uniform generator in the
standard model with adversarial samples.  The adapter uses the samples only
to skip autonomous outputs that have already appeared. -/
theorem uniformlyGeneratableWithoutSamples_implies_withSamples
    {C : LanguageClass α}
    (h : UniformlyGeneratableWithoutSamples C) :
    UniformlyGeneratableWithoutRepetitions C := by
  apply uniformlyGeneratableWithoutRepetitions_of_generic
  exact
    GenLimit.UnionClosedness.uniformlyGeneratable_of_withoutAdversaryInput
      ((uniformlyGeneratableWithoutSamples_iff_withoutAdversaryInput C).mp h)

/-- An autonomous generator in the limit also gives a non-uniform generator
in the standard model with adversarial samples. -/
theorem generatableInLimitWithoutSamples_implies_withSamples
    {C : LanguageClass α}
    (h : GeneratableInLimitWithoutSamples C) :
    NonuniformlyGeneratableWithoutRepetitions C := by
  apply nonuniformlyGeneratableWithoutRepetitions_of_generic
  exact
    GenLimit.UnionClosedness.nonuniformlyGeneratable_of_withoutAdversaryInput
      ((generatableInLimitWithoutSamples_iff_withoutAdversaryInput C).mp h)

/-! ## The one-step presentation convention -/

theorem isLimitGeneratorWithoutRepetitions_iff_onInjectivePresentations
    (gen : Generator α) (C : LanguageClass α) :
    IsLimitGeneratorWithoutRepetitions gen C ↔
      GenLimit.UnionClosedness.IsLimitGeneratorOnInjectivePresentations
        gen C := by
  constructor
  · intro hgen L hLC stream hinjective hpresents
    obtain ⟨T, hT⟩ :=
      hgen L hLC stream ⟨hinjective, hpresents⟩
    refine ⟨T + 1, ?_⟩
    intro s hs
    obtain ⟨t, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    exact
      (correctAt_iff_generic_succ gen L stream t).mp
        (hT t (by omega))
  · intro hgen L hLC stream henumeration
    obtain ⟨T, hT⟩ :=
      hgen L hLC stream henumeration.1 henumeration.2
    refine ⟨T, ?_⟩
    intro t ht
    exact
      (correctAt_iff_generic_succ gen L stream t).mpr
        (hT (t + 1) (by omega))

theorem generatableInLimitWithoutRepetitions_iff_onInjectivePresentations
    (C : LanguageClass α) :
    GeneratableInLimitWithoutRepetitions C ↔
      GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations C := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact
      ⟨gen,
        (isLimitGeneratorWithoutRepetitions_iff_onInjectivePresentations
          gen C).mp hgen⟩
  · rintro ⟨gen, hgen⟩
    exact
      ⟨gen,
        (isLimitGeneratorWithoutRepetitions_iff_onInjectivePresentations
          gen C).mpr hgen⟩

/-! ## Transporting the Paper11 predicates across a universe equivalence -/

theorem uniformWithoutAdversaryInput_rename
    (e : α ≃ β) {C : LanguageClass α}
    (h :
      GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput C) :
    GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput
      (GenLimit.Support.renameLanguageClass e C) := by
  obtain ⟨outputs, T, hinjective, houtputs⟩ := h
  refine
    ⟨GenLimit.Support.renameStream e outputs, T,
      GenLimit.Support.renameStream_injective e hinjective, ?_⟩
  rintro K ⟨L, hLC, rfl⟩ t ht
  exact
    (GenLimit.Support.mem_renameLanguage_iff e L (outputs t)).mpr
      (houtputs L hLC t ht)

theorem nonuniformWithoutAdversaryInput_rename
    (e : α ≃ β) {C : LanguageClass α}
    (h :
      GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput C) :
    GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput
      (GenLimit.Support.renameLanguageClass e C) := by
  obtain ⟨outputs, hinjective, houtputs⟩ := h
  refine
    ⟨GenLimit.Support.renameStream e outputs,
      GenLimit.Support.renameStream_injective e hinjective, ?_⟩
  rintro K ⟨L, hLC, rfl⟩
  obtain ⟨T, hT⟩ := houtputs L hLC
  refine ⟨T, ?_⟩
  intro t ht
  exact
    (GenLimit.Support.mem_renameLanguage_iff e L (outputs t)).mpr
      (hT t ht)

theorem generatableOnInjectivePresentations_rename
    (e : α ≃ β) {C : LanguageClass α}
    (h :
      GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations C) :
    GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations
      (GenLimit.Support.renameLanguageClass e C) := by
  obtain ⟨gen, hgen⟩ := h
  refine ⟨GenLimit.Support.renameGenerator e gen, ?_⟩
  rintro K ⟨L, hLC, rfl⟩ stream hinjective hpresents
  let pulled := GenLimit.Support.renameStream e.symm stream
  have hpulledInjective : Function.Injective pulled :=
    GenLimit.Support.renameStream_injective e.symm hinjective
  have hpulledPresents : Presents pulled L := by
    have h := GenLimit.Support.presents_renameStream e.symm hpresents
    simpa [pulled] using h
  obtain ⟨T, hT⟩ :=
    hgen L hLC pulled hpulledInjective hpulledPresents
  refine ⟨T, ?_⟩
  intro t ht
  have hcorrect :=
    (GenLimit.Support.correctAt_rename_iff e gen L pulled t).mpr
      (hT t ht)
  simpa [pulled] using hcorrect

theorem not_generatableOnInjectivePresentations_rename
    (e : α ≃ β) {C : LanguageClass α}
    (h :
      ¬GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations C) :
    ¬GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations
      (GenLimit.Support.renameLanguageClass e C) := by
  intro hrenamed
  apply h
  have hback :=
    generatableOnInjectivePresentations_rename e.symm hrenamed
  simpa using hback

end GenLimit.NoiseLossFeedback
