import GenLimit.Core.ClassGeneration

/-!
# Generation without adversary input

Theorem 3.2 says that each component class can be generated without first
receiving elements from the adversary.  This is stronger than the shared
uniform and non-uniform predicates, which constrain eventual correctness but
allow the generator to learn from its finite input history.

The paper's strengthening is represented here by an injective autonomous
output stream.  Uniform generation uses one eventual-correctness time for the
whole class; non-uniform generation permits that time to depend on the target
language.  In particular, non-uniform autonomous generation may make finitely
many early mistakes.

These notions and their adapter to the history-based Core API remain local to
Paper10.  The adapter consults a finite history only to skip outputs that have
already been shown; its underlying output order is fixed independently of the
target and of the adversary's examples.
-/

namespace GenLimit.UnionClosedness

open GenLimit.Generic

/-- A zero-seed autonomous schedule: its next output depends only on its own
clock, not on adversary-provided examples. -/
abbrev NoAdversaryInputSchedule (α : Type*) := ℕ → α

/-- `T` is a class-wide correctness time for an injective autonomous
schedule. -/
def IsUniformNoAdversaryInputScheduleAt
    (outputs : NoAdversaryInputSchedule α)
    (H : LanguageClass α) (T : ℕ) : Prop :=
  Function.Injective outputs ∧
    ∀ L, L ∈ H → ∀ t, T ≤ t → outputs t ∈ L

/-- One injective autonomous output stream is eventually correct for every
language in `H`, from a class-wide time independent of the target. -/
def UniformlyGeneratableWithoutAdversaryInput
    (H : LanguageClass α) : Prop :=
  ∃ outputs : NoAdversaryInputSchedule α, ∃ T : ℕ,
    IsUniformNoAdversaryInputScheduleAt outputs H T

/-- An injective autonomous schedule whose correctness time may depend on
the target language. -/
def IsNonuniformNoAdversaryInputSchedule
    (outputs : NoAdversaryInputSchedule α)
    (H : LanguageClass α) : Prop :=
  Function.Injective outputs ∧
    ∀ L, L ∈ H → ∃ T : ℕ, ∀ t, T ≤ t → outputs t ∈ L

/-- One injective autonomous output stream is eventually correct for every
language in `H`, with a correctness time that may depend on the target. -/
def NonuniformlyGeneratableWithoutAdversaryInput
    (H : LanguageClass α) : Prop :=
  ∃ outputs : NoAdversaryInputSchedule α,
    IsNonuniformNoAdversaryInputSchedule outputs H

private theorem autonomousTail_injective
    {outputs : ℕ → α} (hinjective : Function.Injective outputs)
    (T : ℕ) :
    Function.Injective (fun k : ℕ => outputs (T + k)) := by
  intro i j hij
  exact Nat.add_left_cancel (hinjective hij)

private theorem exists_fresh_autonomous_index
    (outputs : ℕ → α) (hinjective : Function.Injective outputs)
    {t : ℕ} (xs : Fin t → α) :
    ∃ n : ℕ, t ≤ n ∧ outputs n ∉ sequenceSample xs := by
  classical
  have htail :
      (Set.range (fun k : ℕ => outputs (t + k))).Infinite :=
    Set.infinite_range_of_injective
      (autonomousTail_injective hinjective t)
  obtain ⟨x, hxTail, hxFresh⟩ :=
    (htail.diff (sequenceSample xs).finite_toSet).nonempty
  obtain ⟨k, rfl⟩ := hxTail
  exact ⟨t + k, Nat.le_add_right t k, hxFresh⟩

/-- Adapt an injective autonomous output stream to the Core generator API by
selecting the first output at or beyond the current time that is absent from
the finite adversary history. -/
noncomputable def freshGeneratorFromAutonomousOutputs
    (outputs : ℕ → α) (hinjective : Function.Injective outputs) :
    Generator α := by
  classical
  intro _t xs
  exact outputs (Nat.find
    (exists_fresh_autonomous_index outputs hinjective xs))

theorem freshGeneratorFromAutonomousOutputs_spec
    (outputs : ℕ → α) (hinjective : Function.Injective outputs)
    {t : ℕ} (xs : Fin t → α) :
    ∃ n : ℕ,
      t ≤ n ∧
      freshGeneratorFromAutonomousOutputs outputs hinjective t xs =
        outputs n ∧
      freshGeneratorFromAutonomousOutputs outputs hinjective t xs ∉
        sequenceSample xs := by
  classical
  have hspec := Nat.find_spec
    (exists_fresh_autonomous_index outputs hinjective xs)
  refine ⟨_, hspec.1, ?_, ?_⟩
  · rfl
  · exact hspec.2

/-- A uniform no-input witness gives an ordinary uniform generator. -/
theorem uniformlyGeneratable_of_withoutAdversaryInput
    {H : LanguageClass α}
    (h : UniformlyGeneratableWithoutAdversaryInput H) :
    UniformlyGeneratable H := by
  classical
  obtain ⟨outputs, T, hinjective, houtputs⟩ := h
  let G := freshGeneratorFromAutonomousOutputs outputs hinjective
  refine ⟨G, T, ?_⟩
  intro L hL stream _hstream t hcard s hts
  have hTt : T ≤ t := by
    calc
      T = (sample stream t).card := hcard.symm
      _ ≤ t := sample_card_le stream t
  obtain ⟨n, hsn, hout, hfresh⟩ :=
    freshGeneratorFromAutonomousOutputs_spec
      outputs hinjective (fun i : Fin s => stream i)
  have houtput : output G stream s = outputs n := hout
  constructor
  · rw [houtput]
    exact houtputs L hL n ((hTt.trans hts).trans hsn)
  · rw [houtput]
    simpa [G, hout, sequenceSample_prefix] using hfresh

/-- A non-uniform no-input witness gives an ordinary non-uniform generator. -/
theorem nonuniformlyGeneratable_of_withoutAdversaryInput
    {H : LanguageClass α}
    (h : NonuniformlyGeneratableWithoutAdversaryInput H) :
    NonuniformlyGeneratable H := by
  classical
  obtain ⟨outputs, hinjective, houtputs⟩ := h
  let G := freshGeneratorFromAutonomousOutputs outputs hinjective
  refine ⟨G, ?_⟩
  intro L hL
  obtain ⟨T, hT⟩ := houtputs L hL
  refine ⟨T, ?_⟩
  intro stream _hstream t hcard s hts
  have hTt : T ≤ t := by
    calc
      T = (sample stream t).card := hcard.symm
      _ ≤ t := sample_card_le stream t
  obtain ⟨n, hsn, hout, hfresh⟩ :=
    freshGeneratorFromAutonomousOutputs_spec
      outputs hinjective (fun i : Fin s => stream i)
  have houtput : output G stream s = outputs n := hout
  constructor
  · rw [houtput]
    exact hT n ((hTt.trans hts).trans hsn)
  · rw [houtput]
    simpa [G, hout, sequenceSample_prefix] using hfresh

/-- A class-wide no-input time is in particular a target-dependent one. -/
theorem uniformWithoutAdversaryInput_implies_nonuniform
    {H : LanguageClass α}
    (h : UniformlyGeneratableWithoutAdversaryInput H) :
    NonuniformlyGeneratableWithoutAdversaryInput H := by
  obtain ⟨outputs, T, hinjective, houtputs⟩ := h
  exact ⟨outputs, hinjective, fun L hL => ⟨T, houtputs L hL⟩⟩

/-- An injective autonomous tail inside every target implies the paper's
standing infinite-language convention. -/
theorem uus_of_nonuniformWithoutAdversaryInput
    {H : LanguageClass α}
    (h : NonuniformlyGeneratableWithoutAdversaryInput H) :
    UUS H := by
  obtain ⟨outputs, hinjective, houtputs⟩ := h
  intro L hL
  obtain ⟨T, hT⟩ := houtputs L hL
  have htail :
      (Set.range (fun k : ℕ => outputs (T + k))).Infinite :=
    Set.infinite_range_of_injective
      (autonomousTail_injective hinjective T)
  apply htail.mono
  rintro x ⟨k, rfl⟩
  exact hT (T + k) (Nat.le_add_right T k)

theorem uus_of_uniformWithoutAdversaryInput
    {H : LanguageClass α}
    (h : UniformlyGeneratableWithoutAdversaryInput H) :
    UUS H :=
  uus_of_nonuniformWithoutAdversaryInput
    (uniformWithoutAdversaryInput_implies_nonuniform h)

end GenLimit.UnionClosedness
