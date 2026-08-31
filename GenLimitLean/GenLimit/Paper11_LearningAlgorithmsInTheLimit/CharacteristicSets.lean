import GenLimit.Paper11_LearningAlgorithmsInTheLimit.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Characteristic sets and late-splitting models

This file checks Lemma 9 and the information-theoretic core of Theorem 17.
The paper's final step turns this core into a noncomputability theorem by a
reduction from the Halting Problem.  We do not claim that machine-level step
without a Turing-computability development.
-/

namespace GenLimit.LearningAlgorithmsLimit

open scoped BigOperators

/-- The graph of observations from model `m` on an input set. -/
def exampleSet
    (observe : Model → Input → Obs) (m : Model)
    (inputs : Set Input) : Set (Input × Obs) :=
  {z | z.1 ∈ inputs ∧ z.2 = observe m z.1}

/-- Definition 8 with the target-model and learner-representation types kept
separate, as in Definition 7 and in the paper's TM-to-FST applications. -/
def IsCharacteristicSet
    (learner : Set (Input × Obs) → Rep)
    (observe : Model → Input → Obs)
    (modelSemantics : Model → Input → Option Output)
    (representationSemantics : Rep → Input → Option Output)
    (source : Set Input) (m : Model) (core : Set Input) : Prop :=
  core ⊆ source ∧
    ∀ inputs, core ⊆ inputs → inputs ⊆ source →
      CorrectOn representationSemantics (modelSemantics m) source
        (learner (exampleSet observe m inputs))

theorem exampleSet_eq_of_observations_eq
    {observe : Model → Input → Obs}
    {m m' : Model} {inputs : Set Input}
    (h : ∀ x ∈ inputs, observe m x = observe m' x) :
    exampleSet observe m inputs =
      exampleSet observe m' inputs := by
  ext z
  constructor
  · rintro ⟨hz, hobs⟩
    exact ⟨hz, hobs.trans (h z.1 hz)⟩
  · rintro ⟨hz, hobs⟩
    exact ⟨hz, hobs.trans (h z.1 hz).symm⟩

/-- Lemma 9 (Distinguishability), for total observation domains.  Partial
domains can be represented by `Option` inside `Obs`. -/
theorem lemma_9_distinguishability
    {learner : Set (Input × Obs) → Rep}
    {observe : Model → Input → Obs}
    {modelSemantics : Model → Input → Option Output}
    {representationSemantics : Rep → Input → Option Output}
    {source coreM coreN : Set Input} {m n : Model}
    (hM : IsCharacteristicSet
      learner observe modelSemantics representationSemantics source m coreM)
    (hN : IsCharacteristicSet
      learner observe modelSemantics representationSemantics source n coreN)
    (hdifferent : ¬AgreeOn modelSemantics source m n) :
    ∃ x ∈ coreM ∪ coreN, observe m x ≠ observe n x := by
  by_contra hnone
  push_neg at hnone
  let combined := coreM ∪ coreN
  have hcombined : combined ⊆ source :=
    Set.union_subset hM.1 hN.1
  have hexamples :
      exampleSet observe m combined =
        exampleSet observe n combined :=
    exampleSet_eq_of_observations_eq hnone
  have hmCorrect :=
    hM.2 combined Set.subset_union_left hcombined
  have hnCorrect :=
    hN.2 combined Set.subset_union_right hcombined
  rw [hexamples] at hmCorrect
  apply hdifferent
  intro x hx
  exact (hmCorrect x hx).symm.trans (hnCorrect x hx)

/-- The pair of models used in the proof of Theorem 17, abstracted to the
only relevant parameter: they have identical observations on input lengths
below `splitAt` and different outputs from `splitAt` onward. -/
def lateSplitObservation
    (splitAt : ℕ) (branch : Bool) (inputLength : ℕ) : Bool :=
  if splitAt ≤ inputLength then branch else false

def lateSplitSemantics
    (splitAt : ℕ) (branch : Bool) (inputLength : ℕ) :
    Option Bool :=
  some (lateSplitObservation splitAt branch inputLength)

theorem lateSplitObservation_eq_below
    (splitAt n : ℕ) (h : n < splitAt) :
    lateSplitObservation splitAt false n =
      lateSplitObservation splitAt true n := by
  simp [lateSplitObservation, Nat.not_le.mpr h]

theorem lateSplitObservation_ne_at
    (splitAt : ℕ) :
    lateSplitObservation splitAt false splitAt ≠
      lateSplitObservation splitAt true splitAt := by
  simp [lateSplitObservation]

theorem lateSplitSemantics_different
    (splitAt : ℕ) :
    ¬AgreeOn (lateSplitSemantics splitAt)
      Set.univ false true := by
  intro h
  have := h splitAt (Set.mem_univ splitAt)
  simp [lateSplitSemantics, lateSplitObservation] at this

/-- Every pair of characteristic sets for the late-splitting models must
contain an input at least as long as the simulated halting time. -/
theorem theorem_17_lateSplit_characteristic_obstruction
    (learner : Set (ℕ × Bool) → Bool)
    (splitAt : ℕ) (coreFalse coreTrue : Set ℕ)
    (hFalse : IsCharacteristicSet
      learner (lateSplitObservation splitAt)
      (lateSplitSemantics splitAt)
      (lateSplitSemantics splitAt)
      Set.univ false coreFalse)
    (hTrue : IsCharacteristicSet
      learner (lateSplitObservation splitAt)
      (lateSplitSemantics splitAt)
      (lateSplitSemantics splitAt)
      Set.univ true coreTrue) :
    ∃ n ∈ coreFalse ∪ coreTrue, splitAt ≤ n := by
  obtain ⟨n, hn, hdiff⟩ :=
    lemma_9_distinguishability hFalse hTrue
      (lateSplitSemantics_different splitAt)
  refine ⟨n, hn, ?_⟩
  by_contra hnot
  exact hdiff (lateSplitObservation_eq_below
    splitAt n (Nat.lt_of_not_ge hnot))

/-- A concrete mass measure: every example contributes at least its input
length plus one. -/
def inputMass (S : Finset ℕ) : ℕ :=
  ∑ n ∈ S, (n + 1)

theorem inputWeight_le_mass_of_mem
    {S : Finset ℕ} {n : ℕ} (hn : n ∈ S) :
    n + 1 ≤ inputMass S := by
  classical
  unfold inputMass
  exact Finset.single_le_sum_of_canonicallyOrdered hn

/-- Finite-mass form of Theorem 17's semantic lower bound. -/
theorem theorem_17_mass_lower_bound_core
    (learner : Set (ℕ × Bool) → Bool)
    (splitAt : ℕ) (coreFalse coreTrue : Finset ℕ)
    (hFalse : IsCharacteristicSet
      learner (lateSplitObservation splitAt)
      (lateSplitSemantics splitAt)
      (lateSplitSemantics splitAt)
      Set.univ false (coreFalse : Set ℕ))
    (hTrue : IsCharacteristicSet
      learner (lateSplitObservation splitAt)
      (lateSplitSemantics splitAt)
      (lateSplitSemantics splitAt)
      Set.univ true (coreTrue : Set ℕ)) :
    splitAt + 1 ≤ inputMass coreFalse + inputMass coreTrue := by
  obtain ⟨n, hn, hsplit⟩ :=
    theorem_17_lateSplit_characteristic_obstruction
      learner splitAt (coreFalse : Set ℕ) (coreTrue : Set ℕ)
      hFalse hTrue
  rcases hn with hnFalse | hnTrue
  · have hmass := inputWeight_le_mass_of_mem hnFalse
    omega
  · have hmass := inputWeight_le_mass_of_mem hnTrue
    omega

/-- Corollary 18's observation-monotonicity core: forgetting information
cannot separate a pair that was indistinguishable with richer observations. -/
theorem corollary_18_forgetting_preserves_indistinguishability
    (rich : Model → Input → Rich)
    (forget : Rich → Poor)
    {m n : Model} {inputs : Set Input}
    (h : ∀ x ∈ inputs, rich m x = rich n x) :
    ∀ x ∈ inputs, forget (rich m x) = forget (rich n x) := by
  intro x hx
  exact congrArg forget (h x hx)

end GenLimit.LearningAlgorithmsLimit
