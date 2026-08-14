import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Nonuniform

/-!
# Charikar--Pabbaraju: the no-repeated-output refinement

The Section 3 footnote observes that the greedy non-uniform generator can be
made not to repeat its own outputs.  This module formalizes that refinement.
The finite-history state remembers all earlier outputs and excludes them,
together with the current input sample, from the same infinite greedy core.

This is still the paper's semantic construction: the critical finiteness and
inclusion tests are noncomputable.  No oracle-machine or runtime claim is made.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-- Finite state sufficient to exclude every earlier output. -/
structure NoRepeatGreedyState (α : Type*) where
  outputs : Finset α
  output : α

/-- The harmless empty-history output.  It is inserted into the used-output
set so that every later output is distinct from it as well. -/
noncomputable def noRepeatGreedyInitial [Infinite α] :
    NoRepeatGreedyState α := by
  classical
  let x := Classical.choose (Set.infinite_univ.nonempty :
    (Set.univ : Set α).Nonempty)
  exact ⟨{x}, x⟩

theorem noRepeatGreedyInitial_output_mem [Infinite α] :
    (noRepeatGreedyInitial : NoRepeatGreedyState α).output ∈
      (noRepeatGreedyInitial : NoRepeatGreedyState α).outputs := by
  simp [noRepeatGreedyInitial]

/-- One semantic greedy step, excluding both observations and all outputs
already stored in the state. -/
noncomputable def noRepeatGreedyStep [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α)
    (previous : NoRepeatGreedyState α)
    (S : Finset α) (n : ℕ) :
    NoRepeatGreedyState α := by
  classical
  let used := S ∪ previous.outputs
  let y := Classical.choose
    ((greedyCore_infinite C S n).diff used.finite_toSet).nonempty
  exact ⟨insert y previous.outputs, y⟩

theorem noRepeatGreedyStep_spec [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α)
    (previous : NoRepeatGreedyState α)
    (S : Finset α) (n : ℕ) :
    (noRepeatGreedyStep C previous S n).output ∈
        greedyCore C S n ∧
      (noRepeatGreedyStep C previous S n).output ∉ S ∧
      (noRepeatGreedyStep C previous S n).output ∉ previous.outputs := by
  classical
  let used := S ∪ previous.outputs
  have hchoice := Classical.choose_spec
    ((greedyCore_infinite C S n).diff used.finite_toSet).nonempty
  have hnotUsed :
      Classical.choose
          ((greedyCore_infinite C S n).diff used.finite_toSet).nonempty ∉
        used := hchoice.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [noRepeatGreedyStep, used] using hchoice.1
  · intro hS
    exact hnotUsed (Finset.mem_union_left previous.outputs hS)
  · intro houtputs
    exact hnotUsed (Finset.mem_union_right S houtputs)

theorem noRepeatGreedyStep_output_mem_outputs [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α)
    (previous : NoRepeatGreedyState α)
    (S : Finset α) (n : ℕ) :
    (noRepeatGreedyStep C previous S n).output ∈
      (noRepeatGreedyStep C previous S n).outputs := by
  classical
  simp [noRepeatGreedyStep]

theorem noRepeatGreedyStep_outputs_mono [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α)
    (previous : NoRepeatGreedyState α)
    (S : Finset α) (n : ℕ) :
    previous.outputs ⊆
      (noRepeatGreedyStep C previous S n).outputs := by
  classical
  intro x hx
  simpa [noRepeatGreedyStep] using
    Finset.mem_insert_of_mem hx

/-- Interpret a finite history.  At a successor length the previous state is
computed from the strict prefix and the new output is chosen from the current
greedy core. -/
noncomputable def noRepeatGreedyRun [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) :
    (t : ℕ) → (Fin t → α) → NoRepeatGreedyState α
  | 0, _ => noRepeatGreedyInitial
  | t + 1, xs =>
      noRepeatGreedyStep C
        (noRepeatGreedyRun C t (fun i => xs i.castSucc))
        (GenLimit.Generic.sequenceSample xs) (t + 1)

/-- The generator emitted by the finite-history state interpreter. -/
noncomputable def noRepeatGreedyGenerator [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) :
    GenLimit.Generic.Generator α :=
  fun t xs => (noRepeatGreedyRun C t xs).output

theorem noRepeatGreedyRun_output_mem_outputs [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α)
    (t : ℕ) (xs : Fin t → α) :
    (noRepeatGreedyRun C t xs).output ∈
      (noRepeatGreedyRun C t xs).outputs := by
  cases t with
  | zero =>
      simpa [noRepeatGreedyRun] using
        (noRepeatGreedyInitial_output_mem (α := α))
  | succ t =>
      simpa [noRepeatGreedyRun] using
        noRepeatGreedyStep_output_mem_outputs C
          (noRepeatGreedyRun C t
            (fun i => xs i.castSucc))
          (GenLimit.Generic.sequenceSample xs) (t + 1)

theorem noRepeatGreedyRun_succ_outputs_mono [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    (noRepeatGreedyRun C t (fun i => stream i)).outputs ⊆
      (noRepeatGreedyRun C (t + 1) (fun i => stream i)).outputs := by
  simpa [noRepeatGreedyRun] using
    noRepeatGreedyStep_outputs_mono C
      (noRepeatGreedyRun C t (fun i => stream i))
      (GenLimit.Generic.sequenceSample
        (fun i : Fin (t + 1) => stream i)) (t + 1)

theorem noRepeatGreedyRun_output_mem_later_outputs [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α)
    (stream : GenLimit.Generic.Stream α) {s t : ℕ}
    (hst : s ≤ t) :
    (noRepeatGreedyRun C s (fun i => stream i)).output ∈
      (noRepeatGreedyRun C t (fun i => stream i)).outputs := by
  induction t with
  | zero =>
      have hs : s = 0 := Nat.eq_zero_of_le_zero hst
      subst s
      exact noRepeatGreedyRun_output_mem_outputs C 0
        (fun i => stream i)
  | succ t ih =>
      rcases Nat.eq_or_lt_of_le hst with rfl | hlt
      · exact noRepeatGreedyRun_output_mem_outputs C (t + 1)
          (fun i => stream i)
      · exact noRepeatGreedyRun_succ_outputs_mono C stream t
          (ih (Nat.le_of_lt_succ hlt))

theorem noRepeatGreedyRun_succ_spec [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    (noRepeatGreedyRun C (t + 1) (fun i => stream i)).output ∈
        greedyCore C (GenLimit.Generic.sample stream (t + 1)) (t + 1) ∧
      (noRepeatGreedyRun C (t + 1) (fun i => stream i)).output ∉
        GenLimit.Generic.sample stream (t + 1) ∧
      (noRepeatGreedyRun C (t + 1) (fun i => stream i)).output ∉
        (noRepeatGreedyRun C t (fun i => stream i)).outputs := by
  simpa [noRepeatGreedyRun, GenLimit.Generic.sequenceSample_prefix] using
    noRepeatGreedyStep_spec C
      (noRepeatGreedyRun C t (fun i => stream i))
      (GenLimit.Generic.sequenceSample
        (fun i : Fin (t + 1) => stream i)) (t + 1)

/-- A generator never repeats an output on any input stream. -/
def OutputsWithoutRepetition
    (gen : GenLimit.Generic.Generator α) : Prop :=
  ∀ stream : GenLimit.Generic.Stream α,
    Function.Injective (fun t => GenLimit.Generic.output gen stream t)

theorem noRepeatGreedyGenerator_without_repetition [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) :
    OutputsWithoutRepetition (noRepeatGreedyGenerator C) := by
  intro stream a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le a) hablt))
    have hale : a ≤ u := Nat.le_of_lt_succ hablt
    have haMem :=
      noRepeatGreedyRun_output_mem_later_outputs C stream hale
    have hbNot := (noRepeatGreedyRun_succ_spec C stream u).2.2
    have heq :
        (noRepeatGreedyRun C a (fun i => stream i)).output =
          (noRepeatGreedyRun C (u + 1) (fun i => stream i)).output := by
      simpa [GenLimit.Generic.output, noRepeatGreedyGenerator] using hab
    apply hbNot
    exact heq ▸ haMem
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le b) hbalt))
    have hble : b ≤ u := Nat.le_of_lt_succ hbalt
    have hbMem :=
      noRepeatGreedyRun_output_mem_later_outputs C stream hble
    have haNot := (noRepeatGreedyRun_succ_spec C stream u).2.2
    have heq :
        (noRepeatGreedyRun C b (fun i => stream i)).output =
          (noRepeatGreedyRun C (u + 1) (fun i => stream i)).output := by
      simpa [GenLimit.Generic.output, noRepeatGreedyGenerator] using hab.symm
    apply haNot
    exact heq ▸ hbMem

/-- Theorem 6 with the optional no-repeated-output refinement from the
Section 3 footnote. -/
theorem nonuniform_upper_bound_no_repetition [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) {i t : ℕ}
    (stream : GenLimit.Generic.Stream α)
    (hstream : GenLimit.Generic.StreamIn stream (C i))
    (hthreshold : max (i + 1) (nonuniformComplexity C i + 1) ≤
      (GenLimit.Generic.sample stream t).card) :
    GenLimit.Generic.CorrectAt (noRepeatGreedyGenerator C) (C i) stream t := by
  let S := GenLimit.Generic.sample stream t
  have hiCard : i + 1 ≤ S.card :=
    (Nat.le_max_left _ _).trans hthreshold
  have hmCard : nonuniformComplexity C i < S.card := by
    apply Nat.lt_of_succ_le
    exact (Nat.le_max_right _ _).trans hthreshold
  have hit : i + 1 ≤ t :=
    hiCard.trans (GenLimit.Generic.sample_card_le stream t)
  have hS : (↑S : Set α) ⊆ C i := by
    intro x hx
    obtain ⟨s, -, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hx
    exact hstream ⟨s, rfl⟩
  have hiFirst : i ∈ selectedIndices C S (i + 1) :=
    target_selected_at_threshold hS hmCard
  have hiFinal : i ∈ selectedIndices C S t :=
    selectedIndices_mono C S hit hiFirst
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ i) hit))
  have hspec := noRepeatGreedyRun_succ_spec C stream u
  change
    noRepeatGreedyGenerator C (u + 1)
        (fun j : Fin (u + 1) => stream j) ∈ C i ∧
      noRepeatGreedyGenerator C (u + 1)
        (fun j : Fin (u + 1) => stream j) ∉ S
  exact ⟨greedyCore_subset_target hiFinal hspec.1, hspec.2.1⟩

/-- Overview Theorem 1 together with the Section 3 nonrepetition footnote:
one generator has the paper's non-uniform guarantee and never repeats an
output, even before its correctness threshold. -/
theorem countable_collections_nonuniformly_generatable_without_repetition
    [Infinite α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (_hInfinite : ∀ i, (C i).Infinite) :
    ∃ gen : GenLimit.Generic.Generator α,
      IsNonuniformGenerator gen C ∧ OutputsWithoutRepetition gen := by
  refine ⟨noRepeatGreedyGenerator C, ?_, ?_⟩
  · intro i
    refine ⟨max (i + 1) (nonuniformComplexity C i + 1), ?_⟩
    intro stream hP t ht
    exact nonuniform_upper_bound_no_repetition C stream
      (GenLimit.Generic.streamIn_of_presents hP) ht
  · exact noRepeatGreedyGenerator_without_repetition C

end GenLimit.CharikarPabbaraju
