import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Definitions
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.MainClasses

/-!
# Alternating-phase endgames of the Theorem 4.1 diagonal

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, proof of detailed Theorem 4.1.

This module isolates the infinite-phase certificate used by the shared
alternating recursion.  The recursion enumerates all negative integers and
permanently omits an injective sequence of positive transition outputs.  The
older finite-stall certificate API is intentionally absent: under the
temporary success hypothesis each one-sided phase is proved to terminate,
so only the infinite trace is constructed and used by the public proofs.
-/

namespace GenLimit.UnionClosedness

/-- The data produced by the infinite branch of the alternating-phase
construction in detailed Theorem 4.1. -/
structure InfinitePhaseCertificate
    (G : GenLimit.Generic.Generator ℤ) where
  stream : ℕ → ℤ
  stream_injective : Function.Injective stream
  transitionTime : ℕ → ℕ
  omittedOutput : ℕ → ℤ
  transitionTime_strictMono : StrictMono transitionTime
  omittedOutput_injective : Function.Injective omittedOutput
  omittedOutput_positive :
    ∀ k, omittedOutput k ∈ positiveIntegers
  output_at_transition :
    ∀ k, GenLimit.Generic.output G stream (transitionTime k) =
      omittedOutput k
  omitted_forever :
    ∀ k, omittedOutput k ∉ Set.range stream
  negative_omissions_finite :
    (negativeIntegers \ Set.range stream).Finite
  no_zero_enumerated :
    Set.range stream ⊆ negativeIntegers ∪ positiveIntegers

/-- The positive points permanently skipped at phase transitions. -/
def InfinitePhaseCertificate.omittedSet
    {G : GenLimit.Generic.Generator ℤ}
    (C : InfinitePhaseCertificate G) : Set ℤ :=
  Set.range C.omittedOutput

theorem InfinitePhaseCertificate.omittedSet_infinite
    {G : GenLimit.Generic.Generator ℤ}
    (C : InfinitePhaseCertificate G) :
    C.omittedSet.Infinite :=
  Set.infinite_range_of_injective C.omittedOutput_injective

theorem InfinitePhaseCertificate.omittedSet_subset_positive
    {G : GenLimit.Generic.Generator ℤ}
    (C : InfinitePhaseCertificate G) :
    C.omittedSet ⊆ positiveIntegers := by
  rintro z ⟨k, rfl⟩
  exact C.omittedOutput_positive k

theorem InfinitePhaseCertificate.omittedSet_disjoint_target
    {G : GenLimit.Generic.Generator ℤ}
    (C : InfinitePhaseCertificate G) :
    Disjoint C.omittedSet (Set.range C.stream) := by
  rw [Set.disjoint_left]
  rintro z ⟨k, rfl⟩ hz
  exact C.omitted_forever k hz

/-- The range of an infinite phase trace belongs to the first class of
detailed Theorem 4.1. -/
theorem InfinitePhaseCertificate.target_mem_firstClass
    {G : GenLimit.Generic.Generator ℤ}
    (C : InfinitePhaseCertificate G) :
    Set.range C.stream ∈ finiteNegativeInfinitePositiveClass := by
  let B : Set ℤ := positiveIntegers \ Set.range C.stream
  let A : Set ℤ := negativeIntegers \ Set.range C.stream
  refine ⟨A, B, Set.diff_subset, C.negative_omissions_finite,
    Set.diff_subset, ?_, ?_⟩
  · apply C.omittedSet_infinite.mono
    rintro z ⟨k, rfl⟩
    exact ⟨C.omittedOutput_positive k, C.omitted_forever k⟩
  · apply Set.Subset.antisymm
    · intro z hz
      rcases C.no_zero_enumerated hz with hzneg | hzpos
      · refine Or.inl ⟨hzneg, ?_⟩
        dsimp only [A]
        intro hzA
        exact hzA.2 hz
      · refine Or.inr ⟨hzpos, ?_⟩
        dsimp only [B]
        intro hzB
        exact hzB.2 hz
    · intro z hz
      rcases hz with hzneg | hzpos
      · by_contra hzTarget
        change z ∈ negativeIntegers ∧ z ∉ A at hzneg
        apply hzneg.2
        dsimp only [A]
        exact ⟨hzneg.1, hzTarget⟩
      · by_contra hzTarget
        change z ∈ positiveIntegers ∧ z ∉ B at hzpos
        apply hzpos.2
        dsimp only [B]
        exact ⟨hzpos.1, hzTarget⟩

/-- Transition times in an infinite phase trace are unbounded. -/
theorem InfinitePhaseCertificate.exists_transition_after
    {G : GenLimit.Generic.Generator ℤ}
    (C : InfinitePhaseCertificate G) (T : ℕ) :
    ∃ k, T ≤ C.transitionTime k := by
  refine ⟨T, ?_⟩
  exact C.transitionTime_strictMono.id_le T

/-- Every recorded phase-transition output is invalid for the final target. -/
theorem InfinitePhaseCertificate.transition_not_correct
    {G : GenLimit.Generic.Generator ℤ}
    (C : InfinitePhaseCertificate G) (k : ℕ) :
    ¬GenLimit.Generic.CorrectAt G (Set.range C.stream) C.stream
      (C.transitionTime k) := by
  intro hcorrect
  apply C.omitted_forever k
  simpa [GenLimit.Generic.CorrectAt, C.output_at_transition k] using
    hcorrect.1

/-- The exact infinite-phase endgame: the trace presents a member of the
first class and defeats the proposed generator at unbounded transition
times. -/
theorem infinite_phase_endgame
    {G : GenLimit.Generic.Generator ℤ}
    (C : InfinitePhaseCertificate G) :
    Set.range C.stream ∈ finiteNegativeInfinitePositiveClass ∧
      GenLimit.Generic.Presents C.stream (Set.range C.stream) ∧
      ∀ T, ∃ t, T ≤ t ∧
        ¬GenLimit.Generic.CorrectAt G (Set.range C.stream) C.stream t := by
  refine ⟨C.target_mem_firstClass, rfl, ?_⟩
  intro T
  obtain ⟨k, hk⟩ := C.exists_transition_after T
  exact ⟨C.transitionTime k, hk, C.transition_not_correct k⟩

end GenLimit.UnionClosedness
