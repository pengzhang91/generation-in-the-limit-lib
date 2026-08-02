import GenLimit.Angluin.Definitions

/-!
# The semantic core of Angluin's sufficiency argument

This module formalizes the stabilization argument in the forward construction
of Theorem 1 of Angluin (1980), pp. 121--122.  It starts from finite-stage
approximations to the uniformly enumerated tell-tales and defines the paper's
least-index learner.

The result is intentionally named `semantic...`: the theorem proves the
mathematical correctness of the construction.  It does not erase the source's
additional requirement that the family, tell-tale enumeration, and learner be
recursive.  Those effective predicates are recorded in `Definitions.lean`.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

/-- Index `i` passes Angluin's stage test on the history `xs`: it has appeared
in the bounded index search, the tell-tale content emitted so far has appeared
in the data, and all data seen so far are consistent with `C i`. -/
def StageEligible
    (C : Generic.LanguageFamily α) (A : ℕ → ℕ → Finset α)
    {t : ℕ} (xs : Fin t → α) (i : ℕ) : Prop :=
  i ≤ t ∧
    A i t ⊆ Generic.sequenceSample xs ∧
    (↑(Generic.sequenceSample xs) : Set α) ⊆ C i

/-- Angluin's least-index learner.  If the finite stage test has no passing
index, it makes the arbitrary default guess `0`. -/
noncomputable def semanticLearner
    (C : Generic.LanguageFamily α) (A : ℕ → ℕ → Finset α) :
    SemanticIdentifier α := by
  classical
  exact fun t xs =>
    if h : ∃ i, StageEligible C A xs i then Nat.find h else 0

theorem semanticLearner_eligible
    {C : Generic.LanguageFamily α} {A : ℕ → ℕ → Finset α}
    {t : ℕ} {xs : Fin t → α}
    (h : ∃ i, StageEligible C A xs i) :
    StageEligible C A xs (semanticLearner C A t xs) := by
  classical
  rw [semanticLearner, dif_pos h]
  exact Nat.find_spec h

theorem semanticLearner_le_of_eligible
    {C : Generic.LanguageFamily α} {A : ℕ → ℕ → Finset α}
    {t i : ℕ} {xs : Fin t → α}
    (hi : StageEligible C A xs i) :
    semanticLearner C A t xs ≤ i := by
  classical
  let h : ∃ j, StageEligible C A xs j := ⟨i, hi⟩
  rw [semanticLearner, dif_pos h]
  exact Nat.find_min' h hi

/-- A fixed index denoting the target eventually passes the stage test. -/
theorem eventually_stageEligible_of_same_language
    {C : Generic.LanguageFamily α} {A : ℕ → ℕ → Finset α}
    (hA : IsTellTaleApproximation C A)
    {z i : ℕ} (hsame : C i = C z)
    {stream : Generic.Stream α} (hP : Generic.Presents stream (C z)) :
    ∃ N, ∀ t, N ≤ t →
      StageEligible C A (fun r : Fin t => stream r) i := by
  classical
  obtain ⟨T, hTell, NA, hstable⟩ := hA.2 i
  have hTz : (↑T : Set α) ⊆ C z := by
    simpa [hsame] using hTell.1
  obtain ⟨NS, hTS⟩ := Generic.finset_eventually_subset_sample hP T hTz
  refine ⟨max i (max NA NS), ?_⟩
  intro t ht
  have hit : i ≤ t := le_trans (Nat.le_max_left _ _) ht
  have hAt : A i t = T :=
    hstable t (le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) ht))
  have hNSt : NS ≤ t :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) ht)
  have hsample : Generic.sample stream NS ⊆ Generic.sample stream t :=
    Generic.sample_mono hNSt
  have hTsample : T ⊆ Generic.sample stream t :=
    fun x hx => hsample (hTS hx)
  have hsampleTarget : (↑(Generic.sample stream t) : Set α) ⊆ C z := by
    intro x hx
    exact Generic.mem_language_of_mem_sample_of_presents hP hx
  rw [StageEligible, Generic.sequenceSample_prefix]
  refine ⟨hit, ?_, ?_⟩
  · simpa [hAt] using hTsample
  · simpa [hsame] using hsampleTarget

/-- Every fixed lower index denoting a different language eventually fails one
of the two substantive stage tests.

If the target is not contained in the candidate, positive data eventually
exhibit a counterexample.  If the target is a proper subset of the candidate,
the candidate's tell-tale eventually emits an element outside the target. -/
theorem eventually_not_stageEligible_of_different_language
    {C : Generic.LanguageFamily α} {A : ℕ → ℕ → Finset α}
    (hA : IsTellTaleApproximation C A)
    {z i : ℕ} (hdiff : C i ≠ C z)
    {stream : Generic.Stream α} (hP : Generic.Presents stream (C z)) :
    ∃ N, ∀ t, N ≤ t →
      ¬StageEligible C A (fun r : Fin t => stream r) i := by
  classical
  by_cases htargetCandidate : C z ⊆ C i
  · obtain ⟨T, hTell, NA, hstable⟩ := hA.2 i
    have hnotCandidateTarget : ¬C i ⊆ C z := by
      intro hback
      exact hdiff (Set.Subset.antisymm hback htargetCandidate)
    have hnotTellTarget : ¬(↑T : Set α) ⊆ C z := by
      intro hTz
      have heq : C z = C i := hTell.eq_of_between hTz htargetCandidate
      exact hdiff heq.symm
    obtain ⟨x, hxT, hxnotTarget⟩ := Set.not_subset.mp hnotTellTarget
    refine ⟨NA, ?_⟩
    intro t ht hEligible
    have hxA : x ∈ A i t := by
      rw [hstable t ht]
      exact hxT
    have hxSequence : x ∈ Generic.sequenceSample (fun r : Fin t => stream r) :=
      hEligible.2.1 hxA
    have hxSample : x ∈ Generic.sample stream t := by
      simpa [Generic.sequenceSample_prefix] using hxSequence
    exact hxnotTarget (Generic.mem_language_of_mem_sample_of_presents hP hxSample)
  · obtain ⟨x, hxTarget, hxnotCandidate⟩ := Set.not_subset.mp htargetCandidate
    obtain ⟨N, hN⟩ := Generic.eventually_mem_sample_of_presents hP hxTarget
    refine ⟨N, ?_⟩
    intro t ht hEligible
    have hxSample : x ∈ Generic.sample stream t := hN t ht
    have hxSequence : x ∈ Generic.sequenceSample (fun r : Fin t => stream r) := by
      simpa [Generic.sequenceSample_prefix] using hxSample
    exact hxnotCandidate (hEligible.2.2 hxSequence)

/-- Finitely many pointwise eventual bounds can be made simultaneous. -/
theorem eventually_all_lt
    {P : ℕ → ℕ → Prop} {k : ℕ}
    (h : ∀ i, i < k → ∃ N, ∀ t, N ≤ t → P i t) :
    ∃ N, ∀ t, N ≤ t → ∀ i, i < k → P i t := by
  induction k with
  | zero =>
      exact ⟨0, by simp⟩
  | succ k ih =>
      have hlt : ∀ i, i < k → ∃ N, ∀ t, N ≤ t → P i t := by
        intro i hi
        exact h i (lt_trans hi (Nat.lt_succ_self k))
      obtain ⟨N₀, hN₀⟩ := ih hlt
      obtain ⟨N₁, hN₁⟩ := h k (Nat.lt_succ_self k)
      refine ⟨max N₀ N₁, ?_⟩
      intro t ht i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | rfl
      · exact hN₀ t (le_trans (Nat.le_max_left _ _) ht) i hik
      · exact hN₁ t (le_trans (Nat.le_max_right _ _) ht)

/-- Kernel-checked semantic core of the sufficiency half of Angluin's
Theorem 1: the least-index construction stabilizes syntactically to the least
index denoting the target.

No computability conclusion is asserted here.  In the paper, computability of
the family and the tell-tale enumeration makes the finite stage test and its
bounded least-index search effective. -/
theorem semanticLearner_semanticallyIdentifies
    {C : Generic.LanguageFamily α} {A : ℕ → ℕ → Finset α}
    (hA : IsTellTaleApproximation C A) :
    SemanticallyIdentifies (semanticLearner C A) C := by
  classical
  intro z stream hP
  let hex : ∃ i, C i = C z := ⟨z, rfl⟩
  let k : ℕ := Nat.find hex
  have hk : C k = C z := Nat.find_spec hex
  have hbelow : ∀ i, i < k → C i ≠ C z := by
    intro i hi
    exact Nat.find_min hex hi
  obtain ⟨Neligible, hEligible⟩ :=
    eventually_stageEligible_of_same_language hA hk hP
  have hpointwise : ∀ i, i < k → ∃ N, ∀ t, N ≤ t →
      ¬StageEligible C A (fun r : Fin t => stream r) i := by
    intro i hi
    exact eventually_not_stageEligible_of_different_language
      hA (hbelow i hi) hP
  obtain ⟨Nlower, hLower⟩ := eventually_all_lt hpointwise
  refine ⟨k, hk, ?_⟩
  refine ⟨max Neligible Nlower, ?_⟩
  intro t ht
  have htEligible : Neligible ≤ t :=
    le_trans (Nat.le_max_left _ _) ht
  have htLower : Nlower ≤ t :=
    le_trans (Nat.le_max_right _ _) ht
  have hkEligible : StageEligible C A (fun r : Fin t => stream r) k :=
    hEligible t htEligible
  have hexists : ∃ i, StageEligible C A (fun r : Fin t => stream r) i :=
    ⟨k, hkEligible⟩
  let j := semanticLearner C A t (fun r : Fin t => stream r)
  have hjEligible : StageEligible C A (fun r : Fin t => stream r) j :=
    semanticLearner_eligible hexists
  have hjle : j ≤ k := semanticLearner_le_of_eligible hkEligible
  have hjnotlt : ¬j < k := by
    intro hjlt
    exact hLower t htLower j hjlt hjEligible
  have hjk : j = k := Nat.le_antisymm hjle (Nat.not_lt.mp hjnotlt)
  exact hjk

end GenLimit.Angluin
