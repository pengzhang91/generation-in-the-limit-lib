import GenLimit.DenseGeneration.Patient.Machine

/-!
# Recurrence and history facts for the patient-scope machine

This module derives facts that depend only on the recurrence in
`PatientMachine.processRound`.  They are kept separate from the semantic
focus/scope invariants used to prove eventual validity.

Because `PatientMachine` is total on arbitrary streams, its off-model
backtracking fallback can increment `tau` while retaining the old focus when
no consistent language exists.  Thus the unrestricted converse “unchanged
focus implies unchanged `tau`” is false.  Below it is stated under the natural
condition that the old focus remains consistent; a presentation-dependent
version can instead discharge the off-model branch using existence of the
true consistent language.
-/

namespace GenLimit
namespace PatientMachine

/-- A stable-focus decision either preserves `tau` or increments it once. -/
theorem stableDecision_tau_cases
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    let d := stableDecision C stream t old
    d.tau = old.tau ∨ d.tau = old.tau + 1 := by
  classical
  simp only [stableDecision]
  split
  · dsimp
    split <;> simp
  · simp

/-- A focus change made by the stable branch increments `tau` exactly once. -/
theorem stableDecision_tau_eq_succ_of_focus_ne
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hfocus : (stableDecision C stream t old).focus ≠ old.focus) :
    (stableDecision C stream t old).tau = old.tau + 1 := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · by_cases heq :
        highestCritical C stream (t + 1) (old.scope + 1) old.focus =
          old.focus
    · simp [stableDecision, hwait, heq] at hfocus
    · simp [stableDecision, hwait, heq]
  · simp [stableDecision, hwait] at hfocus

/-- If the stable branch retains the focus, it retains `tau`. -/
theorem stableDecision_tau_eq_of_focus_eq
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hfocus : (stableDecision C stream t old).focus = old.focus) :
    (stableDecision C stream t old).tau = old.tau := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · have heq :
        highestCritical C stream (t + 1) (old.scope + 1) old.focus =
          old.focus := by
      simpa [stableDecision, hwait] using hfocus
    simp [stableDecision, hwait, heq]
  · simp [stableDecision, hwait]

/-- Every backtracking decision increments `tau` exactly once, including the
totalized off-model branch. -/
theorem backtrackDecision_tau_eq_succ
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (backtrackDecision C stream t old).tau = old.tau + 1 := by
  classical
  by_cases hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty
  · simp [backtrackDecision, hcon]
  · by_cases hall : ∃ j, Consistent C stream (t + 1) j
    · simp [backtrackDecision, hcon, hall]
    · simp [backtrackDecision, hcon, hall]

/-- If at least one language is consistent, the focus selected by
backtracking is consistent.  This excludes only the explicitly totalized
off-model fallback. -/
theorem backtrackDecision_focus_consistent_of_exists
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hall : ∃ i, Consistent C stream (t + 1) i) :
    Consistent C stream (t + 1)
      (backtrackDecision C stream t old).focus := by
  classical
  by_cases hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty
  · by_cases hsurv :
        (survivingCriticalIndices C stream t old.scope).Nonempty
    · have hspec := highestSurvivor_spec
          (C := C) (stream := stream) (t := t) (scope := old.scope)
          (fallback := old.focus) hsurv
      have hcrit : RecursiveCritical C stream (t + 1)
          (highestSurvivor C stream t old.scope old.focus) := hspec.2.2.1
      have hfocus :
          (backtrackDecision C stream t old).focus =
            highestSurvivor C stream t old.scope old.focus := by
        simp [backtrackDecision, hcon, hsurv, highestSurvivor]
      rw [hfocus]
      exact recursiveCritical_consistent hcrit
    · have hspec := lowestConsistentInScope_spec
          (C := C) (stream := stream) (t := t + 1)
          (scope := old.scope) (fallback := old.focus) hcon
      have hfocus :
          (backtrackDecision C stream t old).focus =
            lowestConsistentInScope C stream (t + 1) old.scope old.focus := by
        simp [backtrackDecision, hcon, hsurv, lowestConsistentInScope]
      rw [hfocus]
      exact hspec.2.1
  · have hspec := lowestConsistent_spec
        (C := C) (stream := stream) (t := t + 1)
        (fallback := old.focus) hall
    have hfocus :
        (backtrackDecision C stream t old).focus =
          lowestConsistent C stream (t + 1) old.focus := by
      simp [backtrackDecision, hcon, hall]
    rw [hfocus]
    exact hspec.1

/-- Every decision either preserves `tau` or increments it once. -/
theorem decide_tau_cases
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    let d := decide C stream t old
    d.tau = old.tau ∨ d.tau = old.tau + 1 := by
  classical
  simp only [decide]
  split
  · exact stableDecision_tau_cases C stream t old
  · exact Or.inr (backtrackDecision_tau_eq_succ C stream t old)

/-- Any decision which changes focus increments `tau` exactly once. -/
theorem decide_tau_eq_succ_of_focus_ne
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hfocus : (decide C stream t old).focus ≠ old.focus) :
    (decide C stream t old).tau = old.tau + 1 := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · have hfocus' :
        (stableDecision C stream t old).focus ≠ old.focus := by
      simpa [decide, hcon] using hfocus
    simpa [decide, hcon] using
      stableDecision_tau_eq_succ_of_focus_ne C stream t old hfocus'
  · simpa [decide, hcon] using
      backtrackDecision_tau_eq_succ C stream t old

/-- When the old focus remains consistent, an unchanged focus implies an
unchanged `tau`; this excludes the backtracking fallback. -/
theorem decide_tau_eq_of_focus_eq_of_consistent
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hcon : Consistent C stream (t + 1) old.focus)
    (hfocus : (decide C stream t old).focus = old.focus) :
    (decide C stream t old).tau = old.tau := by
  classical
  rw [decide, if_pos hcon] at hfocus ⊢
  exact stableDecision_tau_eq_of_focus_eq C stream t old hfocus

/-- In any on-model round with at least one consistent language, retaining
the focus is equivalent, as far as the recurrence is concerned, to retaining
`tau`. -/
theorem decide_tau_eq_of_focus_eq_of_exists_consistent
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hall : ∃ i, Consistent C stream (t + 1) i)
    (hfocus : (decide C stream t old).focus = old.focus) :
    (decide C stream t old).tau = old.tau := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · exact decide_tau_eq_of_focus_eq_of_consistent
      C stream t old hcon hfocus
  · have hbackFocus :
        (backtrackDecision C stream t old).focus = old.focus := by
      simpa [decide, hcon] using hfocus
    have hbackCon :=
      backtrackDecision_focus_consistent_of_exists C stream t old hall
    rw [hbackFocus] at hbackCon
    exact False.elim (hcon hbackCon)

/-- A completed round either preserves `tau` or increments it once. -/
theorem processRound_tau_cases
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).tau = old.tau ∨
      (processRound O stream t old).tau = old.tau + 1 := by
  simpa only [processRound] using
    decide_tau_cases O.language stream t old

/-- `tau` never decreases in one completed round. -/
theorem processRound_tau_mono
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    old.tau ≤ (processRound O stream t old).tau := by
  rcases processRound_tau_cases O stream t old with h | h
  · omega
  · omega

/-- A round which changes focus increments `tau` exactly once. -/
theorem processRound_tau_eq_succ_of_focus_ne
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hfocus : (processRound O stream t old).focus ≠ old.focus) :
    (processRound O stream t old).tau = old.tau + 1 := by
  apply decide_tau_eq_succ_of_focus_ne O.language stream t old
  simpa only [processRound] using hfocus

/-- On the consistent-focus branch, a round which retains the focus also
retains `tau`. -/
theorem processRound_tau_eq_of_focus_eq_of_consistent
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hcon : Consistent O.language stream (t + 1) old.focus)
    (hfocus : (processRound O stream t old).focus = old.focus) :
    (processRound O stream t old).tau = old.tau := by
  apply decide_tau_eq_of_focus_eq_of_consistent
    O.language stream t old hcon
  simpa only [processRound] using hfocus

/-- In an on-model round with a consistent candidate somewhere in the
family, an unchanged focus implies unchanged `tau`. -/
theorem processRound_tau_eq_of_focus_eq_of_exists_consistent
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hall : ∃ i, Consistent O.language stream (t + 1) i)
    (hfocus : (processRound O stream t old).focus = old.focus) :
    (processRound O stream t old).tau = old.tau := by
  apply decide_tau_eq_of_focus_eq_of_exists_consistent
    O.language stream t old hall
  simpa only [processRound] using hfocus

/-- The age stored after every completed round is positive. -/
theorem processRound_age_pos
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    0 < (processRound O stream t old).age := by
  classical
  by_cases hfocus : (decide O.language stream t old).focus = old.focus
  · simp [processRound, hfocus]
  · simp [processRound, hfocus]

/-- `tau` never decreases along the `run` recurrence. -/
theorem run_tau_le_succ
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream t).tau ≤ (run O stream (t + 1)).tau := by
  rw [run_succ]
  exact processRound_tau_mono O stream t (run O stream t)

/-- `tau` is globally monotone along the run. -/
theorem run_tau_mono
    (O : OracleFamily) (stream : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    (run O stream s).tau ≤ (run O stream t).tau := by
  induction t generalizing s with
  | zero =>
      have hs : s = 0 := Nat.eq_zero_of_le_zero hst
      subst s
      exact Nat.le_refl _
  | succ t ih =>
      rcases eq_or_lt_of_le hst with hEq | hlt
      · subst s
        exact Nat.le_refl _
      · exact le_trans (ih (Nat.le_of_lt_succ hlt))
          (run_tau_le_succ O stream t)

/-- A focus change between consecutive run states increments `tau` exactly
once. -/
theorem run_succ_tau_eq_succ_of_focus_ne
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ)
    (hfocus : (run O stream (t + 1)).focus ≠
      (run O stream t).focus) :
    (run O stream (t + 1)).tau = (run O stream t).tau + 1 := by
  rw [run_succ] at hfocus ⊢
  exact processRound_tau_eq_succ_of_focus_ne
    O stream t (run O stream t) hfocus

/-- Every noninitial run state has positive age. -/
theorem run_succ_age_pos
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    0 < (run O stream (t + 1)).age := by
  rw [run_succ]
  exact processRound_age_pos O stream t (run O stream t)

/-- Along a genuine presentation, an unchanged focus between consecutive run
states implies unchanged `tau`. -/
theorem run_succ_tau_eq_of_focus_eq
    (O : OracleFamily) (stream : ℕ → ℕ) {z t : ℕ}
    (hP : Presents stream (O.language z))
    (hfocus : (run O stream (t + 1)).focus =
      (run O stream t).focus) :
    (run O stream (t + 1)).tau = (run O stream t).tau := by
  rw [run_succ] at hfocus ⊢
  apply processRound_tau_eq_of_focus_eq_of_exists_consistent
    O stream t (run O stream t) ⟨z, presents_consistent hP⟩ hfocus

/-- The recorded age never exceeds the number of completed rounds. -/
theorem run_age_le_time
    (O : OracleFamily) (stream : ℕ → ℕ) :
    ∀ t, (run O stream t).age ≤ t := by
  intro t
  induction t with
  | zero => simp [initialState]
  | succ t ih =>
      classical
      rw [run_succ]
      simp [processRound]
      split <;> omega

/-- Looking back fewer than `age` completed rounds reaches a post-state with
the same focus.  The indices `t - k`, for `k < age`, are exactly the last
`age` completed-round post-states, including the current state at `k = 0`. -/
theorem run_focus_eq_of_lt_age
    (O : OracleFamily) (stream : ℕ → ℕ) :
    ∀ t k, k < (run O stream t).age →
      (run O stream (t - k)).focus = (run O stream t).focus := by
  intro t
  induction t with
  | zero =>
      intro k hk
      simp [initialState] at hk
  | succ t ih =>
      intro k hk
      classical
      by_cases hk0 : k = 0
      · subst k
        simp
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        by_cases hsame :
            (decide O.language stream t (run O stream t)).focus =
              (run O stream t).focus
        ·
          simp [run_succ, processRound, hsame] at hk
          have hj : j < (run O stream t).age := by omega
          have hprev := ih j hj
          simpa [run_succ, processRound, hsame] using hprev
        · have hage : (run O stream (t + 1)).age = 1 := by
            simp [run_succ, processRound, hsame]
          omega

/-- The used set recurrence inserts precisely the output of the new round. -/
theorem run_succ_used
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).used =
      insert (output O stream t) (run O stream t).used := by
  classical
  rw [run_succ]
  simp [processRound, output_eq_leastAvailable]

/-- The used set after `t` rounds is exactly the image of all earlier
outputs. -/
theorem run_used_eq_image_outputs
    (O : OracleFamily) (stream : ℕ → ℕ) :
    ∀ t, (run O stream t).used =
      (Finset.range t).image (output O stream) := by
  intro t
  induction t with
  | zero => simp [initialState]
  | succ t ih =>
      rw [run_succ_used, ih, Finset.range_add_one, Finset.image_insert]

/-- Membership in `used` is equivalent to occurrence as an earlier output. -/
theorem mem_run_used_iff
    (O : OracleFamily) (stream : ℕ → ℕ) {t x : ℕ} :
    x ∈ (run O stream t).used ↔
      ∃ r, r < t ∧ output O stream r = x := by
  classical
  rw [run_used_eq_image_outputs]
  simp

/-- The current output is fresh relative to all earlier outputs. -/
theorem output_not_mem_run_used
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∉ (run O stream t).used :=
  (output_available O stream t).2.2

/-- The round-`t` output has not appeared in the adversary stream through
round `t`. -/
theorem output_not_mem_adversary_sample
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∉ sample stream (t + 1) :=
  (output_available O stream t).2.1

/-- Generator outputs never repeat. -/
theorem output_injective
    (O : OracleFamily) (stream : ℕ → ℕ) :
    Function.Injective (output O stream) := by
  intro r t hrt
  rcases lt_trichotomy r t with hlt | heq | hgt
  · have hmem : output O stream r ∈ (run O stream t).used :=
      mem_run_used_iff O stream |>.2 ⟨r, hlt, rfl⟩
    have hfresh := output_not_mem_run_used O stream t
    exact False.elim (hfresh (hrt ▸ hmem))
  · exact heq
  · have hmem : output O stream t ∈ (run O stream r).used :=
      mem_run_used_iff O stream |>.2 ⟨t, hgt, rfl⟩
    have hfresh := output_not_mem_run_used O stream r
    exact False.elim (hfresh (hrt.symm ▸ hmem))

end PatientMachine
end GenLimit
