import GenLimit.DenseGeneration.Patient.Machine

/-!
# Invariants of the semantic patient-scope machine

This file proves that the state machine in
`GenLimit.DenseGeneration.Patient.Machine` follows
the paper's mathematical model whenever the adversary stream presents one of
the candidate languages.  The statements separate local transition facts
from the global run invariant so later validity and charging arguments can use
the branch information directly.
-/

namespace GenLimit
namespace PatientMachine

/-- If the old focus survives one more observation, criticality of every
language in the old scope is unchanged.  The old focus being maximal is the
key hypothesis: every old critical language contains it and therefore also
survives. -/
theorem critical_iff_next_of_focus_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope focus : ℕ}
    (hfocus : IsFocus C stream t scope focus)
    (hsurvives : Consistent C stream (t + 1) focus) :
    ∀ i, i < scope →
      (RecursiveCritical C stream t i ↔
        RecursiveCritical C stream (t + 1) i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hiscope
      constructor
      · intro hiold
        have hifocus : i ≤ focus := hfocus.2.2 i hiscope hiold
        have hsub : C focus ⊆ C i :=
          recursiveCritical_subset_of_le hifocus hiold hfocus.2.1
        have hinewCon : Consistent C stream (t + 1) i :=
          fun x hx => hsub (hsurvives hx)
        cases i with
        | zero => simpa [RecursiveCritical] using hinewCon
        | succ i =>
            rw [RecursiveCritical]
            refine ⟨hinewCon, ?_⟩
            intro j hji hjnew
            have hjlt : j < i + 1 := Nat.lt_succ_of_le hji
            have hjscope : j < scope := lt_trans hjlt hiscope
            have hjold : RecursiveCritical C stream t j :=
              (ih j hjlt hjscope).2 hjnew
            have hiold' : Consistent C stream t (i + 1) ∧
                ∀ k, k ≤ i → RecursiveCritical C stream t k →
                  C (i + 1) ⊆ C k := by
              simpa [RecursiveCritical] using hiold
            exact hiold'.2 j hji hjold
      · intro hinew
        have hinewCon := recursiveCritical_consistent hinew
        have hioldCon : Consistent C stream t i := by
          intro x hx
          exact hinewCon (sample_mono (Nat.le_succ t) hx)
        cases i with
        | zero => simpa [RecursiveCritical] using hioldCon
        | succ i =>
            rw [RecursiveCritical]
            refine ⟨hioldCon, ?_⟩
            intro j hji hjold
            have hjlt : j < i + 1 := Nat.lt_succ_of_le hji
            have hjscope : j < scope := lt_trans hjlt hiscope
            have hjnew : RecursiveCritical C stream (t + 1) j :=
              (ih j hjlt hjscope).1 hjold
            have hinew' : Consistent C stream (t + 1) (i + 1) ∧
                ∀ k, k ≤ i → RecursiveCritical C stream (t + 1) k →
                  C (i + 1) ⊆ C k := by
              simpa [RecursiveCritical] using hinew
            exact hinew'.2 j hji hjnew

/-- A surviving focus remains the focus when the scope is fixed. -/
theorem focus_next_of_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope focus : ℕ}
    (hfocus : IsFocus C stream t scope focus)
    (hsurvives : Consistent C stream (t + 1) focus) :
    IsFocus C stream (t + 1) scope focus := by
  refine ⟨hfocus.1, ?_, ?_⟩
  · exact (critical_iff_next_of_focus_consistent hfocus hsurvives
      focus hfocus.1).1 hfocus.2.1
  · intro j hjs hj
    exact hfocus.2.2 j hjs
      ((critical_iff_next_of_focus_consistent hfocus hsurvives j hjs).2 hj)

/-- At time zero, index zero is the unique index in scope and is critical. -/
theorem initial_focus_isFocus
    (C : LanguageFamily) (stream : ℕ → ℕ) :
    IsFocus C stream 0 initialState.scope initialState.focus := by
  simp [initialState, IsFocus, RecursiveCritical, Consistent, sample]

@[simp] theorem stableDecision_scope
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (stableDecision C stream t old).scope =
      if 2 ^ old.tau ≤ old.age then old.scope + 1 else old.scope := by
  classical
  by_cases h : 2 ^ old.tau ≤ old.age <;> simp [stableDecision, h]

@[simp] theorem stableDecision_move
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (stableDecision C stream t old).move =
      if 2 ^ old.tau ≤ old.age then .expand else .stay := by
  classical
  by_cases h : 2 ^ old.tau ≤ old.age <;> simp [stableDecision, h]

theorem stableDecision_of_not_wait
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hwait : ¬ 2 ^ old.tau ≤ old.age) :
    stableDecision C stream t old =
      ⟨old.scope, old.tau, old.focus, .stay⟩ := by
  classical
  simp [stableDecision, hwait]

theorem stableDecision_isFocus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hsurvives : Consistent C stream (t + 1) old.focus) :
    IsFocus C stream (t + 1)
      (stableDecision C stream t old).scope
      (stableDecision C stream t old).focus := by
  classical
  have hfixed := focus_next_of_consistent hfocus hsurvives
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · let newScope := old.scope + 1
    have hlt : old.focus < newScope :=
      lt_of_lt_of_le hfocus.1 (Nat.le_succ old.scope)
    have hne :
        (criticalIndices C stream (t + 1) newScope).Nonempty := by
      exact ⟨old.focus, mem_criticalIndices.mpr ⟨hlt, hfixed.2.1⟩⟩
    have hnewFocus := highestCritical_isFocus
      (fallback := old.focus) hne
    simpa [stableDecision, hwait, newScope] using hnewFocus
  · simpa [stableDecision, hwait] using hfixed

/-- In an expansion round the selected focus is never below the old focus. -/
theorem stableDecision_focus_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hsurvives : Consistent C stream (t + 1) old.focus) :
    old.focus ≤ (stableDecision C stream t old).focus := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · have hnew := stableDecision_isFocus hfocus hsurvives
    have holdNew : RecursiveCritical C stream (t + 1) old.focus :=
      (focus_next_of_consistent hfocus hsurvives).2.1
    have hlt : old.focus < (stableDecision C stream t old).scope := by
      simpa [stableDecision, hwait] using
        (lt_of_lt_of_le hfocus.1 (Nat.le_succ old.scope))
    exact hnew.2.2 old.focus hlt holdNew
  · simp [stableDecision, hwait]

/-- A stable-branch focus change can only move to the newly admitted index.
It therefore certifies that the exponential waiting condition was met. -/
theorem stableDecision_changed
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hsurvives : Consistent C stream (t + 1) old.focus)
    (hchanged : (stableDecision C stream t old).focus ≠ old.focus) :
    2 ^ old.tau ≤ old.age ∧
      (stableDecision C stream t old).focus = old.scope := by
  classical
  have hwait : 2 ^ old.tau ≤ old.age := by
    by_contra hnot
    exact hchanged (by simp [stableDecision, hnot])
  have hnew := stableDecision_isFocus hfocus hsurvives
  have hle : (stableDecision C stream t old).focus ≤ old.scope := by
    have hlt : (stableDecision C stream t old).focus < old.scope + 1 := by
      simpa [stableDecision, hwait] using hnew.1
    exact Nat.le_of_lt_succ hlt
  have hnotlt : ¬ (stableDecision C stream t old).focus < old.scope := by
    intro hlt
    have hfixed := focus_next_of_consistent hfocus hsurvives
    have hcrit := hnew.2.1
    have hbelow : (stableDecision C stream t old).focus ≤ old.focus :=
      hfixed.2.2 _ hlt hcrit
    have habove := stableDecision_focus_le hfocus hsurvives
    exact hchanged (Nat.le_antisymm hbelow habove)
  exact ⟨hwait, Nat.le_antisymm hle (Nat.le_of_not_gt hnotlt)⟩

/-- Backtracking always increments `tau` and records its branch. -/
@[simp] theorem backtrackDecision_tau
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (backtrackDecision C stream t old).tau = old.tau + 1 := by
  classical
  by_cases hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty
  · simp [backtrackDecision, hcon]
  · by_cases hall : ∃ j, Consistent C stream (t + 1) j <;>
      simp [backtrackDecision, hcon, hall]

@[simp] theorem backtrackDecision_move
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (backtrackDecision C stream t old).move = .backtrack := by
  classical
  by_cases hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty
  · simp [backtrackDecision, hcon]
  · by_cases hall : ∃ j, Consistent C stream (t + 1) j <;>
      simp [backtrackDecision, hcon, hall]

/-- Backtracking returns a genuine focus whenever some language in the whole
family remains consistent. -/
theorem backtrackDecision_isFocus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    IsFocus C stream (t + 1)
      (backtrackDecision C stream t old).scope
      (backtrackDecision C stream t old).focus := by
  classical
  let consistent := consistentIndices C stream (t + 1) old.scope
  by_cases hcon : consistent.Nonempty
  · let survivors := survivingCriticalIndices C stream t old.scope
    by_cases hsurv : survivors.Nonempty
    · let i := highestSurvivor C stream t old.scope old.focus
      have hi := highestSurvivor_spec (fallback := old.focus) hsurv
      have hifocus : IsFocus C stream (t + 1) (i + 1) i := by
        refine ⟨Nat.lt_succ_self i, hi.2.2.1, ?_⟩
        intro j hj _
        exact Nat.le_of_lt_succ hj
      simpa [backtrackDecision, consistent, hcon, survivors, hsurv, i]
        using hifocus
    · let i := lowestConsistentInScope C stream (t + 1)
        old.scope old.focus
      have hi := lowestConsistentInScope_spec
        (fallback := old.focus) hcon
      have hicrit : RecursiveCritical C stream (t + 1) i :=
        recursiveCritical_of_consistent_of_minimal hi.2.1 hi.2.2
      have hifocus : IsFocus C stream (t + 1) (i + 1) i := by
        exact ⟨Nat.lt_succ_self i, hicrit,
          fun j hj _ => Nat.le_of_lt_succ hj⟩
      simpa [backtrackDecision, consistent, hcon, survivors, hsurv, i]
        using hifocus
  · let i := lowestConsistent C stream (t + 1) old.focus
    have hi := lowestConsistent_spec (fallback := old.focus) hexists
    have hicrit : RecursiveCritical C stream (t + 1) i :=
      recursiveCritical_of_consistent_of_minimal hi.1 hi.2
    have hifocus : IsFocus C stream (t + 1) (i + 1) i := by
      exact ⟨Nat.lt_succ_self i, hicrit,
        fun j hj _ => Nat.le_of_lt_succ hj⟩
    simpa [backtrackDecision, consistent, hcon, hexists, i]
      using hifocus

theorem backtrackDecision_of_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hsurv : (survivingCriticalIndices C stream t old.scope).Nonempty) :
    backtrackDecision C stream t old =
      let i := highestSurvivor C stream t old.scope old.focus
      ⟨i + 1, old.tau + 1, i, .backtrack⟩ := by
  classical
  simp [backtrackDecision, hcon, hsurv]

theorem backtrackDecision_of_no_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hsurv : ¬ (survivingCriticalIndices C stream t old.scope).Nonempty) :
    backtrackDecision C stream t old =
      let i := lowestConsistentInScope C stream (t + 1)
        old.scope old.focus
      ⟨i + 1, old.tau + 1, i, .backtrack⟩ := by
  classical
  simp [backtrackDecision, hcon, hsurv]

theorem backtrackDecision_of_empty_scope
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hcon : ¬ (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    backtrackDecision C stream t old =
      let i := lowestConsistent C stream (t + 1) old.focus
      ⟨i + 1, old.tau + 1, i, .backtrack⟩ := by
  classical
  simp [backtrackDecision, hcon, hexists]

/-- With a surviving old critical language, backtracking lands strictly below
the falsified old focus. -/
theorem backtrackDecision_focus_lt_of_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hfalsified : ¬ Consistent C stream (t + 1) old.focus)
    (hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hsurv : (survivingCriticalIndices C stream t old.scope).Nonempty) :
    (backtrackDecision C stream t old).focus < old.focus := by
  classical
  let i := highestSurvivor C stream t old.scope old.focus
  have hi := highestSurvivor_spec (fallback := old.focus) hsurv
  have hile : i ≤ old.focus := hfocus.2.2 i hi.1 hi.2.1
  have hine : i ≠ old.focus := by
    intro hieq
    apply hfalsified
    rw [← hieq]
    exact recursiveCritical_consistent hi.2.2.1
  have hilt : i < old.focus := lt_of_le_of_ne hile hine
  simpa [backtrackDecision_of_survivor hcon hsurv, i] using hilt

/-- If no consistent language remains in the old scope, the selected global
minimum lies weakly beyond that scope. -/
theorem backtrackDecision_scope_le_focus_of_empty
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hcon : ¬ (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    old.scope ≤ (backtrackDecision C stream t old).focus := by
  classical
  let i := lowestConsistent C stream (t + 1) old.focus
  have hi := (lowestConsistent_spec (fallback := old.focus) hexists).1
  have hnotlt : ¬ i < old.scope := by
    intro hlt
    apply hcon
    exact ⟨i, mem_consistentIndices.mpr ⟨hlt, hi⟩⟩
  have hiscope : old.scope ≤ i := Nat.le_of_not_gt hnotlt
  simpa [backtrackDecision_of_empty_scope hcon hexists, i] using hiscope

@[simp] theorem stableDecision_tau
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (stableDecision C stream t old).tau =
      if (stableDecision C stream t old).focus = old.focus then
        old.tau else old.tau + 1 := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp [stableDecision, hwait]
  · simp [stableDecision, hwait]

theorem stableDecision_tau_mono
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    old.tau ≤ (stableDecision C stream t old).tau := by
  classical
  rw [stableDecision_tau]
  split <;> omega

/-- The complete focus decision is well-formed under the abstract on-model
condition that at least one language remains consistent. -/
theorem decide_isFocus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    IsFocus C stream (t + 1)
      (decide C stream t old).scope
      (decide C stream t old).focus := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · simpa [decide, hcon] using stableDecision_isFocus hfocus hcon
  · simpa [decide, hcon] using backtrackDecision_isFocus hexists

theorem decide_tau_mono
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    old.tau ≤ (decide C stream t old).tau := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · simpa [decide, hcon] using stableDecision_tau_mono C stream t old
  · simp [decide, hcon]

/-- On model, `tau` stays fixed exactly when the focus stays fixed; otherwise
it increases by one. -/
theorem decide_tau_eq_focus_test
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    (decide C stream t old).tau =
      if (decide C stream t old).focus = old.focus then
        old.tau else old.tau + 1 := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · simp [decide, hcon, stableDecision_tau]
  · have hnewFocus := decide_isFocus hfocus hexists
    have hnewCon := recursiveCritical_consistent hnewFocus.2.1
    have hne : (decide C stream t old).focus ≠ old.focus := by
      intro heq
      exact hcon (heq ▸ hnewCon)
    have hneBack : (backtrackDecision C stream t old).focus ≠ old.focus := by
      simpa [decide, hcon] using hne
    simp [decide, hcon, hneBack]

@[simp] theorem processRound_scope
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).scope =
      (decide O.language stream t old).scope := by
  simp [processRound]

@[simp] theorem processRound_tau
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).tau =
      (decide O.language stream t old).tau := by
  simp [processRound]

@[simp] theorem processRound_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).focus =
      (decide O.language stream t old).focus := by
  simp [processRound]

@[simp] theorem processRound_age
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).age =
      if (decide O.language stream t old).focus = old.focus then
        old.age + 1 else 1 := by
  simp [processRound]

@[simp] theorem processRound_move
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).move =
      (decide O.language stream t old).move := by
  simp [processRound]

@[simp] theorem processRound_used
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).used =
      insert
        (leastAvailable O.language O.infinite' stream (t + 1) old.used
          (decide O.language stream t old).focus)
        old.used := by
  simp [processRound]

@[simp] theorem run_succ_scope
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).scope =
      (decide O.language stream t (run O stream t)).scope := by
  simp

@[simp] theorem run_succ_tau
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).tau =
      (decide O.language stream t (run O stream t)).tau := by
  simp

@[simp] theorem run_succ_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).focus =
      (decide O.language stream t (run O stream t)).focus := by
  simp

@[simp] theorem run_succ_age
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).age =
      if (run O stream (t + 1)).focus = (run O stream t).focus then
        (run O stream t).age + 1 else 1 := by
  simp

@[simp] theorem run_succ_move
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).move =
      (decide O.language stream t (run O stream t)).move := by
  simp

/-- The semantic machine is on-model when at least one candidate language is
consistent after every finite observation prefix.  Exact presentation of a
family member is one sufficient condition, but partial enumeration supplies
the same invariant without presenting any member of the family exactly. -/
def OnModel (O : OracleFamily) (stream : ℕ → ℕ) : Prop :=
  ∀ t, ∃ i, Consistent O.language stream t i

/-- The semantic machine's focus is well-formed whenever the run is
on-model. -/
theorem run_focus_isFocus_of_onModel
    (O : OracleFamily) {stream : ℕ → ℕ}
    (hOn : OnModel O stream) :
    ∀ t, IsFocus O.language stream t
      (run O stream t).scope (run O stream t).focus := by
  intro t
  induction t with
  | zero => simpa using initial_focus_isFocus O.language stream
  | succ t ih =>
      have hexists : ∃ i, Consistent O.language stream (t + 1) i :=
        hOn (t + 1)
      have hnext := decide_isFocus ih hexists
      simpa using hnext

/-- An exact presentation of a family member is an on-model run. -/
theorem onModel_of_presents
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) : OnModel O stream := by
  intro t
  exact ⟨z, presents_consistent hP⟩

/-- The semantic machine's focus is well-formed at every time along a target
presentation. -/
theorem run_focus_isFocus
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∀ t, IsFocus O.language stream t
      (run O stream t).scope (run O stream t).focus :=
  run_focus_isFocus_of_onModel O (onModel_of_presents O hP)

theorem run_scope_pos
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) (t : ℕ) :
    0 < (run O stream t).scope := by
  have hf := run_focus_isFocus O hP t
  exact lt_of_le_of_lt (Nat.zero_le _) hf.1

theorem run_tau_step_mono
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream t).tau ≤ (run O stream (t + 1)).tau := by
  simpa using decide_tau_mono O.language stream t (run O stream t)

theorem run_tau_pos
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    0 < (run O stream t).tau := by
  induction t with
  | zero => simp [initialState]
  | succ t ih => exact lt_of_lt_of_le ih (run_tau_step_mono O stream t)

theorem run_age_pos_succ
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    0 < (run O stream (t + 1)).age := by
  rw [run_succ_age]
  split <;> omega

theorem run_tau_eq_focus_test
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) (t : ℕ) :
    (run O stream (t + 1)).tau =
      if (run O stream (t + 1)).focus = (run O stream t).focus then
        (run O stream t).tau else (run O stream t).tau + 1 := by
  have hfocus := run_focus_isFocus O hP t
  have hexists : ∃ i, Consistent O.language stream (t + 1) i :=
    ⟨z, presents_consistent hP⟩
  have htau := decide_tau_eq_focus_test hfocus hexists
  simpa using htau

theorem run_tau_succ_eq_iff_focus_eq
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) (t : ℕ) :
    (run O stream (t + 1)).tau = (run O stream t).tau ↔
      (run O stream (t + 1)).focus = (run O stream t).focus := by
  rw [run_tau_eq_focus_test O hP t]
  split <;> rename_i h
  · simpa using h
  · omega

theorem run_tau_succ_eq_add_one_iff_focus_ne
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) (t : ℕ) :
    (run O stream (t + 1)).tau = (run O stream t).tau + 1 ↔
      (run O stream (t + 1)).focus ≠ (run O stream t).focus := by
  rw [run_tau_eq_focus_test O hP t]
  split
  · omega
  · simp_all

/-- The finite set of outputs in rounds strictly before `t`. -/
noncomputable def outputsBefore
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).image (output O stream)

theorem run_used_eq_outputsBefore
    (O : OracleFamily) (stream : ℕ → ℕ) :
    ∀ t, (run O stream t).used = outputsBefore O stream t := by
  intro t
  induction t with
  | zero => simp [outputsBefore, initialState]
  | succ t ih =>
      simp [outputsBefore, Finset.range_add_one, processRound, ih,
        output_eq_leastAvailable]

theorem output_mem_run_used
    (O : OracleFamily) (stream : ℕ → ℕ) {s t : ℕ} (hst : s < t) :
    output O stream s ∈ (run O stream t).used := by
  rw [run_used_eq_outputsBefore]
  exact Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hst, rfl⟩

theorem output_not_mem_sample
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∉ sample stream (t + 1) :=
  (output_available O stream t).2.1

theorem output_not_mem_prior_used
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∉ (run O stream t).used :=
  (output_available O stream t).2.2

theorem output_mem_round_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∈ O.language (run O stream (t + 1)).focus := by
  simpa using (output_available O stream t).1

/-- Generator announcements are pairwise distinct. -/
theorem output_ne_of_lt
    (O : OracleFamily) (stream : ℕ → ℕ) {s t : ℕ} (hst : s < t) :
    output O stream s ≠ output O stream t := by
  intro heq
  have hmem := output_mem_run_used O stream hst
  rw [heq] at hmem
  exact output_not_mem_prior_used O stream t hmem

/-- The round-`t` generator output differs from every adversary announcement
through round `t`. -/
theorem stream_ne_output
    (O : OracleFamily) (stream : ℕ → ℕ) (t s : ℕ) (hst : s ≤ t) :
    stream s ≠ output O stream t := by
  intro heq
  have hmem : stream s ∈ sample stream (t + 1) :=
    value_mem_sample (Nat.lt_succ_of_le hst)
  rw [heq] at hmem
  exact output_not_mem_sample O stream t hmem

end PatientMachine
end GenLimit
