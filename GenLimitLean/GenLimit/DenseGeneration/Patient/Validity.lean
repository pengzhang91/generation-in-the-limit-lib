import GenLimit.DenseGeneration.Patient.MachineInvariant
import GenLimit.DenseGeneration.Patient.History
import GenLimit.Core.TargetStability
import GenLimit.Core.PartialPresentation
import GenLimit.DenseGeneration.Dynamics

/-!
# Validity of the semantic patient-scope machine

This file proves Lemma 3.11 for the semantic machine.  The proof has two
parts.  First, after consistency stabilizes on the finite target prefix, a
scope not yet containing the target must eventually increase.  Second, once
the target is critical and lies in scope, every later transition keeps it in
scope.  The selected focus is then contained in the target, so every output is
a fresh target element.
-/

namespace GenLimit
namespace PatientMachine

/-- `processRound` preserves the focus well-formedness supplied by `decide`. -/
theorem processRound_isFocus
    {O : OracleFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus O.language stream t old.scope old.focus)
    (hexists : ∃ i, Consistent O.language stream (t + 1) i) :
    IsFocus O.language stream (t + 1)
      (processRound O stream t old).scope
      (processRound O stream t old).focus := by
  simpa only [processRound] using decide_isFocus hfocus hexists

/-- Compatibility name for the post-round focus membership fact.  New code
uses `output_mem_round_focus`; this alias preserves audited downstream source
anchors. -/
theorem output_mem_run_succ_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∈ O.language (run O stream (t + 1)).focus :=
  output_mem_round_focus O stream t

/-- If the target is critical both before and after a transition and is in
the old scope, the new scope still contains it. -/
theorem processRound_preserves_target_in_scope
    {O : OracleFamily} {stream : ℕ → ℕ} {t z : ℕ} {old : State}
    (hzscope : z < old.scope)
    (hzold : RecursiveCritical O.language stream t z)
    (hznew : RecursiveCritical O.language stream (t + 1) z) :
    z < (processRound O stream t old).scope := by
  classical
  by_cases hcon : Consistent O.language stream (t + 1) old.focus
  · simp only [processRound]
    rw [decide, if_pos hcon]
    rw [stableDecision_scope]
    split <;> omega
  · have hscopeCon :
        (consistentIndices O.language stream (t + 1) old.scope).Nonempty :=
      ⟨z, mem_consistentIndices.mpr
        ⟨hzscope, recursiveCritical_consistent hznew⟩⟩
    have hsurv :
        (survivingCriticalIndices O.language stream t old.scope).Nonempty :=
      ⟨z, mem_survivingCriticalIndices.mpr
        ⟨hzscope, hzold, hznew⟩⟩
    let i := highestSurvivor O.language stream t old.scope old.focus
    have hi := highestSurvivor_spec
      (C := O.language) (stream := stream) (t := t)
      (scope := old.scope) (fallback := old.focus) hsurv
    have hzi : z ≤ i := hi.2.2.2 z hzscope hzold hznew
    simp only [processRound]
    rw [decide, if_neg hcon]
    rw [backtrackDecision_of_survivor hscopeCon hsurv]
    simpa [i] using Nat.lt_succ_of_le hzi

/-- Once the target is eventually critical and has entered the scope, it
remains in scope forever. -/
theorem target_in_scope_persistent
    (O : OracleFamily) (stream : ℕ → ℕ) {z T t : ℕ}
    (hcrit : ∀ u, T ≤ u → RecursiveCritical O.language stream u z)
    (hTt : T ≤ t) (hzscope : z < (run O stream t).scope) :
    ∀ u, t ≤ u → z < (run O stream u).scope := by
  intro u htu
  induction u, htu using Nat.le_induction with
  | base => exact hzscope
  | succ u htu ih =>
      rw [run_succ]
      apply processRound_preserves_target_in_scope
        ih
      · exact hcrit u (le_trans hTt htu)
      · exact hcrit (u + 1) (by omega)

/-- Once consistency has stabilized on indices through `w`, a scope not yet
containing `w` must later increase.  The presented set need not itself be one
of the indexed languages; `hOn` supplies the weaker on-model invariant needed
to keep the machine focus well-formed. -/
theorem exists_later_scope_increase_below_witness
    (O : OracleFamily) (stream : ℕ → ℕ) {E : Language} {w T t : ℕ}
    (hP : Presents stream E)
    (hOn : OnModel O stream)
    (hstable : ∀ u, T ≤ u → ∀ i, i ≤ w →
      (Consistent O.language stream u i ↔ E ⊆ O.language i))
    (hTt : T ≤ t)
    (hscope : (run O stream t).scope ≤ w) :
    ∃ u, t < u ∧
      (run O stream t).scope < (run O stream u).scope := by
  generalize hn :
      2 ^ (run O stream t).tau - (run O stream t).age = n
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
      let old := run O stream t
      have hfocus := run_focus_isFocus_of_onModel O hOn t
      have hfocusLe : old.focus ≤ w :=
        le_trans (Nat.le_of_lt hfocus.1) hscope
      have hfocusCon : Consistent O.language stream t old.focus :=
        recursiveCritical_consistent hfocus.2.1
      have hESub : E ⊆ O.language old.focus :=
        (hstable t hTt old.focus hfocusLe).1 hfocusCon
      have hnextCon : Consistent O.language stream (t + 1) old.focus :=
        consistent_of_presented_subset hP hESub
      by_cases hwait : 2 ^ old.tau ≤ old.age
      · refine ⟨t + 1, Nat.lt_succ_self t, ?_⟩
        simp [run_succ, processRound, decide, hnextCon,
          stableDecision, hwait, old]
      · have hnextScope :
            (run O stream (t + 1)).scope = old.scope := by
          simp [run_succ, processRound, decide, hnextCon,
            stableDecision, hwait, old]
        have hnextTau : (run O stream (t + 1)).tau = old.tau := by
          simp [run_succ, processRound, decide, hnextCon,
            stableDecision, hwait, old]
        have hnextAge : (run O stream (t + 1)).age = old.age + 1 := by
          simp [run_succ, processRound, decide, hnextCon,
            stableDecision, hwait, old]
        have hageLt : old.age < 2 ^ old.tau := Nat.lt_of_not_ge hwait
        have hmeasureCore :
            2 ^ old.tau - (old.age + 1) <
              2 ^ old.tau - old.age := by
          omega
        have hmeasureLt :
            2 ^ (run O stream (t + 1)).tau -
                (run O stream (t + 1)).age < n := by
          calc
            2 ^ (run O stream (t + 1)).tau -
                (run O stream (t + 1)).age =
                2 ^ old.tau - (old.age + 1) := by
                  rw [hnextTau, hnextAge]
            _ < 2 ^ old.tau - old.age := hmeasureCore
            _ = n := by simpa [old] using hn
        have hscopeNext : (run O stream (t + 1)).scope ≤ w := by
          rw [hnextScope]
          simpa [old] using hscope
        obtain ⟨u, htu, huScope⟩ := ih _ hmeasureLt
          (t := t + 1) (by omega) hscopeNext
          rfl
        refine ⟨u, lt_trans (Nat.lt_succ_self t) htu, ?_⟩
        have : old.scope < (run O stream u).scope := by
          rw [← hnextScope]
          exact huScope
        simpa [old] using this

/-- Exact-presentation specialization of
`exists_later_scope_increase_below_witness`. -/
theorem exists_later_scope_increase_below_target
    (O : OracleFamily) (stream : ℕ → ℕ) {z T t : ℕ}
    (hP : Presents stream (O.language z))
    (hstable : ∀ u, T ≤ u → ∀ i, i ≤ z →
      (Consistent O.language stream u i ↔ O.language z ⊆ O.language i))
    (hTt : T ≤ t)
    (hscope : (run O stream t).scope ≤ z) :
    ∃ u, t < u ∧
      (run O stream t).scope < (run O stream u).scope :=
  exists_later_scope_increase_below_witness O stream hP
    (onModel_of_presents O hP) hstable hTt hscope

/-- An eventually permanent critical witness eventually enters the patient
scope and remains there. -/
theorem critical_witness_eventually_in_scope
    (O : OracleFamily) (stream : ℕ → ℕ) {E : Language} {w Tc : ℕ}
    (hP : Presents stream E)
    (hOn : OnModel O stream)
    (hcrit : ∀ t, Tc ≤ t → RecursiveCritical O.language stream t w) :
    ∃ T, ∀ t, T ≤ t → w < (run O stream t).scope := by
  obtain ⟨Ts, hstable⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := O.language) hP (w + 1)
  let T0 := max Ts Tc
  have hTs : Ts ≤ T0 := Nat.le_max_left _ _
  have hTc : Tc ≤ T0 := Nat.le_max_right _ _
  have hreachFrom : ∀ t, T0 ≤ t →
      ∃ u, t ≤ u ∧ w < (run O stream u).scope := by
    intro t hT0t
    generalize hn : w + 1 - (run O stream t).scope = n
    induction n using Nat.strong_induction_on generalizing t with
    | h n ih =>
        by_cases hwscope : w < (run O stream t).scope
        · exact ⟨t, Nat.le_refl _, hwscope⟩
        · have hscope : (run O stream t).scope ≤ w :=
            Nat.le_of_not_gt hwscope
          obtain ⟨u, htu, hinc⟩ :=
            exists_later_scope_increase_below_witness O stream hP hOn
              (fun v hv i hi => hstable v (le_trans hTs hv) i
                (Nat.lt_succ_of_le hi))
              hT0t hscope
          by_cases huw : w < (run O stream u).scope
          · exact ⟨u, Nat.le_of_lt htu, huw⟩
          · have huscope : (run O stream u).scope ≤ w :=
              Nat.le_of_not_gt huw
            have hmeasureLt :
                w + 1 - (run O stream u).scope < n := by
              rw [← hn]
              omega
            obtain ⟨v, huv, hvscope⟩ := ih _ hmeasureLt
              (t := u) (le_trans hT0t (Nat.le_of_lt htu)) rfl
            exact ⟨v, le_trans (Nat.le_of_lt htu) huv, hvscope⟩
  have hreach : ∃ u, T0 ≤ u ∧ w < (run O stream u).scope :=
    hreachFrom T0 (Nat.le_refl _)
  obtain ⟨u, hT0u, huscope⟩ := hreach
  refine ⟨u, ?_⟩
  intro t hut
  exact target_in_scope_persistent O stream
    (fun v hv => hcrit v (le_trans hTc (le_trans hT0u hv)))
    (Nat.le_refl u) huscope t hut

/-- The patient scope eventually contains an exactly presented target and
never loses it. -/
theorem target_eventually_in_scope
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∃ T, ∀ t, T ≤ t → z < (run O stream t).scope := by
  obtain ⟨Tc, hcrit⟩ := target_eventually_recursiveCritical hP
  exact critical_witness_eventually_in_scope O stream hP
    (onModel_of_presents O hP) hcrit

/-- Lemma 3.11: the semantic patient-scope generator eventually outputs fresh
elements of the presented target language.  Freshness and injectivity are
available separately as `output_not_mem_sample` and `output_injective`. -/
theorem patient_validity
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∃ T, ∀ t, T ≤ t → output O stream t ∈ O.language z := by
  obtain ⟨Ts, hscope⟩ := target_eventually_in_scope O stream hP
  obtain ⟨Tc, hcrit⟩ := target_eventually_recursiveCritical hP
  refine ⟨max Ts Tc, ?_⟩
  intro t ht
  have hTs : Ts ≤ t + 1 := by omega
  have hTc : Tc ≤ t + 1 := by omega
  have hfocus := run_focus_isFocus O hP (t + 1)
  have hsub : O.language (run O stream (t + 1)).focus ⊆ O.language z :=
    focus_subset_target hfocus (hscope (t + 1) hTs) (hcrit (t + 1) hTc)
  exact hsub (output_mem_round_focus O stream t)

end PatientMachine
end GenLimit
