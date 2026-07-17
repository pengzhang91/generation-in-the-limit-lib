import GenLimit.DenseGeneration.Patient.Fact312
import GenLimit.DenseGeneration.Patient.MachineInvariant
import GenLimit.DenseGeneration.Patient.Output

/-!
# Concrete late switch landings

This module identifies the exact backtracking endpoint associated with a late
switch-loss value.  It stops before choosing an earlier departure or defining
any charge set.
-/

namespace GenLimit
namespace PatientMachine

/-- Eventual target criticality and target-in-scope already imply eventual
output validity. -/
theorem output_mem_target_of_critical_in_scope
    (O : OracleFamily) (stream : ℕ → ℕ) {z T : ℕ}
    (hP : Presents stream (O.language z))
    (hcritical : ∀ t, T ≤ t → RecursiveCritical O.language stream t z)
    (hinScope : ∀ t, T ≤ t → z < (run O stream t).scope) :
    ∀ t, T ≤ t → output O stream t ∈ O.language z := by
  intro t ht
  have ht' : T ≤ t + 1 := le_trans ht (Nat.le_succ t)
  have hfocus := run_focus_isFocus O hP (t + 1)
  have hsub := focus_subset_target hfocus
    (hinScope (t + 1) ht') (hcritical (t + 1) ht')
  exact hsub (output_available_post_focus O stream t).1

/-- The concrete trace induced by the stabilized target hypotheses. -/
noncomputable def stabilizedGameTrace
    (O : OracleFamily) (stream : ℕ → ℕ) (z T : ℕ)
    (hP : Presents stream (O.language z))
    (hcritical : ∀ t, T ≤ t → RecursiveCritical O.language stream t z)
    (hinScope : ∀ t, T ≤ t → z < (run O stream t).scope) :
    PatientScope.GameTrace :=
  gameTrace O stream z T hP
    (output_mem_target_of_critical_in_scope O stream hP hcritical hinScope)

/-- All local information supplied by a late switch loss at its first
adversary occurrence. -/
structure LateSwitchLanding
    (O : OracleFamily) (stream : ℕ → ℕ) (z T x : ℕ)
    (G : PatientScope.GameTrace) : Prop where
  /-- Every field is stated at the unique first adversary round announcing
  `x`. -/
  late : T < G.firstAdversaryTime x
  adversary_eq : stream (G.firstAdversaryTime x) = x
  fresh : x ∉ sample stream (G.firstAdversaryTime x)
  switchRound : SwitchRound O stream (G.firstAdversaryTime x)

  /-- The switch forces the survivor backtracking branch. -/
  oldFocus_falsified :
    ¬ Consistent O.language stream (G.firstAdversaryTime x + 1)
      (run O stream (G.firstAdversaryTime x)).focus
  consistent_nonempty :
    (consistentIndices O.language stream (G.firstAdversaryTime x + 1)
      (run O stream (G.firstAdversaryTime x)).scope).Nonempty
  survivor_nonempty :
    (survivingCriticalIndices O.language stream (G.firstAdversaryTime x)
      (run O stream (G.firstAdversaryTime x)).scope).Nonempty
  post_move_backtrack :
    (run O stream (G.firstAdversaryTime x + 1)).move = .backtrack
  landing_eq_highestSurvivor :
    (run O stream (G.firstAdversaryTime x + 1)).focus =
      highestSurvivor O.language stream (G.firstAdversaryTime x)
        (run O stream (G.firstAdversaryTime x)).scope
        (run O stream (G.firstAdversaryTime x)).focus

  /-- Set-theoretic properties of the landing focus. -/
  landing_oldCritical :
    RecursiveCritical O.language stream (G.firstAdversaryTime x)
      (run O stream (G.firstAdversaryTime x + 1)).focus
  landing_newCritical :
    RecursiveCritical O.language stream (G.firstAdversaryTime x + 1)
      (run O stream (G.firstAdversaryTime x + 1)).focus
  landing_below_oldFocus :
    (run O stream (G.firstAdversaryTime x + 1)).focus <
      (run O stream (G.firstAdversaryTime x)).focus
  target_le_landing :
    z ≤ (run O stream (G.firstAdversaryTime x + 1)).focus
  value_mem_landing :
    x ∈ O.language (run O stream (G.firstAdversaryTime x + 1)).focus
  landing_subset_target :
    O.language (run O stream (G.firstAdversaryTime x + 1)).focus ⊆
      O.language z

/-- A witness in `lateSwitchLoss` occurs at the concrete trace's first
adversary time. -/
theorem lateSwitchLoss_witness_eq_firstAdversaryTime
    (O : OracleFamily) (stream : ℕ → ℕ) {z T : ℕ}
    (hP : Presents stream (O.language z))
    (hcritical : ∀ t, T ≤ t → RecursiveCritical O.language stream t z)
    (hinScope : ∀ t, T ≤ t → z < (run O stream t).scope)
    {x w : ℕ}
    (hx : x ∈ lateSwitchLoss O stream T)
    (hw : stream w = x) (hfresh : x ∉ sample stream w) :
    (stabilizedGameTrace O stream z T hP hcritical hinScope).firstAdversaryTime x =
      w := by
  let G := stabilizedGameTrace O stream z T hP hcritical hinScope
  have hxA : x ∈ G.attacker := by
    simpa [G, stabilizedGameTrace, gameTrace,
      PatientScope.GameTrace.attacker] using hx.1
  have hspec : stream (G.firstAdversaryTime x) = x := by
    simpa [G, stabilizedGameTrace, gameTrace] using
      G.firstAdversaryTime_spec hxA
  have hle : G.firstAdversaryTime x ≤ w := by
    apply G.firstAdversaryTime_min hxA
    simpa [G, stabilizedGameTrace, gameTrace] using hw
  have hnotlt : ¬ G.firstAdversaryTime x < w := by
    intro hlt
    apply hfresh
    have hm := value_mem_sample
      (stream := stream) (s := G.firstAdversaryTime x) (t := w) hlt
    simpa [hspec] using hm
  exact Nat.le_antisymm hle (Nat.le_of_not_gt hnotlt)

/-- Every late switch loss has the requested survivor-landing certificate at
its first adversary occurrence. -/
theorem lateSwitchLoss_landing
    (O : OracleFamily) (stream : ℕ → ℕ) {z T : ℕ}
    (hP : Presents stream (O.language z))
    (hcritical : ∀ t, T ≤ t → RecursiveCritical O.language stream t z)
    (hinScope : ∀ t, T ≤ t → z < (run O stream t).scope)
    {x : ℕ} (hx : x ∈ lateSwitchLoss O stream T) :
    LateSwitchLanding O stream z T x
      (stabilizedGameTrace O stream z T hP hcritical hinScope) := by
  classical
  let G := stabilizedGameTrace O stream z T hP hcritical hinScope
  rcases hx.2 with ⟨w, hTw, hwx, hfreshW, hswitchW⟩
  let t := G.firstAdversaryTime x
  have htw : t = w := by
    exact lateSwitchLoss_witness_eq_firstAdversaryTime
      O stream hP hcritical hinScope hx hwx hfreshW
  have htx : stream t = x := by simpa [htw] using hwx
  have hTt : T < t := by simpa [htw] using hTw
  have hfresh : x ∉ sample stream t := by simpa [htw] using hfreshW
  have hswitch : SwitchRound O stream t := by simpa [htw] using hswitchW
  have hfalsified :
      ¬ Consistent O.language stream (t + 1) (run O stream t).focus := by
    intro hcon
    exact hswitch (hcon (value_mem_sample (Nat.lt_succ_self t)))
  have hzOld : RecursiveCritical O.language stream t z :=
    hcritical t (Nat.le_of_lt hTt)
  have hzNew : RecursiveCritical O.language stream (t + 1) z :=
    hcritical (t + 1) (by omega)
  have hzScope : z < (run O stream t).scope :=
    hinScope t (Nat.le_of_lt hTt)
  have hconsistent :
      (consistentIndices O.language stream (t + 1)
        (run O stream t).scope).Nonempty :=
    ⟨z, mem_consistentIndices.mpr
      ⟨hzScope, recursiveCritical_consistent hzNew⟩⟩
  have hsurvivor :
      (survivingCriticalIndices O.language stream t
        (run O stream t).scope).Nonempty :=
    ⟨z, mem_survivingCriticalIndices.mpr ⟨hzScope, hzOld, hzNew⟩⟩
  let i := highestSurvivor O.language stream t
    (run O stream t).scope (run O stream t).focus
  have hi := highestSurvivor_spec
    (C := O.language) (stream := stream) (t := t)
    (scope := (run O stream t).scope)
    (fallback := (run O stream t).focus) hsurvivor
  have hzi : z ≤ i := hi.2.2.2 z hzScope hzOld hzNew
  have hlanding : (run O stream (t + 1)).focus = i := by
    simp [run_succ, processRound, decide, hfalsified,
      backtrackDecision_of_survivor hconsistent hsurvivor, i]
  have hbelow : i < (run O stream t).focus := by
    have hfocus := run_focus_isFocus O hP t
    have hb := backtrackDecision_focus_lt_of_survivor
      hfocus hfalsified hconsistent hsurvivor
    simpa [run_succ, processRound, decide, hfalsified,
      backtrackDecision_of_survivor hconsistent hsurvivor, i] using hb
  have hxSample : x ∈ sample stream (t + 1) := by
    have hm := value_mem_sample
      (stream := stream) (s := t) (t := t + 1) (Nat.lt_succ_self t)
    simpa [htx] using hm
  have hxLanding : x ∈ O.language i :=
    recursiveCritical_consistent hi.2.2.1 hxSample
  have hsub : O.language i ⊆ O.language z :=
    recursiveCritical_subset_of_le hzi hzNew hi.2.2.1
  refine
    { late := hTt
      adversary_eq := htx
      fresh := hfresh
      switchRound := hswitch
      oldFocus_falsified := hfalsified
      consistent_nonempty := hconsistent
      survivor_nonempty := hsurvivor
      post_move_backtrack := ?_
      landing_eq_highestSurvivor := hlanding
      landing_oldCritical := ?_
      landing_newCritical := ?_
      landing_below_oldFocus := ?_
      target_le_landing := ?_
      value_mem_landing := ?_
      landing_subset_target := ?_ }
  · change (run O stream (t + 1)).move = .backtrack
    simp [run_succ, processRound, decide, hfalsified,
      backtrackDecision_move]
  · change RecursiveCritical O.language stream t
      (run O stream (t + 1)).focus
    rw [hlanding]
    exact hi.2.1
  · change RecursiveCritical O.language stream (t + 1)
      (run O stream (t + 1)).focus
    rw [hlanding]
    exact hi.2.2.1
  · change (run O stream (t + 1)).focus < (run O stream t).focus
    rw [hlanding]
    exact hbelow
  · change z ≤ (run O stream (t + 1)).focus
    rw [hlanding]
    exact hzi
  · change x ∈ O.language (run O stream (t + 1)).focus
    rw [hlanding]
    exact hxLanding
  · change O.language (run O stream (t + 1)).focus ⊆ O.language z
    rw [hlanding]
    exact hsub

end PatientMachine
end GenLimit
