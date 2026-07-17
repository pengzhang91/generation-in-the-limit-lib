import GenLimit.DenseGeneration.Patient.Certificate
import GenLimit.DenseGeneration.Patient.Departure
import GenLimit.DenseGeneration.Patient.Switch
import GenLimit.DenseGeneration.Abstract.TargetSwitchCharging

/-!
# Charging settled switch losses

This module constructs the target-relative charging certificate for the late
switch losses of the semantic patient-scope machine.  A loss is charged to the
exponential block immediately preceding the canonical latest departure from
its backtracking landing focus.
-/

namespace GenLimit
namespace PatientMachine

/-- The round data carried by a settled switch loss. -/
def IsSettledSwitchTime
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) (x t : ℕ) : Prop :=
  settledThreshold O stream z hP < t ∧
    stream t = x ∧ x ∉ sample stream t ∧ SwitchRound O stream t

/-- Canonical fresh adversary round of a settled switch value. -/
noncomputable def settledSwitchTime
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, IsSettledSwitchTime O stream z hP x t then
    Nat.find h else 0

theorem settledSwitchTime_spec
    {O : OracleFamily} {stream : ℕ → ℕ} {z x : ℕ}
    (hP : Presents stream (O.language z))
    (hx : x ∈ settledSwitchLoss O stream z hP) :
    IsSettledSwitchTime O stream z hP x
      (settledSwitchTime O stream z hP x) := by
  classical
  rcases hx with ⟨-, t, ht, htx, hfresh, hswitch⟩
  have hexists : ∃ q, IsSettledSwitchTime O stream z hP x q :=
    ⟨t, ht, htx, hfresh, hswitch⟩
  simp [settledSwitchTime, hexists]
  exact Nat.find_spec hexists

/-- The state reached by backtracking at a settled switch. -/
noncomputable def settledLandingFocus
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) (x : ℕ) : ℕ :=
  (run O stream (settledSwitchTime O stream z hP x + 1)).focus

/-- A settled switch lands at a previously critical language strictly below
the falsified focus. -/
theorem settledSwitch_certifiedLanding
    {O : OracleFamily} {stream : ℕ → ℕ} {z x : ℕ}
    (hP : Presents stream (O.language z))
    (hx : x ∈ settledSwitchLoss O stream z hP) :
    CertifiedLanding O stream (settledSwitchTime O stream z hP x)
      (settledLandingFocus O stream z hP x) := by
  classical
  let T := settledThreshold O stream z hP
  let t := settledSwitchTime O stream z hP x
  let old := run O stream t
  let i := settledLandingFocus O stream z hP x
  have htime := settledSwitchTime_spec hP hx
  have htT : T ≤ t := Nat.le_of_lt htime.1
  have hfocus : IsFocus O.language stream t old.scope old.focus :=
    run_focus_isFocus O hP t
  have hfalsified : ¬ Consistent O.language stream (t + 1) old.focus := by
    intro hcon
    exact htime.2.2.2
      (hcon (value_mem_sample (stream := stream) (Nat.lt_succ_self t)))
  have hzOld : RecursiveCritical O.language stream t z :=
    settled_target_critical O stream z hP htT
  have hzNew : RecursiveCritical O.language stream (t + 1) z :=
    settled_target_critical O stream z hP (by omega)
  have hzScope : z < old.scope :=
    settled_target_in_scope O stream z hP htT
  have hcon :
      (consistentIndices O.language stream (t + 1) old.scope).Nonempty := by
    exact ⟨z, mem_consistentIndices.mpr
      ⟨hzScope, recursiveCritical_consistent hzNew⟩⟩
  have hsurv :
      (survivingCriticalIndices O.language stream t old.scope).Nonempty := by
    exact ⟨z, mem_survivingCriticalIndices.mpr
      ⟨hzScope, hzOld, hzNew⟩⟩
  let b := highestSurvivor O.language stream t old.scope old.focus
  have hb := highestSurvivor_spec (fallback := old.focus) hsurv
  have hnewEq : (run O stream (t + 1)).focus = b := by
    calc
      (run O stream (t + 1)).focus =
          (decide O.language stream t old).focus := by
            simp [old]
      _ = (backtrackDecision O.language stream t old).focus := by
        simp [decide, hfalsified]
      _ = b := by
        have hback := backtrackDecision_of_survivor hcon hsurv
        simpa [b] using congrArg Decision.focus hback
  have hiEq : i = b := by simpa [i, settledLandingFocus] using hnewEq
  have hbelow : b < old.focus := by
    have hlt := backtrackDecision_focus_lt_of_survivor
      hfocus hfalsified hcon hsurv
    simpa [run_succ, processRound, decide, hfalsified,
      backtrackDecision_of_survivor hcon hsurv, b] using hlt
  refine ⟨?_, ?_, ?_⟩
  · change RecursiveCritical O.language stream t i
    rw [hiEq]
    exact hb.2.1
  · rfl
  · change i < old.focus
    rw [hiEq]
    exact hbelow

/-- The landing language of a settled switch is contained in the target. -/
theorem settledLandingFocus_subset_target
    {O : OracleFamily} {stream : ℕ → ℕ} {z x : ℕ}
    (hP : Presents stream (O.language z))
    (hx : x ∈ settledSwitchLoss O stream z hP) :
    O.language (settledLandingFocus O stream z hP x) ⊆ O.language z := by
  let t := settledSwitchTime O stream z hP x
  let i := settledLandingFocus O stream z hP x
  have hland := settledSwitch_certifiedLanding hP hx
  have htime := settledSwitchTime_spec hP hx
  have htT : settledThreshold O stream z hP ≤ t :=
    Nat.le_of_lt htime.1
  have ht1T : settledThreshold O stream z hP ≤ t + 1 :=
    le_trans htT (Nat.le_succ t)
  have hz : RecursiveCritical O.language stream t z :=
    settled_target_critical O stream z hP htT
  have hi : RecursiveCritical O.language stream t i := hland.oldCritical
  have hzNew : RecursiveCritical O.language stream (t + 1) z :=
    settled_target_critical O stream z hP ht1T
  have hzScopeNew : z < (run O stream (t + 1)).scope :=
    settled_target_in_scope O stream z hP ht1T
  have hfocusNew := run_focus_isFocus O hP (t + 1)
  have hzi : z ≤ i := by
    have := hfocusNew.2.2 z hzScopeNew hzNew
    simpa [i, settledLandingFocus] using this
  exact recursiveCritical_subset_of_le hzi hz hi

/-- Canonical patient departure charged to a settled switch value. -/
noncomputable def settledDeparture
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) (x : ℕ) : ℕ :=
  latestDeparture O stream (settledSwitchTime O stream z hP x)
    (settledLandingFocus O stream z hP x)

/-- Positive focus-change label used by the charging lemma. -/
noncomputable def settledTau
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) (x : ℕ) : ℕ :=
  (run O stream (settledDeparture O stream z hP x)).tau

/-- Charged generator values, listed in reverse chronological order from the
patient block immediately preceding the canonical departure. -/
noncomputable def settledCharge
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) (x : ℕ) : Finset ℕ := by
  classical
  let d := settledDeparture O stream z hP x
  let p := 2 ^ settledTau O stream z hP x
  exact (Finset.range p).image fun k => output O stream (d - 1 - k)

theorem settledDeparture_spec
    {O : OracleFamily} {stream : ℕ → ℕ} {z x : ℕ}
    (hP : Presents stream (O.language z))
    (hx : x ∈ settledSwitchLoss O stream z hP) :
    settledDeparture O stream z hP x <
        settledSwitchTime O stream z hP x ∧
      UpwardDeparture O stream (settledLandingFocus O stream z hP x)
        (settledDeparture O stream z hP x) := by
  have hland := settledSwitch_certifiedLanding hP hx
  simpa [settledDeparture] using hland.latestDeparture_spec hP

theorem settledTau_pos
    {O : OracleFamily} {stream : ℕ → ℕ} {z x : ℕ}
    (hP : Presents stream (O.language z))
    (_hx : x ∈ settledSwitchLoss O stream z hP) :
    0 < settledTau O stream z hP x := by
  exact run_tau_pos O stream (settledDeparture O stream z hP x)

/-- Canonical charge labels are injective on settled switch-loss values. -/
theorem settledTau_injective
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    Set.InjOn (settledTau O stream z hP)
      (settledSwitchLoss O stream z hP) := by
  intro x hx y hy hxy
  have hxLand := settledSwitch_certifiedLanding hP hx
  have hyLand := settledSwitch_certifiedLanding hP hy
  have hpair := certifiedLanding_label_injective hP hxLand hyLand (by
    simpa [settledTau, settledDeparture, landingLabel] using hxy)
  have hxTime := settledSwitchTime_spec hP hx
  have hyTime := settledSwitchTime_spec hP hy
  calc
    x = stream (settledSwitchTime O stream z hP x) := hxTime.2.1.symm
    _ = stream (settledSwitchTime O stream z hP y) := by rw [hpair.1]
    _ = y := hyTime.2.1

/-- The charge contains exactly `2 ^ tau` distinct generator values. -/
theorem settledCharge_card
    {O : OracleFamily} {stream : ℕ → ℕ} {z x : ℕ}
    (hP : Presents stream (O.language z))
    (hx : x ∈ settledSwitchLoss O stream z hP) :
    (settledCharge O stream z hP x).card =
      2 ^ settledTau O stream z hP x := by
  classical
  let d := settledDeparture O stream z hP x
  let p := 2 ^ settledTau O stream z hP x
  let rounds := Finset.range p
  let f : ℕ → ℕ := fun k => output O stream (d - 1 - k)
  have hdep := (settledDeparture_spec hP hx).2
  have hpTime : p ≤ d := by
    simpa [p, settledTau, d] using upwardDeparture_pow_le_time hP hdep
  have hfInj : Set.InjOn f rounds := by
    intro k hk l hl hkl
    have hklt : k < p := by simpa [rounds] using hk
    have hllt : l < p := by simpa [rounds] using hl
    have hroundEq : d - 1 - k = d - 1 - l :=
      output_injective O stream hkl
    omega
  change (rounds.image f).card = p
  calc
    (rounds.image f).card = rounds.card :=
      Finset.card_image_of_injOn hfInj
    _ = p := Finset.card_range p

/-- Every charged value belongs to the target language. -/
theorem settledCharge_mem_target
    {O : OracleFamily} {stream : ℕ → ℕ} {z x y : ℕ}
    (hP : Presents stream (O.language z))
    (hx : x ∈ settledSwitchLoss O stream z hP)
    (hy : y ∈ settledCharge O stream z hP x) :
    y ∈ O.language z := by
  classical
  let d := settledDeparture O stream z hP x
  let p := 2 ^ settledTau O stream z hP x
  have hdep := (settledDeparture_spec hP hx).2
  have hsub := settledLandingFocus_subset_target hP hx
  rw [settledCharge] at hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  have hk' : k < 2 ^ (run O stream d).tau := by
    simpa [p, settledTau, d] using (Finset.mem_range.mp hk)
  exact upwardDeparture_block_output_mem_target hP hdep hsub hk'

/-- Every charged value is strictly smaller than its switch loss. -/
theorem settledCharge_lt_loss
    {O : OracleFamily} {stream : ℕ → ℕ} {z x y : ℕ}
    (hP : Presents stream (O.language z))
    (hx : x ∈ settledSwitchLoss O stream z hP)
    (hy : y ∈ settledCharge O stream z hP x) :
    y < x := by
  classical
  let t := settledSwitchTime O stream z hP x
  let i := settledLandingFocus O stream z hP x
  let d := settledDeparture O stream z hP x
  let p := 2 ^ settledTau O stream z hP x
  have htime := settledSwitchTime_spec hP hx
  have hdepSpec := settledDeparture_spec hP hx
  have hdep : UpwardDeparture O stream i d := hdepSpec.2
  have hdt : d < t := hdepSpec.1
  have hpTime : p ≤ d := by
    simpa [p, settledTau, d] using upwardDeparture_pow_le_time hP hdep
  have hxAttacker : x ∈ AdversaryFirst stream (output O stream) := hx.1
  have hxFresh : x ∉ sample stream t := htime.2.2.1
  have hxStream : stream t = x := htime.2.1
  have hstreamAttacker : stream t ∈
      AdversaryFirst stream (output O stream) := by
    simpa [hxStream] using hxAttacker
  have hstreamFresh : stream t ∉ sample stream t := by
    simpa [hxStream] using hxFresh
  have hpostFocus := run_focus_isFocus O hP (t + 1)
  have hxSample : x ∈ sample stream (t + 1) := by
    rw [mem_sample_iff]
    exact ⟨t, Nat.lt_succ_self t, hxStream⟩
  have hxLanding : x ∈ O.language i := by
    change x ∈ O.language (run O stream (t + 1)).focus
    exact (recursiveCritical_consistent hpostFocus.2.1) hxSample
  rw [settledCharge] at hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  have hkP : k < p := by simpa [p] using (Finset.mem_range.mp hk)
  let r := d - 1 - k
  have hrD : r < d := by
    have hpPos : 0 < p := by
      dsimp [p]
      exact Nat.two_pow_pos _
    dsimp [r]
    omega
  have hrT : r < t := lt_trans hrD hdt
  have hr1T : r + 1 ≤ t := Nat.succ_le_of_lt hrT
  have hkTau : k < 2 ^ (run O stream d).tau := by
    simpa [p, settledTau, d] using hkP
  have hpostEq : (run O stream (r + 1)).focus = i := by
    have hblock := upwardDeparture_age_block hP hdep hkTau
    have hindex : r + 1 = d - k := by
      dsimp [r]
      omega
    rwa [hindex]
  have hxNotSample : x ∉ sample stream (r + 1) := by
    intro hm
    exact hxFresh (sample_mono hr1T hm)
  have hxNotUsed : x ∉ (run O stream r).used := by
    intro hm
    rw [mem_run_used_iff] at hm
    obtain ⟨s, hsr, hsx⟩ := hm
    have hst : s < t := lt_trans hsr hrT
    have hne := no_output_before_fresh_attacker
      O stream hstreamAttacker hstreamFresh s hst
    exact hne (by simpa [hxStream] using hsx)
  have hxAvailable : Available O.language stream (r + 1)
      (run O stream r).used (run O stream (r + 1)).focus x := by
    refine ⟨?_, hxNotSample, hxNotUsed⟩
    rw [hpostEq]
    exact hxLanding
  have hle : output O stream r ≤ x :=
    output_minimal_post_focus O stream r x hxAvailable
  have hne : output O stream r ≠ x := by
    have hne' := no_output_before_fresh_attacker
      O stream hstreamAttacker hstreamFresh r hrT
    simpa [hxStream] using hne'
  exact lt_of_le_of_ne hle hne

/-- Concrete target-relative form of Lemma 3.13. -/
noncomputable def settledChargingCertificate
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP) where
  tau := settledTau O stream z hP
  charge := settledCharge O stream z hP
  switchLoss_subset := by
    intro x hx
    exact (settledSwitchLoss_subset O stream z hP hx).2
  tau_pos := fun _ hx => settledTau_pos hP hx
  tau_injective := settledTau_injective O stream z hP
  charge_size := by
    intro x hx
    rw [settledCharge_card hP hx]
  charge_target := by
    intro x hx y hy
    exact settledCharge_mem_target hP hx hy
  charge_before_loss := by
    intro x hx y hy
    exact Finset.mem_range.mpr (settledCharge_lt_loss hP hx hy)

end PatientMachine
end GenLimit
