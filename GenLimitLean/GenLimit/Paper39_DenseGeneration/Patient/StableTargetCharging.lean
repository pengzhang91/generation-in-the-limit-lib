import GenLimit.Paper39_DenseGeneration.Patient.Departure
import GenLimit.Paper39_DenseGeneration.Patient.Fact312
import GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging

/-!
# Charging from a stable target witness

The patient-scope charging argument does not require an exact presentation of
a family member.  Its common core only needs an eventually permanent critical
witness contained in the true target, eventual inclusion of that witness in
scope, and the ordinary on-model invariant.  Exact and partial presentations
instantiate this package in their respective certificate modules.
-/

namespace GenLimit
namespace PatientMachine

/-- The hypotheses shared by the exact- and partial-presentation charging
arguments. -/
structure StableTargetRun
    (O : OracleFamily) (stream : ℕ → ℕ) (K : Language) where
  witness : ℕ
  threshold : ℕ
  onModel : OnModel O stream
  critical : ∀ t, threshold ≤ t →
    RecursiveCritical O.language stream t witness
  inScope : ∀ t, threshold ≤ t → witness < (run O stream t).scope
  witness_subset_target : O.language witness ⊆ K
  adversary_target : ∀ t, stream t ∈ K

namespace StableTargetRun

variable {O : OracleFamily} {stream : ℕ → ℕ} {K : Language}
    (S : StableTargetRun O stream K)

theorem output_target {t : ℕ} (ht : S.threshold ≤ t) :
    output O stream t ∈ K := by
  have ht' : S.threshold ≤ t + 1 := le_trans ht (Nat.le_succ t)
  have hfocus := run_focus_isFocus_of_onModel O S.onModel (t + 1)
  have hsub : O.language (run O stream (t + 1)).focus ⊆
      O.language S.witness :=
    focus_subset_target hfocus (S.inScope (t + 1) ht')
      (S.critical (t + 1) ht')
  exact S.witness_subset_target
    (hsub (output_available_post_focus O stream t).1)

def IsSwitchTime (x t : ℕ) : Prop :=
  S.threshold < t ∧ stream t = x ∧ x ∉ sample stream t ∧
    SwitchRound O stream t

noncomputable def switchTime (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, S.IsSwitchTime x t then Nat.find h else 0

theorem switchTime_spec {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    S.IsSwitchTime x (S.switchTime x) := by
  classical
  rcases hx with ⟨-, t, ht, htx, hfresh, hswitch⟩
  have hexists : ∃ q, S.IsSwitchTime x q :=
    ⟨t, ht, htx, hfresh, hswitch⟩
  simp [switchTime, hexists]
  exact Nat.find_spec hexists

noncomputable def landingFocus (x : ℕ) : ℕ :=
  (run O stream (S.switchTime x + 1)).focus

theorem certifiedLanding {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    CertifiedLanding O stream (S.switchTime x) (S.landingFocus x) := by
  classical
  let t := S.switchTime x
  let old := run O stream t
  let i := S.landingFocus x
  have htime := S.switchTime_spec hx
  have htT : S.threshold ≤ t := Nat.le_of_lt htime.1
  have hfocus : IsFocus O.language stream t old.scope old.focus :=
    run_focus_isFocus_of_onModel O S.onModel t
  have hfalsified : ¬ Consistent O.language stream (t + 1) old.focus := by
    intro hcon
    exact htime.2.2.2
      (hcon (value_mem_sample (stream := stream) (Nat.lt_succ_self t)))
  have hwOld := S.critical t htT
  have hwNew := S.critical (t + 1) (by omega)
  have hwScope := S.inScope t htT
  have hcon :
      (consistentIndices O.language stream (t + 1) old.scope).Nonempty :=
    ⟨S.witness, mem_consistentIndices.mpr
      ⟨hwScope, recursiveCritical_consistent hwNew⟩⟩
  have hsurv :
      (survivingCriticalIndices O.language stream t old.scope).Nonempty :=
    ⟨S.witness, mem_survivingCriticalIndices.mpr
      ⟨hwScope, hwOld, hwNew⟩⟩
  let b := highestSurvivor O.language stream t old.scope old.focus
  have hb := highestSurvivor_spec (fallback := old.focus) hsurv
  have hnewEq : (run O stream (t + 1)).focus = b := by
    calc
      (run O stream (t + 1)).focus =
          (PatientMachine.decide O.language stream t old).focus := by simp [old]
      _ = (backtrackDecision O.language stream t old).focus := by
        simp [PatientMachine.decide, hfalsified]
      _ = b := by
        have hback := backtrackDecision_of_survivor hcon hsurv
        simpa [b] using congrArg Decision.focus hback
  have hiEq : i = b := by simpa [i, landingFocus] using hnewEq
  have hbelow : b < old.focus := by
    have hlt := backtrackDecision_focus_lt_of_survivor
      hfocus hfalsified hcon hsurv
    simpa [run_succ, processRound, PatientMachine.decide, hfalsified,
      backtrackDecision_of_survivor hcon hsurv, b] using hlt
  refine ⟨?_, ?_, ?_⟩
  · change RecursiveCritical O.language stream t i
    rw [hiEq]
    exact hb.2.1
  · change (run O stream (t + 1)).focus = i
    exact hnewEq.trans hiEq.symm
  · change i < old.focus
    rw [hiEq]
    exact hbelow

theorem landing_subset_target {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    O.language (S.landingFocus x) ⊆ K := by
  let t := S.switchTime x
  let i := S.landingFocus x
  have hland := S.certifiedLanding hx
  have htime := S.switchTime_spec hx
  have htT : S.threshold ≤ t := Nat.le_of_lt htime.1
  have ht1T : S.threshold ≤ t + 1 := le_trans htT (Nat.le_succ t)
  have hw := S.critical t htT
  have hi := hland.oldCritical
  have hwNew := S.critical (t + 1) ht1T
  have hwScopeNew := S.inScope (t + 1) ht1T
  have hfocusNew := run_focus_isFocus_of_onModel O S.onModel (t + 1)
  have hwi : S.witness ≤ i := by
    have := hfocusNew.2.2 S.witness hwScopeNew hwNew
    simpa [i, landingFocus] using this
  exact Set.Subset.trans
    (recursiveCritical_subset_of_le hwi hw hi)
    S.witness_subset_target

noncomputable def departure (x : ℕ) : ℕ :=
  latestDeparture O stream (S.switchTime x) (S.landingFocus x)

noncomputable def tau (x : ℕ) : ℕ :=
  (run O stream (S.departure x)).tau

noncomputable def charge (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ S.tau x)).image fun k =>
    output O stream (S.departure x - 1 - k)

theorem departure_spec {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    S.departure x < S.switchTime x ∧
      UpwardDeparture O stream (S.landingFocus x) (S.departure x) := by
  simpa [departure] using
    (S.certifiedLanding hx).latestDeparture_spec_of_onModel S.onModel

theorem tau_pos {x : ℕ}
    (_hx : x ∈ lateSwitchLoss O stream S.threshold) : 0 < S.tau x :=
  run_tau_pos O stream (S.departure x)

theorem tau_injective : Set.InjOn S.tau
    (lateSwitchLoss O stream S.threshold) := by
  intro x hx y hy hxy
  have hxLand := S.certifiedLanding hx
  have hyLand := S.certifiedLanding hy
  have hpair := certifiedLanding_label_injective_of_onModel S.onModel
    hxLand hyLand (by simpa [tau, departure, landingLabel] using hxy)
  have hxTime := S.switchTime_spec hx
  have hyTime := S.switchTime_spec hy
  calc
    x = stream (S.switchTime x) := hxTime.2.1.symm
    _ = stream (S.switchTime y) := by rw [hpair.1]
    _ = y := hyTime.2.1

theorem charge_card {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    (S.charge x).card = 2 ^ S.tau x := by
  classical
  let d := S.departure x
  let p := 2 ^ S.tau x
  let rounds := Finset.range p
  let f : ℕ → ℕ := fun k => output O stream (d - 1 - k)
  have hdep := (S.departure_spec hx).2
  have hpTime : p ≤ d := by
    simpa [p, tau, d] using
      upwardDeparture_pow_le_time_of_onModel S.onModel hdep
  have hfInj : Set.InjOn f rounds := by
    intro k hk l hl hkl
    have hklt : k < p := by simpa [rounds] using hk
    have hllt : l < p := by simpa [rounds] using hl
    have hroundEq : d - 1 - k = d - 1 - l :=
      output_injective O stream hkl
    omega
  change (rounds.image f).card = p
  rw [Finset.card_image_of_injOn hfInj]
  exact Finset.card_range p

theorem charge_mem_target {x y : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold)
    (hy : y ∈ S.charge x) : y ∈ K := by
  classical
  let d := S.departure x
  let p := 2 ^ S.tau x
  have hdep := (S.departure_spec hx).2
  have hsub := S.landing_subset_target hx
  rw [charge] at hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  have hk' : k < 2 ^ (run O stream d).tau := by
    simpa [p, tau, d] using (Finset.mem_range.mp hk)
  exact hsub
    (upwardDeparture_block_output_mem_of_onModel S.onModel hdep hk')

theorem charge_lt_loss {x y : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold)
    (hy : y ∈ S.charge x) : y < x := by
  classical
  let t := S.switchTime x
  let i := S.landingFocus x
  let d := S.departure x
  let p := 2 ^ S.tau x
  have htime := S.switchTime_spec hx
  have hdepSpec := S.departure_spec hx
  have hdep : UpwardDeparture O stream i d := hdepSpec.2
  have hdt : d < t := hdepSpec.1
  have hpTime : p ≤ d := by
    simpa [p, tau, d] using
      upwardDeparture_pow_le_time_of_onModel S.onModel hdep
  have hxAttacker : x ∈ AdversaryFirst stream (output O stream) := hx.1
  have hxFresh : x ∉ sample stream t := htime.2.2.1
  have hxStream : stream t = x := htime.2.1
  have hstreamAttacker : stream t ∈
      AdversaryFirst stream (output O stream) := by
    simpa [hxStream] using hxAttacker
  have hstreamFresh : stream t ∉ sample stream t := by
    simpa [hxStream] using hxFresh
  have hpostFocus := run_focus_isFocus_of_onModel O S.onModel (t + 1)
  have hxSample : x ∈ sample stream (t + 1) := by
    rw [mem_sample_iff]
    exact ⟨t, Nat.lt_succ_self t, hxStream⟩
  have hxLanding : x ∈ O.language i := by
    change x ∈ O.language (run O stream (t + 1)).focus
    exact (recursiveCritical_consistent hpostFocus.2.1) hxSample
  rw [charge] at hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  have hkP : k < p := by simpa [p] using (Finset.mem_range.mp hk)
  let r := d - 1 - k
  have hrD : r < d := by
    have hpPos : 0 < p := by dsimp [p]; exact Nat.two_pow_pos _
    dsimp [r]
    omega
  have hrT : r < t := lt_trans hrD hdt
  have hr1T : r + 1 ≤ t := Nat.succ_le_of_lt hrT
  have hkTau : k < 2 ^ (run O stream d).tau := by
    simpa [p, tau, d] using hkP
  have hpostEq : (run O stream (r + 1)).focus = i := by
    have hblock := upwardDeparture_age_block_of_onModel
      S.onModel hdep hkTau
    have hindex : r + 1 = d - k := by dsimp [r]; omega
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

noncomputable def chargingCertificate :
    PatientScope.TargetSwitchChargingCertificate K
      (lateSwitchLoss O stream S.threshold) where
  tau := S.tau
  charge := S.charge
  switchLoss_subset := by
    intro x hx
    rcases hx.2 with ⟨t, -, htx, -, -⟩
    simpa [← htx] using S.adversary_target t
  tau_pos := fun _ hx => S.tau_pos hx
  tau_injective := S.tau_injective
  charge_size := by
    intro x hx
    rw [S.charge_card hx]
  charge_target := fun _ hx _ hy => S.charge_mem_target hx hy
  charge_before_loss := by
    intro x hx y hy
    exact Finset.mem_range.mpr (S.charge_lt_loss hx hy)

end StableTargetRun
end PatientMachine
end GenLimit
