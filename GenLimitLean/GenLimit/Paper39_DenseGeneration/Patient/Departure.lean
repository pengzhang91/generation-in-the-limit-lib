import GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant
import GenLimit.Paper39_DenseGeneration.Dynamics
import GenLimit.Paper39_DenseGeneration.Patient.History

/-!
# Patient departures

This file formalizes the historical invariant used in the charging proof for
the patient-scope algorithm.  Whenever a language is critical and lies below
the current focus, the machine previously left that language by an upward
scope-expansion step.  Such a departure carries both its positive `tau` label
and the preceding block of `2 ^ tau` rounds spent at the departing focus.
-/

namespace GenLimit
namespace PatientMachine

/-- Round `d` is an upward departure from language `i`: the pre-round focus is
`i`, the scope-expansion branch is taken, and the post-round focus is higher. -/
def UpwardDeparture
    (O : OracleFamily) (stream : ℕ → ℕ) (i d : ℕ) : Prop :=
  (run O stream d).focus = i ∧
    (run O stream (d + 1)).move = .expand ∧
    i < (run O stream (d + 1)).focus

/-- Departure rounds from `i` strictly before time `t`. -/
noncomputable def departureTimes
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter (UpwardDeparture O stream i)

@[simp] theorem mem_departureTimes
    {O : OracleFamily} {stream : ℕ → ℕ} {t i d : ℕ} :
    d ∈ departureTimes O stream t i ↔
      d < t ∧ UpwardDeparture O stream i d := by
  classical
  simp [departureTimes]

/-- Below a surviving old critical language, new criticality is exactly old
criticality. -/
theorem critical_iff_next_below_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t b i : ℕ}
    (hbold : RecursiveCritical C stream t b)
    (hbnew : RecursiveCritical C stream (t + 1) b)
    (hib : i ≤ b) :
    RecursiveCritical C stream (t + 1) i ↔
      RecursiveCritical C stream t i := by
  have hbfocus : IsFocus C stream t (b + 1) b := by
    exact ⟨Nat.lt_succ_self b, hbold,
      fun j hj _ => Nat.le_of_lt_succ hj⟩
  exact recursiveCritical_iff_of_focus_consistent
    (Nat.le_succ t) hbfocus (recursiveCritical_consistent hbnew)
    i (Nat.lt_succ_of_le hib)

/-- In a backtracking step, every new critical language strictly below the
new focus was already critical and strictly below the old focus.  In either
least-consistent fallback branch there is no such language. -/
theorem critical_below_backtrack_was_below_old_focus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hfalsified : ¬ Consistent C stream (t + 1) old.focus)
    (hexists : ∃ j, Consistent C stream (t + 1) j)
    (hiNew : RecursiveCritical C stream (t + 1) i)
    (hiBelow : i < (backtrackDecision C stream t old).focus) :
    RecursiveCritical C stream t i ∧ i < old.focus := by
  classical
  let consistent := consistentIndices C stream (t + 1) old.scope
  by_cases hcon : consistent.Nonempty
  · let survivors := survivingCriticalIndices C stream t old.scope
    by_cases hsurv : survivors.Nonempty
    · let b := highestSurvivor C stream t old.scope old.focus
      have hb := highestSurvivor_spec (fallback := old.focus) hsurv
      have hback : (backtrackDecision C stream t old).focus = b := by
        simp [backtrackDecision_of_survivor hcon hsurv, b]
      have hib : i < b := by simpa [hback] using hiBelow
      have hiOld : RecursiveCritical C stream t i :=
        (critical_iff_next_below_survivor hb.2.1 hb.2.2.1
          (Nat.le_of_lt hib)).1 hiNew
      have hbOldFocus : b < old.focus := by
        have hlt := backtrackDecision_focus_lt_of_survivor
          hfocus hfalsified hcon hsurv
        rw [hback] at hlt
        exact hlt
      exact ⟨hiOld, lt_trans hib hbOldFocus⟩
    · let b := lowestConsistentInScope C stream (t + 1)
        old.scope old.focus
      have hb := lowestConsistentInScope_spec
        (fallback := old.focus) hcon
      have hback : (backtrackDecision C stream t old).focus = b := by
        simp [backtrackDecision_of_no_survivor hcon hsurv, b]
      have hib : i < b := by simpa [hback] using hiBelow
      exact False.elim
        (hb.2.2 i hib (recursiveCritical_consistent hiNew))
  · let b := lowestConsistent C stream (t + 1) old.focus
    have hb := lowestConsistent_spec (fallback := old.focus) hexists
    have hback : (backtrackDecision C stream t old).focus = b := by
      simp [backtrackDecision_of_empty_scope hcon hexists, b]
    have hib : i < b := by simpa [hback] using hiBelow
    exact False.elim (hb.2 i hib (recursiveCritical_consistent hiNew))

/-- Every critical index below the current focus has an earlier upward
departure from that same index. -/
theorem exists_upwardDeparture_of_critical_lt_focus_of_onModel
    (O : OracleFamily) {stream : ℕ → ℕ}
    (hOn : OnModel O stream) :
    ∀ t i,
      RecursiveCritical O.language stream t i →
      i < (run O stream t).focus →
      ∃ d, d < t ∧ UpwardDeparture O stream i d := by
  intro t
  induction t with
  | zero =>
      intro i _ hi
      simp [initialState] at hi
  | succ t ih =>
      intro i hiNew hiBelow
      let old := run O stream t
      have hfocus : IsFocus O.language stream t old.scope old.focus :=
        run_focus_isFocus_of_onModel O hOn t
      have hexists : ∃ j, Consistent O.language stream (t + 1) j :=
        hOn (t + 1)
      by_cases hsurvives :
          Consistent O.language stream (t + 1) old.focus
      · have hfixed := fixed_scope_one_step hfocus hsurvives
        by_cases hchanged :
            (run O stream (t + 1)).focus = old.focus
        · have hiOld : RecursiveCritical O.language stream t i := by
            have hiscope : i < old.scope := by
              exact lt_trans (hchanged ▸ hiBelow) hfocus.1
            exact (hfixed.1 i hiscope).1 hiNew
          have hiOldFocus : i < old.focus := by
            rw [← hchanged]
            exact hiBelow
          obtain ⟨d, hdt, hdep⟩ := ih i hiOld hiOldFocus
          exact ⟨d, lt_trans hdt (Nat.lt_succ_self t), hdep⟩
        · have hchangedDecision :
              (stableDecision O.language stream t old).focus ≠ old.focus := by
            simpa [run_succ, processRound, decide, hsurvives, old] using hchanged
          have hchangeSpec := stableDecision_changed
            hfocus hsurvives hchangedDecision
          have hnewFocus : (run O stream (t + 1)).focus = old.scope := by
            simpa [run_succ, processRound, decide, hsurvives, old]
              using hchangeSpec.2
          have hiscope : i < old.scope := by
            rw [← hnewFocus]
            exact hiBelow
          have hiOld : RecursiveCritical O.language stream t i :=
            (hfixed.1 i hiscope).1 hiNew
          have hile : i ≤ old.focus := hfocus.2.2 i hiscope hiOld
          rcases eq_or_lt_of_le hile with rfl | hilt
          · refine ⟨t, Nat.lt_succ_self t, ?_⟩
            refine ⟨rfl, ?_, ?_⟩
            · simp [run_succ, processRound, decide, hsurvives, old,
                stableDecision, hchangeSpec.1]
            · simpa [old] using hiBelow
          · obtain ⟨d, hdt, hdep⟩ := ih i hiOld hilt
            exact ⟨d, lt_trans hdt (Nat.lt_succ_self t), hdep⟩
      · have hiOldBelow :=
          critical_below_backtrack_was_below_old_focus
            hfocus hsurvives hexists hiNew (by
              simpa [run_succ, processRound, decide, hsurvives, old]
                using hiBelow)
        obtain ⟨d, hdt, hdep⟩ := ih i hiOldBelow.1 hiOldBelow.2
        exact ⟨d, lt_trans hdt (Nat.lt_succ_self t), hdep⟩

/-- Exact-presentation wrapper for the on-model historical theorem. -/
theorem exists_upwardDeparture_of_critical_lt_focus
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∀ t i,
      RecursiveCritical O.language stream t i →
      i < (run O stream t).focus →
      ∃ d, d < t ∧ UpwardDeparture O stream i d :=
  exists_upwardDeparture_of_critical_lt_focus_of_onModel O
    (onModel_of_presents O hP)

/-- The wait test holds at every upward departure. -/
theorem upwardDeparture_wait_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {i d : ℕ}
    (hOn : OnModel O stream)
    (hdep : UpwardDeparture O stream i d) :
    2 ^ (run O stream d).tau ≤ (run O stream d).age := by
  classical
  have hfocus := run_focus_isFocus_of_onModel O hOn d
  have hstable : Consistent O.language stream (d + 1)
      (run O stream d).focus := by
    by_contra hnot
    have hmove : (run O stream (d + 1)).move = .backtrack := by
      simp [run_succ, processRound, decide, hnot,
        backtrackDecision_move]
    rw [hdep.2.1] at hmove
    cases hmove
  have hchanged :
      (stableDecision O.language stream d (run O stream d)).focus ≠
        (run O stream d).focus := by
    have hrunChanged : (run O stream (d + 1)).focus ≠
        (run O stream d).focus := by
      rw [hdep.1]
      exact Nat.ne_of_gt hdep.2.2
    simpa [run_succ, processRound, decide, hstable] using hrunChanged
  exact (stableDecision_changed hfocus hstable hchanged).1

theorem upwardDeparture_wait
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d) :
    2 ^ (run O stream d).tau ≤ (run O stream d).age :=
  upwardDeparture_wait_of_onModel (onModel_of_presents O hP) hdep

/-- The exponential waiting block fits before the departure time. -/
theorem upwardDeparture_pow_le_time_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {i d : ℕ}
    (hOn : OnModel O stream)
    (hdep : UpwardDeparture O stream i d) :
    2 ^ (run O stream d).tau ≤ d := by
  exact le_trans (upwardDeparture_wait_of_onModel hOn hdep)
    (run_age_le_time O stream d)

theorem upwardDeparture_pow_le_time
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d) :
    2 ^ (run O stream d).tau ≤ d :=
  upwardDeparture_pow_le_time_of_onModel (onModel_of_presents O hP) hdep

/-- Every post-state in the `2 ^ tau` rounds preceding a departure has the
departing focus.  The output in round `d - 1 - k` is made in post-state
`d - k`. -/
theorem upwardDeparture_age_block_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {i d k : ℕ}
    (hOn : OnModel O stream)
    (hdep : UpwardDeparture O stream i d)
    (hk : k < 2 ^ (run O stream d).tau) :
    (run O stream (d - k)).focus = i := by
  have hkAge : k < (run O stream d).age :=
    lt_of_lt_of_le hk (upwardDeparture_wait_of_onModel hOn hdep)
  rw [run_focus_eq_of_lt_age O stream d k hkAge]
  exact hdep.1

theorem upwardDeparture_age_block
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d k : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d)
    (hk : k < 2 ^ (run O stream d).tau) :
    (run O stream (d - k)).focus = i :=
  upwardDeparture_age_block_of_onModel
    (onModel_of_presents O hP) hdep hk

/-- The output in each charged predecessor round belongs to the departing
language. -/
theorem upwardDeparture_block_output_mem_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {i d k : ℕ}
    (hOn : OnModel O stream)
    (hdep : UpwardDeparture O stream i d)
    (hk : k < 2 ^ (run O stream d).tau) :
    output O stream (d - 1 - k) ∈ O.language i := by
  have hpTime := upwardDeparture_pow_le_time_of_onModel hOn hdep
  have hkTime : k < d := lt_of_lt_of_le hk hpTime
  have hindex : d - 1 - k + 1 = d - k := by omega
  have hout := output_mem_round_focus O stream (d - 1 - k)
  rw [hindex, upwardDeparture_age_block_of_onModel hOn hdep hk] at hout
  exact hout

theorem upwardDeparture_block_output_mem
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d k : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d)
    (hk : k < 2 ^ (run O stream d).tau) :
    output O stream (d - 1 - k) ∈ O.language i :=
  upwardDeparture_block_output_mem_of_onModel
    (onModel_of_presents O hP) hdep hk

/-- If the departing language is contained in the target, every output in
the charged block belongs to the target. -/
theorem upwardDeparture_block_output_mem_target
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d k : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d)
    (hsub : O.language i ⊆ O.language z)
    (hk : k < 2 ^ (run O stream d).tau) :
    output O stream (d - 1 - k) ∈ O.language z :=
  hsub (upwardDeparture_block_output_mem hP hdep hk)

/-- If a focus `i` survives until a later time at which the focus is higher,
then some intervening stable expansion departs upward from `i`. -/
theorem exists_upwardDeparture_between_of_onModel
    (O : OracleFamily) {stream : ℕ → ℕ} {a b i : ℕ}
    (hOn : OnModel O stream)
    (hab : a < b)
    (ha : (run O stream a).focus = i)
    (hb : i < (run O stream b).focus)
    (hcon : Consistent O.language stream b i) :
    ∃ d, a ≤ d ∧ d < b ∧ UpwardDeparture O stream i d := by
  generalize hn : b - a = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
      have ha1b : a + 1 ≤ b := Nat.succ_le_of_lt hab
      have hconNext : Consistent O.language stream (a + 1) i :=
        consistent_of_time_le ha1b hcon
      have hfocus := run_focus_isFocus_of_onModel O hOn a
      have hstable : Consistent O.language stream (a + 1)
          (run O stream a).focus := by simpa [ha] using hconNext
      have hleDecision := stableDecision_focus_le hfocus hstable
      have hle : i ≤ (run O stream (a + 1)).focus := by
        rw [run_succ_focus, decide, if_pos hstable]
        simpa [ha] using hleDecision
      by_cases heq : (run O stream (a + 1)).focus = i
      · have ha1ltb : a + 1 < b := by
          by_contra hnot
          have heqb : a + 1 = b := Nat.le_antisymm ha1b (Nat.le_of_not_gt hnot)
          rw [← heqb, heq] at hb
          exact (Nat.lt_irrefl i) hb
        have hdist : b - (a + 1) < n := by omega
        obtain ⟨d, ha1d, hdb, hdep⟩ :=
          ih (b - (a + 1)) hdist (a := a + 1) (b := b)
            ha1ltb heq hb hcon rfl
        exact ⟨d, le_trans (Nat.le_succ a) ha1d, hdb, hdep⟩
      · have hlt : i < (run O stream (a + 1)).focus := by omega
        have hchanged :
            (stableDecision O.language stream a (run O stream a)).focus ≠
              (run O stream a).focus := by
          have : (run O stream (a + 1)).focus ≠
              (run O stream a).focus := by
            rw [ha]
            exact heq
          simpa [run_succ, processRound, decide, hstable] using this
        have hwait := (stableDecision_changed hfocus hstable hchanged).1
        refine ⟨a, Nat.le_refl a, hab, ha, ?_, hlt⟩
        simp [run_succ, processRound, decide, hstable,
          stableDecision, hwait]

theorem exists_upwardDeparture_between
    (O : OracleFamily) {stream : ℕ → ℕ} {z a b i : ℕ}
    (hP : Presents stream (O.language z))
    (hab : a < b)
    (ha : (run O stream a).focus = i)
    (hb : i < (run O stream b).focus)
    (hcon : Consistent O.language stream b i) :
    ∃ d, a ≤ d ∧ d < b ∧ UpwardDeparture O stream i d :=
  exists_upwardDeparture_between_of_onModel O
    (onModel_of_presents O hP) hab ha hb hcon

/-- A certified downward landing is a backtracking endpoint which was already
critical immediately before the landing.  Late switch losses have this form
because the target is a surviving critical language. -/
structure CertifiedLanding
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : Prop where
  oldCritical : RecursiveCritical O.language stream t i
  newFocus : (run O stream (t + 1)).focus = i
  belowOldFocus : i < (run O stream t).focus

/-- Latest departure before `t`, totalized by zero when there is none. -/
noncomputable def latestDeparture
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : ℕ := by
  classical
  let ds := departureTimes O stream t i
  exact if h : ds.Nonempty then ds.max' h else 0

theorem latestDeparture_spec
    {O : OracleFamily} {stream : ℕ → ℕ} {t i : ℕ}
    (hne : (departureTimes O stream t i).Nonempty) :
    latestDeparture O stream t i < t ∧
      UpwardDeparture O stream i (latestDeparture O stream t i) := by
  classical
  let ds := departureTimes O stream t i
  have hmem : ds.max' hne ∈ ds := ds.max'_mem hne
  have heq : latestDeparture O stream t i = ds.max' hne := by
    simp [latestDeparture, ds, hne]
  rw [heq]
  exact mem_departureTimes.mp hmem

theorem departure_le_latest
    {O : OracleFamily} {stream : ℕ → ℕ} {t i d : ℕ}
    (hne : (departureTimes O stream t i).Nonempty)
    (hd : d < t) (hdep : UpwardDeparture O stream i d) :
    d ≤ latestDeparture O stream t i := by
  classical
  let ds := departureTimes O stream t i
  have hdmem : d ∈ ds := mem_departureTimes.mpr ⟨hd, hdep⟩
  have hle := Finset.le_max' ds d hdmem
  simpa [latestDeparture, ds, hne] using hle

theorem CertifiedLanding.departureTimes_nonempty_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t i : ℕ}
    (hOn : OnModel O stream)
    (hland : CertifiedLanding O stream t i) :
    (departureTimes O stream t i).Nonempty := by
  obtain ⟨d, hdt, hdep⟩ :=
    exists_upwardDeparture_of_critical_lt_focus_of_onModel O hOn t i
      hland.oldCritical hland.belowOldFocus
  exact ⟨d, mem_departureTimes.mpr ⟨hdt, hdep⟩⟩

theorem CertifiedLanding.departureTimes_nonempty
    {O : OracleFamily} {stream : ℕ → ℕ} {z t i : ℕ}
    (hP : Presents stream (O.language z))
    (hland : CertifiedLanding O stream t i) :
    (departureTimes O stream t i).Nonempty :=
  hland.departureTimes_nonempty_of_onModel (onModel_of_presents O hP)

theorem CertifiedLanding.latestDeparture_spec_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t i : ℕ}
    (hOn : OnModel O stream)
    (hland : CertifiedLanding O stream t i) :
    latestDeparture O stream t i < t ∧
      UpwardDeparture O stream i (latestDeparture O stream t i) :=
  PatientMachine.latestDeparture_spec
    (hland.departureTimes_nonempty_of_onModel hOn)

theorem CertifiedLanding.latestDeparture_spec
    {O : OracleFamily} {stream : ℕ → ℕ} {z t i : ℕ}
    (hP : Presents stream (O.language z))
    (hland : CertifiedLanding O stream t i) :
    latestDeparture O stream t i < t ∧
      UpwardDeparture O stream i (latestDeparture O stream t i) :=
  hland.latestDeparture_spec_of_onModel (onModel_of_presents O hP)

/-- Two successive certified landings at the same focus use strictly
increasing latest-departure rounds. -/
theorem latestDeparture_lt_of_certifiedLanding_same_focus_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t u i : ℕ}
    (hOn : OnModel O stream)
    (htu : t < u)
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u i) :
    latestDeparture O stream t i < latestDeparture O stream u i := by
  have htSpec := ht.latestDeparture_spec_of_onModel hOn
  have huNonempty := hu.departureTimes_nonempty_of_onModel hOn
  have ht1u : t + 1 < u := by
    by_contra hnot
    have hueq : u = t + 1 := by omega
    have hbelow := hu.belowOldFocus
    rw [hueq, ht.newFocus] at hbelow
    exact (Nat.lt_irrefl i) hbelow
  have hcon : Consistent O.language stream u i :=
    recursiveCritical_consistent hu.oldCritical
  obtain ⟨d, ht1d, hdu, hdep⟩ := exists_upwardDeparture_between_of_onModel
    O hOn ht1u ht.newFocus hu.belowOldFocus hcon
  have hdLatest : d ≤ latestDeparture O stream u i :=
    departure_le_latest huNonempty hdu hdep
  exact lt_of_lt_of_le (lt_trans htSpec.1 (lt_of_lt_of_le
    (Nat.lt_succ_self t) ht1d)) hdLatest

theorem latestDeparture_lt_of_certifiedLanding_same_focus
    {O : OracleFamily} {stream : ℕ → ℕ} {z t u i : ℕ}
    (hP : Presents stream (O.language z))
    (htu : t < u)
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u i) :
    latestDeparture O stream t i < latestDeparture O stream u i :=
  latestDeparture_lt_of_certifiedLanding_same_focus_of_onModel
    (onModel_of_presents O hP) htu ht hu

/-- The canonical latest departure determines a certified landing's time and
focus. -/
theorem certifiedLanding_latestDeparture_injective_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t u i j : ℕ}
    (hOn : OnModel O stream)
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u j)
    (heq : latestDeparture O stream t i =
      latestDeparture O stream u j) :
    t = u ∧ i = j := by
  have htSpec := ht.latestDeparture_spec_of_onModel hOn
  have huSpec := hu.latestDeparture_spec_of_onModel hOn
  have hij : i = j := by
    calc
      i = (run O stream (latestDeparture O stream t i)).focus :=
        htSpec.2.1.symm
      _ = (run O stream (latestDeparture O stream u j)).focus := by rw [heq]
      _ = j := huSpec.2.1
  subst j
  refine ⟨?_, rfl⟩
  rcases lt_trichotomy t u with htu | htu | hut
  · have hlt := latestDeparture_lt_of_certifiedLanding_same_focus_of_onModel
      hOn htu ht hu
    exact False.elim ((Nat.ne_of_lt hlt) heq)
  · exact htu
  · have hlt := latestDeparture_lt_of_certifiedLanding_same_focus_of_onModel
      hOn hut hu ht
    exact False.elim ((Nat.ne_of_lt hlt) heq.symm)

theorem certifiedLanding_latestDeparture_injective
    {O : OracleFamily} {stream : ℕ → ℕ} {z t u i j : ℕ}
    (hP : Presents stream (O.language z))
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u j)
    (heq : latestDeparture O stream t i =
      latestDeparture O stream u j) :
    t = u ∧ i = j :=
  certifiedLanding_latestDeparture_injective_of_onModel
    (onModel_of_presents O hP) ht hu heq

/-- Canonical focus-change label attached to a certified landing. -/
noncomputable def landingLabel
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : ℕ :=
  (run O stream (latestDeparture O stream t i)).tau

/-- Tau labels of different upward-departure rounds are different. -/
theorem upwardDeparture_tau_injective
    (O : OracleFamily) (stream : ℕ → ℕ) :
    Set.InjOn (fun d => (run O stream d).tau)
      {d | ∃ i, UpwardDeparture O stream i d} := by
  intro d hd e he hlabel
  rcases lt_trichotomy d e with hde | rfl | hed
  · obtain ⟨i, hi⟩ := hd
    have hchange : (run O stream (d + 1)).focus ≠
        (run O stream d).focus := by
      exact Nat.ne_of_gt (hi.1 ▸ hi.2.2)
    have hstep := run_succ_tau_eq_succ_of_focus_ne O stream d hchange
    have hmono := run_tau_mono O stream (Nat.succ_le_of_lt hde)
    have hlt : (run O stream d).tau < (run O stream e).tau := by
      calc
        (run O stream d).tau < (run O stream (d + 1)).tau := by omega
        _ ≤ (run O stream e).tau := hmono
    exact False.elim ((Nat.ne_of_lt hlt) hlabel)
  · rfl
  · obtain ⟨i, hi⟩ := he
    have hchange : (run O stream (e + 1)).focus ≠
        (run O stream e).focus := by
      exact Nat.ne_of_gt (hi.1 ▸ hi.2.2)
    have hstep := run_succ_tau_eq_succ_of_focus_ne O stream e hchange
    have hmono := run_tau_mono O stream (Nat.succ_le_of_lt hed)
    have hlt : (run O stream e).tau < (run O stream d).tau := by
      calc
        (run O stream e).tau < (run O stream (e + 1)).tau := by omega
        _ ≤ (run O stream d).tau := hmono
    exact False.elim ((Nat.ne_of_lt hlt) hlabel.symm)

/-- Equal canonical labels force equality of certified landing times and
focus indices. -/
theorem certifiedLanding_label_injective_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t u i j : ℕ}
    (hOn : OnModel O stream)
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u j)
    (heq : landingLabel O stream t i = landingLabel O stream u j) :
    t = u ∧ i = j := by
  have htSpec := ht.latestDeparture_spec_of_onModel hOn
  have huSpec := hu.latestDeparture_spec_of_onModel hOn
  have hdepEq : latestDeparture O stream t i =
      latestDeparture O stream u j := by
    apply upwardDeparture_tau_injective O stream
    · exact ⟨i, htSpec.2⟩
    · exact ⟨j, huSpec.2⟩
    · exact heq
  exact certifiedLanding_latestDeparture_injective_of_onModel
    hOn ht hu hdepEq

theorem certifiedLanding_label_injective
    {O : OracleFamily} {stream : ℕ → ℕ} {z t u i j : ℕ}
    (hP : Presents stream (O.language z))
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u j)
    (heq : landingLabel O stream t i = landingLabel O stream u j) :
    t = u ∧ i = j :=
  certifiedLanding_label_injective_of_onModel
    (onModel_of_presents O hP) ht hu heq

end PatientMachine
end GenLimit
