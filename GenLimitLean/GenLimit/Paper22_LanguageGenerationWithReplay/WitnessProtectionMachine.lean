import GenLimit.Paper22_LanguageGenerationWithReplay.LimitSeparation
import GenLimit.Paper22_LanguageGenerationWithReplay.WitnessProtection

/-!
# The stateful Witness Protection machine

This module turns the finite membership-query round from
`Replay.WitnessProtection` into a causal, source-equivalent normalization of
Algorithm 2 in Racca--Valko--Sanyal, arXiv:2603.11784v2.  The source reuses a
monotone cutoff between rounds; Lean restarts that terminating finite search
at zero each round.  This changes query reuse, not the selected predicate,
witness protection, per-round termination, or the semantic correctness
argument.

At the beginning of a round, `pastOutputs` is exactly the finite set of
earlier machine outputs.  The incoming example is added to `sure` precisely
when it is not one of those outputs.  The round then invokes the terminating
finite-oracle-defined search and records its output.

The construction below is executable relative to the supplied Boolean
membership oracle, but it is the earlier restart-normalized variant.  The
literal carried-cutoff implementation and its explicit finite query cache
live in `CarriedCutoff.lean` and `FiniteQueryTrace.lean`; arbitrary-countable
semantic transport lives in `CountableTransport.lean`.
-/

namespace GenLimit

open GenLimit.Generic
open GenLimit.Replay

namespace OracleFamily

variable (O : GenLimit.OracleFamily)

structure WitnessProtectionState where
  sure : Finset ℕ
  pastOutputs : Finset ℕ
  output : ℕ

def witnessProtectionInitial : WitnessProtectionState :=
  ⟨∅, ∅, 0⟩

/-- The source's sure-set update. -/
def witnessProtectionSureUpdate
    (state : WitnessProtectionState) (x : ℕ) : Finset ℕ :=
  if x ∈ state.pastOutputs then state.sure else insert x state.sure

/-- The inactive fallback branch is irrelevant on a replay enumeration of a
represented target.  It is made total by returning the least sure point when
one exists. -/
def witnessProtectionFallback
    (sure : Finset ℕ) : ℕ :=
  if h : sure.Nonempty then sure.min' h else 0

/-- One restart-normalized semantic round after receiving the new example. -/
def witnessProtectionProcessRound
    (state : WitnessProtectionState) (x t : ℕ) :
    WitnessProtectionState :=
  let sure := witnessProtectionSureUpdate state x
  if hactive : O.HasReplayActive sure t then
    let out :=
      O.replayRoundOutput sure state.pastOutputs t hactive
    ⟨sure, insert out state.pastOutputs, out⟩
  else
    let out := witnessProtectionFallback sure
    ⟨sure, insert out state.pastOutputs, out⟩

/-- The state after processing the first `t` observations. -/
def witnessProtectionRun
    (O : GenLimit.OracleFamily)
    (stream : ℕ → ℕ) : ℕ → WitnessProtectionState
  | 0 => witnessProtectionInitial
  | t + 1 =>
      O.witnessProtectionProcessRound
        (witnessProtectionRun O stream t) (stream t) (t + 1)

@[simp] theorem witnessProtectionRun_zero
    (stream : ℕ → ℕ) :
    O.witnessProtectionRun stream 0 = witnessProtectionInitial := rfl

@[simp] theorem witnessProtectionRun_succ
    (stream : ℕ → ℕ) (t : ℕ) :
    O.witnessProtectionRun stream (t + 1) =
      O.witnessProtectionProcessRound
        (O.witnessProtectionRun stream t) (stream t) (t + 1) := rfl

theorem witnessProtectionProcessRound_sure
    (state : WitnessProtectionState) (x t : ℕ) :
    (O.witnessProtectionProcessRound state x t).sure =
      witnessProtectionSureUpdate state x := by
  unfold witnessProtectionProcessRound
  dsimp only
  split <;> rfl

theorem witnessProtectionProcessRound_pastOutputs
    (state : WitnessProtectionState) (x t : ℕ) :
    (O.witnessProtectionProcessRound state x t).pastOutputs =
      insert (O.witnessProtectionProcessRound state x t).output
        state.pastOutputs := by
  simp [witnessProtectionProcessRound]
  split <;> rfl

theorem witnessProtectionProcessRound_of_active
    (state : WitnessProtectionState) (x t : ℕ)
    (hactive :
      O.HasReplayActive (witnessProtectionSureUpdate state x) t) :
    O.witnessProtectionProcessRound state x t =
      let sure := witnessProtectionSureUpdate state x
      let out := O.replayRoundOutput sure state.pastOutputs t hactive
      ⟨sure, insert out state.pastOutputs, out⟩ := by
  simp [witnessProtectionProcessRound, hactive]

theorem witnessProtectionRun_succ_output_of_active
    (stream : ℕ → ℕ) (t : ℕ)
    (hactive :
      O.HasReplayActive
        (witnessProtectionSureUpdate
          (O.witnessProtectionRun stream t) (stream t)) (t + 1)) :
    (O.witnessProtectionRun stream (t + 1)).output =
      O.replayRoundOutput
        (witnessProtectionSureUpdate
          (O.witnessProtectionRun stream t) (stream t))
        (O.witnessProtectionRun stream t).pastOutputs
        (t + 1) hactive := by
  rw [O.witnessProtectionRun_succ,
    O.witnessProtectionProcessRound_of_active
      (O.witnessProtectionRun stream t) (stream t) (t + 1) hactive]

theorem witnessProtectionSureUpdate_mono
    (state : WitnessProtectionState) (x : ℕ) :
    state.sure ⊆ witnessProtectionSureUpdate state x := by
  intro y hy
  simp only [witnessProtectionSureUpdate]
  split
  · exact hy
  · exact Finset.mem_insert_of_mem hy

theorem witnessProtectionRun_sure_mono
    (stream : ℕ → ℕ) (t : ℕ) :
    (O.witnessProtectionRun stream t).sure ⊆
      (O.witnessProtectionRun stream (t + 1)).sure := by
  rw [O.witnessProtectionRun_succ,
    O.witnessProtectionProcessRound_sure]
  exact witnessProtectionSureUpdate_mono _ _

theorem witnessProtectionRun_pastOutputs_mono
    (stream : ℕ → ℕ) (t : ℕ) :
    (O.witnessProtectionRun stream t).pastOutputs ⊆
      (O.witnessProtectionRun stream (t + 1)).pastOutputs := by
  rw [O.witnessProtectionRun_succ,
    O.witnessProtectionProcessRound_pastOutputs]
  exact Finset.subset_insert _ _

theorem witnessProtectionRun_sure_mono_of_le
    (stream : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    (O.witnessProtectionRun stream s).sure ⊆
      (O.witnessProtectionRun stream t).sure := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t _ ih =>
      exact ih.trans (O.witnessProtectionRun_sure_mono stream t)

theorem witnessProtectionRun_pastOutputs_mono_of_le
    (stream : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    (O.witnessProtectionRun stream s).pastOutputs ⊆
      (O.witnessProtectionRun stream t).pastOutputs := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t _ ih =>
      exact ih.trans
        (O.witnessProtectionRun_pastOutputs_mono stream t)

theorem witnessProtectionRun_output_mem
    (stream : ℕ → ℕ) {t : ℕ} (ht : 0 < t) :
    (O.witnessProtectionRun stream t).output ∈
      (O.witnessProtectionRun stream t).pastOutputs := by
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [O.witnessProtectionRun_succ,
    O.witnessProtectionProcessRound_pastOutputs]
  exact Finset.mem_insert_self _ _

/-! ## Causality and the generic generator interface -/

/-- Complete a finite history by zeros.  Only its exposed prefix is used. -/
def witnessProtectionPrefixStream
    {t : ℕ} (xs : Fin t → ℕ) : ℕ → ℕ :=
  fun k => if hk : k < t then xs ⟨k, hk⟩ else 0

theorem witnessProtectionRun_congr
    {stream₁ stream₂ : ℕ → ℕ} :
    ∀ {t}, (∀ k, k < t → stream₁ k = stream₂ k) →
      O.witnessProtectionRun stream₁ t =
        O.witnessProtectionRun stream₂ t := by
  intro t hprefix
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [O.witnessProtectionRun_succ,
        O.witnessProtectionRun_succ,
        ih (fun k hk => hprefix k (Nat.lt.step hk)),
        hprefix t (Nat.lt_add_one t)]

/-- The executable reset-cutoff core of Algorithm 2 as a generic causal
generator.  The explicit trace theorem is stated for the source-facing
carried-cutoff machine. -/
def witnessProtectionGenerator :
    Generic.Generator ℕ :=
  fun t xs =>
    (O.witnessProtectionRun
      (witnessProtectionPrefixStream xs) t).output

theorem output_witnessProtectionGenerator
    (stream : ℕ → ℕ) (t : ℕ) :
    Generic.output O.witnessProtectionGenerator stream t =
      (O.witnessProtectionRun stream t).output := by
  apply congrArg WitnessProtectionState.output
  apply O.witnessProtectionRun_congr
  intro k hk
  simp [witnessProtectionPrefixStream, hk]

theorem witnessProtection_output_mem_pastOutputs
    (stream : ℕ → ℕ) {k t : ℕ}
    (hk : 0 < k) (hkt : k ≤ t) :
    Generic.output O.witnessProtectionGenerator stream k ∈
      (O.witnessProtectionRun stream t).pastOutputs := by
  rw [O.output_witnessProtectionGenerator]
  exact O.witnessProtectionRun_pastOutputs_mono_of_le stream hkt
    (O.witnessProtectionRun_output_mem stream hk)

/-! ## Sure-set invariants on replay streams -/

/-- Every sure observation is target-valid.  If a replay alternative is used,
the alleged earlier output is already in `pastOutputs`, contradicting the
sure-set insertion test. -/
theorem witnessProtectionRun_sure_subset_target
    {z : ℕ} {stream : ℕ → ℕ}
    (hreplay :
      IsReplaySequence O.witnessProtectionGenerator
        (O.language z) stream) :
    ∀ t, (↑(O.witnessProtectionRun stream t).sure : Set ℕ) ⊆
      O.language z := by
  intro t
  induction t with
  | zero =>
      simp [witnessProtectionRun, witnessProtectionInitial]
  | succ t ih =>
      rw [O.witnessProtectionRun_succ,
        O.witnessProtectionProcessRound_sure]
      simp only [witnessProtectionSureUpdate]
      split
      · exact ih
      · rename_i hnotOutput
        intro y hy
        rw [Finset.mem_coe, Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · rcases hreplay t with htarget |
            ⟨k, hkpos, hkt, hkout⟩
          · exact htarget
          · exfalso
            apply hnotOutput
            rw [← hkout]
            exact O.witnessProtection_output_mem_pastOutputs
              stream hkpos hkt
        · exact ih (by simpa using hy)

theorem witnessProtection_target_active
    {z t : ℕ} {stream : ℕ → ℕ}
    (hreplay :
      IsReplaySequence O.witnessProtectionGenerator
        (O.language z) stream)
    (hzt : z < t) :
    O.HasReplayActive
      (O.witnessProtectionRun stream t).sure t := by
  refine ⟨z, O.mem_replayActive.mpr ⟨hzt, ?_⟩⟩
  apply O.replayConsistentAt_iff.mpr
  exact O.witnessProtectionRun_sure_subset_target hreplay t

/-- One induction step in Lemma 6.3: a fixed least target-versus-earlier
witness cannot enter the output ledger while both indices remain active. -/
theorem witnessProtectionRun_succ_protects_witness
    {z j r : ℕ} {stream : ℕ → ℕ}
    {basePast : Finset ℕ}
    (hreplay :
      IsReplaySequence O.witnessProtectionGenerator
        (O.language z) stream)
    (hzr : z < r + 1)
    (hjz : j < z)
    (hjconsistent :
      O.ReplayConsistentAt
        (O.witnessProtectionRun stream (r + 1)).sure j)
    (hbase :
      basePast ⊆
        (O.witnessProtectionRun stream r).pastOutputs)
    (hdiff : O.HasReplayDifference basePast z j)
    (hwPast :
      O.replayLeastDifference basePast z j ∉
        (O.witnessProtectionRun stream r).pastOutputs) :
    O.replayLeastDifference basePast z j ∉
      (O.witnessProtectionRun stream (r + 1)).pastOutputs := by
  let previous := O.witnessProtectionRun stream r
  let sure :=
    witnessProtectionSureUpdate previous (stream r)
  let w := O.replayLeastDifference basePast z j
  have hsureEq :
      sure = (O.witnessProtectionRun stream (r + 1)).sure := by
    rw [O.witnessProtectionRun_succ,
      O.witnessProtectionProcessRound_sure]
  have hzCons : O.ReplayConsistentAt sure z := by
    apply O.replayConsistentAt_iff.mpr
    intro x hx
    apply O.witnessProtectionRun_sure_subset_target hreplay (r + 1)
    have hmemEq :
        (x ∈ sure) =
          (x ∈ (O.witnessProtectionRun stream (r + 1)).sure) :=
      congrArg (fun S : Finset ℕ => x ∈ S) hsureEq
    exact hmemEq.mp hx
  have hactive : O.HasReplayActive sure (r + 1) :=
    ⟨z, O.mem_replayActive.mpr ⟨hzr, hzCons⟩⟩
  have hzActive : z ∈ O.replayActive sure (r + 1) := by
    exact O.mem_replayActive.mpr ⟨hzr, hzCons⟩
  have hjr : j < r + 1 := lt_trans hjz hzr
  have hjConsSure : O.ReplayConsistentAt sure j := by
    apply O.replayConsistentAt_iff.mpr
    intro x hx
    apply O.replayConsistentAt_iff.mp hjconsistent
    have hmemEq :
        (x ∈ sure) =
          (x ∈ (O.witnessProtectionRun stream (r + 1)).sure) :=
      congrArg (fun S : Finset ℕ => x ∈ S) hsureEq
    exact hmemEq.mp hx
  have hjActive : j ∈ O.replayActive sure (r + 1) :=
    O.mem_replayActive.mpr ⟨hjr, hjConsSure⟩
  have hwSpec := O.replayLeastDifference_spec hdiff
  have hleastCurrent :
      ∀ x, x < w → x ∈ O.language z →
        x ∉ O.language j →
        x ∉ previous.pastOutputs → False := by
    intro x hx hxi hxj hxPrevious
    exact O.replayLeastDifference_minimal hdiff x hx hxi hxj
      (fun hxBase => hxPrevious (hbase hxBase))
  have hroundNe :
      O.replayRoundOutput sure previous.pastOutputs
        (r + 1) hactive ≠ w := by
    exact O.replayRoundOutput_ne_leastDifference
      hactive hzActive hjActive hjz
      hwSpec.1 hwSpec.2.1 hwPast hleastCurrent
  have houtEq :
      (O.witnessProtectionRun stream (r + 1)).output =
        O.replayRoundOutput sure previous.pastOutputs
          (r + 1) hactive := by
    exact O.witnessProtectionRun_succ_output_of_active
      stream r hactive
  rw [O.witnessProtectionRun_succ,
    O.witnessProtectionProcessRound_pastOutputs]
  simp only [Finset.mem_insert, not_or]
  refine ⟨?_, hwPast⟩
  intro hwEq
  apply hroundNe
  rw [← houtEq]
  simpa [previous] using hwEq.symm

/-- The induction from Lemma 6.3.  A least witness fixed immediately before
target index `z` becomes eligible is absent from every later output ledger for
as long as the earlier index remains consistent. -/
theorem witnessProtection_leastDifference_protected
    {z j : ℕ} {stream : ℕ → ℕ}
    (hreplay :
      IsReplaySequence O.witnessProtectionGenerator
        (O.language z) stream)
    (hjz : j < z)
    (hdiff :
      O.HasReplayDifference
        (O.witnessProtectionRun stream z).pastOutputs z j) :
    ∀ t, z + 1 ≤ t →
      O.ReplayConsistentAt
        (O.witnessProtectionRun stream t).sure j →
      O.replayLeastDifference
          (O.witnessProtectionRun stream z).pastOutputs z j ∉
        (O.witnessProtectionRun stream t).pastOutputs := by
  intro t hzt
  induction t, hzt using Nat.le_induction with
  | base =>
      intro hjconsistent
      apply O.witnessProtectionRun_succ_protects_witness
        hreplay (Nat.lt_succ_self z) hjz hjconsistent
        (Finset.Subset.rfl) hdiff
      exact (O.replayLeastDifference_spec hdiff).2.2
  | succ t hzt ih =>
      intro hjconsistent
      have hjPrevious :
          O.ReplayConsistentAt
            (O.witnessProtectionRun stream t).sure j := by
        exact O.replayConsistentAt_mono
          (O.witnessProtectionRun_sure_mono stream t)
          hjconsistent
      have hwPrevious := ih hjPrevious
      apply O.witnessProtectionRun_succ_protects_witness
        hreplay
        (Nat.lt.step
          (lt_of_lt_of_le (Nat.lt_succ_self z) hzt))
        hjz hjconsistent
        (O.witnessProtectionRun_pastOutputs_mono_of_le
          stream (Nat.le_of_succ_le hzt))
        hdiff hwPrevious

/-- Each genuinely separating earlier index is permanently evicted.  Replay
enumeration eventually presents the protected witness; because the machine
has never output it while the index remains active, that occurrence enters
the sure set and witnesses inconsistency forever. -/
theorem witnessProtection_difference_eventually_inconsistent
    {z j : ℕ} {stream : ℕ → ℕ}
    (henum :
      IsReplayEnumeration O.witnessProtectionGenerator
        (O.language z) stream)
    (hjz : j < z)
    (hdiff :
      O.HasReplayDifference
        (O.witnessProtectionRun stream z).pastOutputs z j) :
    ∃ T, ∀ t, T ≤ t →
      ¬O.ReplayConsistentAt
        (O.witnessProtectionRun stream t).sure j := by
  let basePast :=
    (O.witnessProtectionRun stream z).pastOutputs
  let w := O.replayLeastDifference basePast z j
  have hwSpec := O.replayLeastDifference_spec hdiff
  obtain ⟨n, hn⟩ := henum.2 w hwSpec.1
  let T := max (z + 1) (n + 1)
  refine ⟨T, ?_⟩
  intro t hTt hjconsistent
  have hnT : n + 1 ≤ T := Nat.le_max_right _ _
  have hnt : n ≤ t :=
    (Nat.le_trans (Nat.le_succ n) (hnT.trans hTt))
  have hwNotPast :
      w ∉ (O.witnessProtectionRun stream n).pastOutputs := by
    by_cases hnz : n ≤ z
    · intro hwPastN
      exact hwSpec.2.2
        (O.witnessProtectionRun_pastOutputs_mono_of_le
          stream hnz hwPastN)
    · have hzn : z + 1 ≤ n := by omega
      have hjconsistentN :
          O.ReplayConsistentAt
            (O.witnessProtectionRun stream n).sure j := by
        exact O.replayConsistentAt_mono
          (O.witnessProtectionRun_sure_mono_of_le
            stream hnt)
          hjconsistent
      exact O.witnessProtection_leastDifference_protected
        henum.1 hjz hdiff n hzn hjconsistentN
  have hwSureNext :
      w ∈ (O.witnessProtectionRun stream (n + 1)).sure := by
    rw [O.witnessProtectionRun_succ,
      O.witnessProtectionProcessRound_sure]
    simp [witnessProtectionSureUpdate, hn, hwNotPast]
  have hwSure :
      w ∈ (O.witnessProtectionRun stream t).sure := by
    exact O.witnessProtectionRun_sure_mono_of_le
      stream (hnT.trans hTt) hwSureNext
  have hwj :
      w ∈ O.language j :=
    O.replayConsistentAt_iff.mp hjconsistent
      (by simpa using hwSure)
  exact hwSpec.2.1 hwj

/-- Lemma 6.3: the true index eventually becomes replay-critical at every
finite cutoff.  Earlier indices with a genuine target witness are evicted by
the preceding theorem; every remaining earlier index already contains the
target modulo the finite output ledger fixed before index `z` became active. -/
theorem witnessProtection_target_eventually_critical
    {z : ℕ} {stream : ℕ → ℕ}
    (henum :
      IsReplayEnumeration O.witnessProtectionGenerator
        (O.language z) stream) :
    ∃ T, ∀ t, T ≤ t →
      O.ReplayCriticalAt
        (O.witnessProtectionRun stream t).sure
        (O.witnessProtectionRun stream (t - 1)).pastOutputs z := by
  classical
  let basePast :=
    (O.witnessProtectionRun stream z).pastOutputs
  let P : ℕ → ℕ → Prop :=
    fun j t =>
      O.ReplayConsistentAt
          (O.witnessProtectionRun stream t).sure j →
        ∀ x, x ∈ O.language z →
          x ∉ (O.witnessProtectionRun stream (t - 1)).pastOutputs →
          x ∈ O.language j
  have hEach :
      ∀ j ∈ Finset.range z, ∃ T, ∀ t, T ≤ t → P j t := by
    intro j hj
    have hjz : j < z := Finset.mem_range.mp hj
    by_cases hdiff : O.HasReplayDifference basePast z j
    · obtain ⟨Tj, hTj⟩ :=
        O.witnessProtection_difference_eventually_inconsistent
          henum hjz hdiff
      refine ⟨Tj, ?_⟩
      intro t hTt hjconsistent
      exact False.elim ((hTj t hTt) hjconsistent)
    · refine ⟨z + 1, ?_⟩
      intro t hzt _hjconsistent x hxz hxPast
      by_contra hxj
      have hxBase : x ∈ basePast := by
        by_contra hxBase
        exact hdiff ⟨x, hxz, hxj, hxBase⟩
      apply hxPast
      apply O.witnessProtectionRun_pastOutputs_mono_of_le stream
      · exact Nat.le_sub_one_of_lt
          (Nat.lt_of_succ_le hzt)
      · exact hxBase
  have finiteEventually :
      ∀ S : Finset ℕ,
        (∀ j ∈ S, ∃ T, ∀ t, T ≤ t → P j t) →
        ∃ T, ∀ t, T ≤ t → ∀ j ∈ S, P j t := by
    intro S hS
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨0, by simp⟩
    | @insert j S hjS ih =>
        obtain ⟨Tj, hTj⟩ :=
          hS j (Finset.mem_insert_self j S)
        obtain ⟨TS, hTS⟩ := ih (by
          intro i hi
          exact hS i (Finset.mem_insert_of_mem hi))
        refine ⟨max Tj TS, ?_⟩
        intro t hmax i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact hTj t ((Nat.le_max_left _ _).trans hmax)
        · exact hTS t ((Nat.le_max_right _ _).trans hmax) i hi
  have hAll :
      ∃ T, ∀ t, T ≤ t → ∀ j ∈ Finset.range z, P j t := by
    exact finiteEventually (Finset.range z) hEach
  obtain ⟨T₀, hT₀⟩ := hAll
  refine ⟨max (z + 1) T₀, ?_⟩
  intro t ht
  have hT₀t : T₀ ≤ t :=
    (Nat.le_max_right (z + 1) T₀).trans ht
  refine ⟨?_, ?_⟩
  · apply O.replayConsistentAt_iff.mpr
    exact O.witnessProtectionRun_sure_subset_target henum.1 t
  · intro j hjz hjconsistent x hxz hxPast
    exact hT₀ t hT₀t j (Finset.mem_range.mpr hjz)
      hjconsistent x hxz hxPast

/-- Every observed example is either in the current sure set or was already
an output before the current round. -/
theorem witnessProtection_sample_covered :
    ∀ (stream : ℕ → ℕ) {t : ℕ}, 0 < t →
      Generic.sample stream t ⊆
        (O.witnessProtectionRun stream t).sure ∪
          (O.witnessProtectionRun stream (t - 1)).pastOutputs := by
  intro stream t ht x hx
  obtain ⟨s, hst, rfl⟩ := Generic.mem_sample_iff.mp hx
  have hsle : s + 1 ≤ t := Nat.succ_le_iff.mpr hst
  by_cases hout :
      stream s ∈ (O.witnessProtectionRun stream s).pastOutputs
  · apply Finset.mem_union_right
    apply O.witnessProtectionRun_pastOutputs_mono_of_le stream
    · exact Nat.le_sub_one_of_lt hst
    · exact hout
  · apply Finset.mem_union_left
    apply O.witnessProtectionRun_sure_mono_of_le stream hsle
    rw [O.witnessProtectionRun_succ,
      O.witnessProtectionProcessRound_sure]
    simp [witnessProtectionSureUpdate, hout]

set_option maxHeartbeats 800000 in
/-- The current output is fresh from the whole observed sample whenever the
represented target makes the active branch reachable. -/
theorem witnessProtection_output_fresh
    {z t : ℕ} {stream : ℕ → ℕ}
    (hreplay :
      IsReplaySequence O.witnessProtectionGenerator
        (O.language z) stream)
    (hzt : z < t) :
    Generic.output O.witnessProtectionGenerator stream t ∉
      Generic.sample stream t := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le z) hzt
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  let previous := O.witnessProtectionRun stream s
  let sure :=
    witnessProtectionSureUpdate previous (stream s)
  have hsure :
      sure = (O.witnessProtectionRun stream (s + 1)).sure := by
    simp [sure, previous,
      O.witnessProtectionProcessRound_sure]
  have hactive :
      O.HasReplayActive sure (s + 1) := by
    rw [hsure]
    exact O.witnessProtection_target_active hreplay hzt
  have hfresh :=
    O.replayRoundOutput_fresh
      (pastOutputs := previous.pastOutputs) hactive
  have houtEq :
      Generic.output O.witnessProtectionGenerator stream (s + 1) =
        O.replayRoundOutput sure previous.pastOutputs (s + 1) hactive := by
    rw [O.output_witnessProtectionGenerator]
    exact O.witnessProtectionRun_succ_output_of_active
      stream s hactive
  rw [houtEq]
  intro houtSample
  have hcovered :=
    O.witnessProtection_sample_covered stream
      (t := s + 1) (Nat.zero_lt_succ s) houtSample
  rcases Finset.mem_union.mp hcovered with houtSure | houtPast
  · apply hfresh.1
    let out :=
      O.replayRoundOutput sure previous.pastOutputs (s + 1) hactive
    have hmemEq :
        (out ∈ sure) =
          (out ∈ (O.witnessProtectionRun stream (s + 1)).sure) :=
      congrArg (fun S : Finset ℕ => out ∈ S) hsure
    exact hmemEq.mpr houtSure
  · exact hfresh.2 (by simpa [previous] using houtPast)

/-! ## Lemma 6.5 and Theorem 6.1 -/

/-- Lemma 6.5: every replay enumeration of an indexed target eventually
receives fresh, target-valid outputs from Witness Protection. -/
theorem witnessProtection_eventual_correctness
    {z : ℕ} {stream : ℕ → ℕ}
    (henum :
      IsReplayEnumeration O.witnessProtectionGenerator
        (O.language z) stream) :
    ∃ T, ∀ t, T ≤ t →
      Generic.CorrectAt O.witnessProtectionGenerator
        (O.language z) stream t := by
  obtain ⟨Tcritical, hcritical⟩ :=
    O.witnessProtection_target_eventually_critical henum
  refine ⟨max Tcritical (z + 1), ?_⟩
  intro t ht
  have hTcritical : Tcritical ≤ t :=
    (Nat.le_max_left Tcritical (z + 1)).trans ht
  have hzt : z < t :=
    Nat.lt_of_succ_le
      ((Nat.le_max_right Tcritical (z + 1)).trans ht)
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le z) hzt
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
  let previous := O.witnessProtectionRun stream s
  let sure :=
    witnessProtectionSureUpdate previous (stream s)
  have hsureEq :
      sure = (O.witnessProtectionRun stream (s + 1)).sure := by
    rw [O.witnessProtectionRun_succ,
      O.witnessProtectionProcessRound_sure]
  have hcritical' :
      O.ReplayCriticalAt sure previous.pastOutputs z := by
    have hsource := hcritical (s + 1) hTcritical
    simpa [previous, hsureEq] using hsource
  have hactive : O.HasReplayActive sure (s + 1) :=
    ⟨z, O.mem_replayActive.mpr ⟨hzt, hcritical'.1⟩⟩
  let m :=
    O.replayRoundCutoff sure previous.pastOutputs (s + 1) hactive
  have hzfinite :
      O.ReplayFinitelyCriticalAt sure previous.pastOutputs m z :=
    O.replayCriticalAt_finitelyCriticalAt hcritical' m
  have houtTarget :
      O.replayRoundOutput sure previous.pastOutputs
          (s + 1) hactive ∈ O.language z := by
    exact O.replayRoundOutput_mem_of_targetCritical
      hactive hzt hzfinite
  have houtEq :
      Generic.output O.witnessProtectionGenerator stream (s + 1) =
        O.replayRoundOutput sure previous.pastOutputs
          (s + 1) hactive := by
    rw [O.output_witnessProtectionGenerator]
    exact O.witnessProtectionRun_succ_output_of_active
      stream s hactive
  refine ⟨?_, O.witnessProtection_output_fresh henum.1 hzt⟩
  rw [houtEq]
  exact houtTarget

/-- Semantic core of Theorem 6.1 for an explicitly indexed infinite family
over `ℕ` with a uniform Boolean membership oracle. -/
theorem theorem_6_1 :
    IsLimitReplayGenerator O.witnessProtectionGenerator
      (Set.range O.language) := by
  intro L hL stream henum
  obtain ⟨z, rfl⟩ := hL
  exact O.witnessProtection_eventual_correctness henum

/-- Paper-shaped semantic existence wrapper for the restart-normalized
variant on the `ℕ` domain.  The source-facing finite-query theorem uses the
literal carried-cutoff variant instead. -/
theorem theorem_6_1_paper :
    ∃ gen : Generic.Generator ℕ,
      IsLimitReplayGenerator gen (Set.range O.language) :=
  ⟨O.witnessProtectionGenerator, O.theorem_6_1⟩

end OracleFamily

namespace Replay

/-- Source-facing entry point for the semantic core of Theorem 6.1. -/
theorem theorem_6_1 (O : GenLimit.OracleFamily) :
    IsLimitReplayGenerator O.witnessProtectionGenerator
      (Set.range O.language) :=
  O.theorem_6_1

/-- Source-facing existential form of the semantic Theorem 6.1 core. -/
theorem theorem_6_1_paper (O : GenLimit.OracleFamily) :
    ∃ gen : Generic.Generator ℕ,
      IsLimitReplayGenerator gen (Set.range O.language) :=
  O.theorem_6_1_paper

end Replay

end GenLimit
