import GenLimit.Paper22_LanguageGenerationWithReplay.CountableTransport

/-!
# The literal carried-cutoff Witness Protection round

Algorithm 2 in Racca--Valko--Sanyal carries its finite-prefix cutoff between
rounds.  After receiving `x`, it raises the cutoff past both the previous
cutoff and `x`, increments once, and then searches upward until an admissible
output exists.

The earlier semantic development restarts this terminating search each round.
This file removes that normalization.  It proves termination above every
prescribed lower bound, defines the corresponding output, verifies all of the
criticality, validity, freshness, and protected-witness properties used by
Lemmas 6.3--6.5, and gives the exact persistent-state transition.

The definitions are executable relative to the Boolean membership oracle:
the finite predicates are decidable and `Nat.find` performs the proved-
terminating search.  `FiniteQueryTrace.lean` exposes an explicit finite answer
cache covering every query required through the first admissible cutoff.  A
separate Mathlib `Computable` certificate is not asserted here.
-/

namespace GenLimit
namespace OracleFamily

open GenLimit.Generic
open GenLimit.Replay

variable (O : GenLimit.OracleFamily)

/-- Strengthened Lemma 6.4: the admissible search terminates even when it
starts above an arbitrary carried lower bound. -/
theorem replayAdmissible_eventually_nonempty_from
    {sure pastOutputs : Finset ℕ} {t : ℕ}
    (hactive : O.HasReplayActive sure t) (lower : ℕ) :
    ∃ m, lower ≤ m ∧
      (O.replayAdmissible sure pastOutputs t m hactive).Nonempty := by
  classical
  obtain ⟨M, hM⟩ :=
    O.replaySelected_eventually_constant
      (pastOutputs := pastOutputs) hactive
  let n := O.replaySelected sure pastOutputs t M hactive
  let B :=
    sure.card + pastOutputs.card +
      (O.replayActive sure t).card *
        (O.replayActive sure t).card
  obtain ⟨K, hKsub, hKcard⟩ :=
    (O.infinite' n).exists_subset_card_eq (B + 1)
  have hKnonempty : K.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hKempty
    rw [hKempty] at hKcard
    simp [B] at hKcard
  let base := max M (K.max' hKnonempty + 1)
  let m := max lower base
  have hlower : lower ≤ m := Nat.le_max_left _ _
  have hBasem : base ≤ m := Nat.le_max_right _ _
  have hMm : M ≤ m :=
    (Nat.le_max_left M (K.max' hKnonempty + 1)).trans hBasem
  have hselected :
      O.replaySelected sure pastOutputs t m hactive = n := by
    exact hM m hMm
  have hKprefix : K ⊆ O.finitePrefix n m := by
    intro x hx
    apply O.mem_finitePrefix.mpr
    refine ⟨?_, hKsub (by simpa using hx)⟩
    have hxmax : x ≤ K.max' hKnonempty :=
      Finset.le_max' K x hx
    have hmaxBase :
        K.max' hKnonempty + 1 ≤ base :=
      Nat.le_max_right M (K.max' hKnonempty + 1)
    exact
      lt_of_le_of_lt hxmax
        (lt_of_lt_of_le (Nat.lt_succ_self _)
          (hmaxBase.trans hBasem))
  refine ⟨m, hlower, ?_⟩
  rw [Finset.nonempty_iff_ne_empty]
  intro hadmEmpty
  let excluded :=
    sure ∪ pastOutputs ∪ O.replayWitnesses sure pastOutputs t m
  have hprefixSub :
      O.finitePrefix n m ⊆ excluded := by
    intro x hx
    by_contra hxexcluded
    have hxadm :
        x ∈ O.replayAdmissible sure pastOutputs t m hactive := by
      rw [O.mem_replayAdmissible]
      have hxprefix := O.mem_finitePrefix.mp hx
      have hxparts :
          x ∉ sure ∧ x ∉ pastOutputs ∧
            x ∉ O.replayWitnesses sure pastOutputs t m := by
        simpa [excluded] using hxexcluded
      simpa [hselected] using
        ⟨hxprefix.1, hxprefix.2, hxparts⟩
    rw [hadmEmpty] at hxadm
    exact Finset.notMem_empty x hxadm
  have hKexcluded : K ⊆ excluded :=
    fun _ hx => hprefixSub (hKprefix hx)
  have hExcludedCard :
      excluded.card ≤ B := by
    calc
      excluded.card
          ≤ (sure ∪ pastOutputs).card +
              (O.replayWitnesses sure pastOutputs t m).card :=
        Finset.card_union_le _ _
      _ ≤ (sure.card + pastOutputs.card) +
              ((O.replayActive sure t).card *
                (O.replayActive sure t).card) := by
        exact Nat.add_le_add
          (Finset.card_union_le _ _)
          (O.replayWitnesses_card_le sure pastOutputs t m)
      _ = B := by
        simp [B, Nat.add_assoc]
  have hKle : K.card ≤ excluded.card :=
    Finset.card_le_card hKexcluded
  have : B + 1 ≤ B := by
    rw [← hKcard]
    exact hKle.trans hExcludedCard
  omega

/-- The first terminating cutoff at or above `lower`. -/
def replayCarriedRoundCutoff
    (sure pastOutputs : Finset ℕ) (t lower : ℕ)
    (hactive : O.HasReplayActive sure t) : ℕ :=
  Nat.find (O.replayAdmissible_eventually_nonempty_from
    (pastOutputs := pastOutputs) hactive lower)

theorem replayCarriedRoundCutoff_spec
    {sure pastOutputs : Finset ℕ} {t lower : ℕ}
    (hactive : O.HasReplayActive sure t) :
    lower ≤ O.replayCarriedRoundCutoff
        sure pastOutputs t lower hactive ∧
      (O.replayAdmissible sure pastOutputs t
        (O.replayCarriedRoundCutoff
          sure pastOutputs t lower hactive)
        hactive).Nonempty := by
  exact Nat.find_spec
    (O.replayAdmissible_eventually_nonempty_from
      (pastOutputs := pastOutputs) hactive lower)

/-- The first admissible output at the first terminating cutoff no smaller
than the carried lower bound. -/
def replayCarriedRoundOutput
    (sure pastOutputs : Finset ℕ) (t lower : ℕ)
    (hactive : O.HasReplayActive sure t) : ℕ :=
  let m :=
    O.replayCarriedRoundCutoff sure pastOutputs t lower hactive
  (O.replayAdmissible sure pastOutputs t m hactive).min'
    (O.replayCarriedRoundCutoff_spec hactive).2

/-- Complete source-facing certificate for one carried-cutoff round. -/
theorem replayCarriedRoundOutput_spec
    {sure pastOutputs : Finset ℕ} {t lower : ℕ}
    (hactive : O.HasReplayActive sure t) :
    let m :=
      O.replayCarriedRoundCutoff sure pastOutputs t lower hactive
    let n := O.replaySelected sure pastOutputs t m hactive
    lower ≤ m ∧
      O.ReplayFinitelyCriticalAt sure pastOutputs m n ∧
      (∀ i, i < t →
        O.ReplayFinitelyCriticalAt sure pastOutputs m i →
          i ≤ n) ∧
      O.replayCarriedRoundOutput
          sure pastOutputs t lower hactive < m ∧
      O.replayCarriedRoundOutput
          sure pastOutputs t lower hactive ∈ O.language n ∧
      O.replayCarriedRoundOutput
          sure pastOutputs t lower hactive ∉ sure ∧
      O.replayCarriedRoundOutput
          sure pastOutputs t lower hactive ∉ pastOutputs ∧
      O.replayCarriedRoundOutput
          sure pastOutputs t lower hactive ∉
            O.replayWitnesses sure pastOutputs t m := by
  dsimp only
  let m :=
    O.replayCarriedRoundCutoff sure pastOutputs t lower hactive
  let n := O.replaySelected sure pastOutputs t m hactive
  have hout :
      O.replayCarriedRoundOutput sure pastOutputs t lower hactive ∈
        O.replayAdmissible sure pastOutputs t m hactive := by
    exact Finset.min'_mem _
      (O.replayCarriedRoundCutoff_spec hactive).2
  have hout' := O.mem_replayAdmissible.mp hout
  refine
    ⟨(O.replayCarriedRoundCutoff_spec hactive).1,
      O.replaySelected_critical hactive, ?_, hout'.1,
      hout'.2.1, hout'.2.2.1, hout'.2.2.2.1,
      hout'.2.2.2.2⟩
  intro i hit hi
  exact O.replaySelected_max hactive hit hi

theorem replayCarriedRoundOutput_mem_of_targetCritical
    {sure pastOutputs : Finset ℕ} {t lower z : ℕ}
    (hactive : O.HasReplayActive sure t)
    (hzt : z < t)
    (hzcritical :
      O.ReplayFinitelyCriticalAt sure pastOutputs
        (O.replayCarriedRoundCutoff
          sure pastOutputs t lower hactive) z) :
    O.replayCarriedRoundOutput
        sure pastOutputs t lower hactive ∈ O.language z := by
  let m :=
    O.replayCarriedRoundCutoff sure pastOutputs t lower hactive
  let n := O.replaySelected sure pastOutputs t m hactive
  have hspec :=
    O.replayCarriedRoundOutput_spec
      (lower := lower) (pastOutputs := pastOutputs) hactive
  dsimp only at hspec
  rcases hspec with
    ⟨_hlower, hncritical, hmax, houtlt, houtn, _houtSure,
      houtPast, _houtWitness⟩
  have hzn : z ≤ n := hmax z hzt hzcritical
  rcases eq_or_lt_of_le hzn with hznEq | hznLt
  · simpa [hznEq] using houtn
  · have hsemantic :=
      O.replayFinitelyCriticalAt_iff.mp hncritical
    exact hsemantic.2 z hznLt
      (O.replayFinitelyCriticalAt_iff.mp hzcritical).1
      (O.replayCarriedRoundOutput
        sure pastOutputs t lower hactive)
      houtlt houtn houtPast

theorem replayCarriedRoundOutput_fresh
    {sure pastOutputs : Finset ℕ} {t lower : ℕ}
    (hactive : O.HasReplayActive sure t) :
    O.replayCarriedRoundOutput
        sure pastOutputs t lower hactive ∉ sure ∧
      O.replayCarriedRoundOutput
        sure pastOutputs t lower hactive ∉ pastOutputs := by
  have hspec :=
    O.replayCarriedRoundOutput_spec
      (lower := lower) (pastOutputs := pastOutputs) hactive
  dsimp only at hspec
  exact
    ⟨hspec.2.2.2.2.2.1,
      hspec.2.2.2.2.2.2.1⟩

/-- The protected-witness argument is unchanged when the search starts from
a carried lower bound. -/
theorem replayCarriedRoundOutput_ne_leastDifference
    {sure pastOutputs : Finset ℕ} {t lower i j w : ℕ}
    (hactive : O.HasReplayActive sure t)
    (hiActive : i ∈ O.replayActive sure t)
    (hjActive : j ∈ O.replayActive sure t)
    (hji : j < i)
    (hwi : w ∈ O.language i)
    (hwj : w ∉ O.language j)
    (hwout : w ∉ pastOutputs)
    (hleast :
      ∀ x, x < w → x ∈ O.language i →
        x ∉ O.language j → x ∉ pastOutputs → False) :
    O.replayCarriedRoundOutput
        sure pastOutputs t lower hactive ≠ w := by
  let m :=
    O.replayCarriedRoundCutoff sure pastOutputs t lower hactive
  have hspec :=
    O.replayCarriedRoundOutput_spec
      (lower := lower) (pastOutputs := pastOutputs) hactive
  dsimp only at hspec
  by_cases hwm : w < m
  · have hwDiff :
        w ∈ O.replayDifferencePrefix pastOutputs i j m :=
      O.mem_replayDifferencePrefix.mpr
        ⟨hwm, hwi, hwj, hwout⟩
    have hdiff :
        (O.replayDifferencePrefix pastOutputs i j m).Nonempty :=
      ⟨w, hwDiff⟩
    have hwitness :
        O.replayWitnessValue pastOutputs i j m = w := by
      rw [replayWitnessValue, dif_pos hdiff]
      apply Nat.le_antisymm
      · exact Finset.min'_le _ w hwDiff
      · apply Nat.le_of_not_gt
        intro hminlt
        have hminMem :=
          Finset.min'_mem
            (O.replayDifferencePrefix pastOutputs i j m) hdiff
        have hparts :=
          O.mem_replayDifferencePrefix.mp hminMem
        exact hleast _ hminlt hparts.2.1
          hparts.2.2.1 hparts.2.2.2
    have hpair :
        (i, j) ∈ O.replayActivePairs sure t := by
      simp [replayActivePairs, hiActive, hjActive, hji]
    have hwW :
        w ∈ O.replayWitnesses sure pastOutputs t m := by
      apply Finset.mem_image.mpr
      refine ⟨(i, j), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hpair, hdiff⟩
      · simpa using hwitness
    intro hout
    exact hspec.2.2.2.2.2.2.2 (hout ▸ hwW)
  · intro hout
    have houtlt := hspec.2.2.2.1
    have hmw : m ≤ w := Nat.le_of_not_gt hwm
    rw [hout] at houtlt
    exact (Nat.not_lt_of_ge hmw) houtlt

/-! ## Literal persistent state -/

structure CarriedWitnessProtectionState where
  sure : Finset ℕ
  pastOutputs : Finset ℕ
  cutoff : ℕ
  output : ℕ

def carriedWitnessProtectionInitial :
    CarriedWitnessProtectionState :=
  ⟨∅, ∅, 0, 0⟩

/-- Zero-based translation of lines 12--14 of Algorithm 2.  Source element
`q ≥ 1` is encoded by `q - 1`; hence moving the one-based cutoff past `q`
means first reaching `x + 1`, followed by the repeat-loop increment. -/
def replayCarriedStart
    (state : CarriedWitnessProtectionState) (x : ℕ) : ℕ :=
  max state.cutoff (x + 1) + 1

/-- One executable literal carried-cutoff transition of Algorithm 2. -/
def carriedWitnessProtectionProcessRound
    (state : CarriedWitnessProtectionState) (x t : ℕ) :
    CarriedWitnessProtectionState :=
  let sure :=
    witnessProtectionSureUpdate
      ⟨state.sure, state.pastOutputs, state.output⟩ x
  if hactive : O.HasReplayActive sure t then
    let lower := replayCarriedStart state x
    let cutoff :=
      O.replayCarriedRoundCutoff
        sure state.pastOutputs t lower hactive
    let out :=
      O.replayCarriedRoundOutput
        sure state.pastOutputs t lower hactive
    ⟨sure, insert out state.pastOutputs, cutoff, out⟩
  else
    let out := witnessProtectionFallback sure
    ⟨sure, insert out state.pastOutputs, state.cutoff, out⟩

theorem carriedWitnessProtectionProcessRound_of_active
    (state : CarriedWitnessProtectionState) (x t : ℕ)
    (hactive :
      O.HasReplayActive
        (witnessProtectionSureUpdate
          ⟨state.sure, state.pastOutputs, state.output⟩ x) t) :
    O.carriedWitnessProtectionProcessRound state x t =
      let sure :=
        witnessProtectionSureUpdate
          ⟨state.sure, state.pastOutputs, state.output⟩ x
      let lower := replayCarriedStart state x
      let cutoff :=
        O.replayCarriedRoundCutoff
          sure state.pastOutputs t lower hactive
      let out :=
        O.replayCarriedRoundOutput
          sure state.pastOutputs t lower hactive
      ⟨sure, insert out state.pastOutputs, cutoff, out⟩ := by
  simp [carriedWitnessProtectionProcessRound, hactive]

theorem carriedWitnessProtectionProcessRound_sure
    (state : CarriedWitnessProtectionState) (x t : ℕ) :
    (O.carriedWitnessProtectionProcessRound state x t).sure =
      witnessProtectionSureUpdate
        ⟨state.sure, state.pastOutputs, state.output⟩ x := by
  unfold carriedWitnessProtectionProcessRound
  dsimp only
  split <;> rfl

theorem carriedWitnessProtectionProcessRound_pastOutputs
    (state : CarriedWitnessProtectionState) (x t : ℕ) :
    (O.carriedWitnessProtectionProcessRound state x t).pastOutputs =
      insert (O.carriedWitnessProtectionProcessRound state x t).output
        state.pastOutputs := by
  simp [carriedWitnessProtectionProcessRound]
  split <;> rfl

theorem carriedWitnessProtectionProcessRound_cutoff_mono
    (state : CarriedWitnessProtectionState) (x t : ℕ) :
    state.cutoff ≤
      (O.carriedWitnessProtectionProcessRound state x t).cutoff := by
  unfold carriedWitnessProtectionProcessRound
  dsimp only
  split
  · rename_i hactive
    calc
      state.cutoff ≤ max state.cutoff (x + 1) :=
        Nat.le_max_left _ _
      _ ≤ max state.cutoff (x + 1) + 1 :=
        Nat.le_succ _
      _ ≤ O.replayCarriedRoundCutoff
          (witnessProtectionSureUpdate
            ⟨state.sure, state.pastOutputs, state.output⟩ x)
          state.pastOutputs t (replayCarriedStart state x)
          hactive :=
        O.replayCarriedRoundCutoff_spec hactive |>.1
  · exact le_rfl

theorem carriedWitnessProtectionProcessRound_cutoff_gt_input_of_active
    (state : CarriedWitnessProtectionState) (x t : ℕ)
    (hactive :
      O.HasReplayActive
        (witnessProtectionSureUpdate
          ⟨state.sure, state.pastOutputs, state.output⟩ x) t) :
    x <
      (O.carriedWitnessProtectionProcessRound state x t).cutoff := by
  rw [O.carriedWitnessProtectionProcessRound_of_active
    state x t hactive]
  calc
    x < x + 1 := Nat.lt_succ_self x
    _ ≤ max state.cutoff (x + 1) := Nat.le_max_right _ _
    _ ≤ max state.cutoff (x + 1) + 1 := Nat.le_succ _
    _ ≤ O.replayCarriedRoundCutoff
        (witnessProtectionSureUpdate
          ⟨state.sure, state.pastOutputs, state.output⟩ x)
        state.pastOutputs t (replayCarriedStart state x)
        hactive :=
      O.replayCarriedRoundCutoff_spec hactive |>.1

/-- Persistent execution of the literal carried-cutoff state transition. -/
def carriedWitnessProtectionRun
    (O : GenLimit.OracleFamily)
    (stream : ℕ → ℕ) : ℕ → CarriedWitnessProtectionState
  | 0 => carriedWitnessProtectionInitial
  | t + 1 =>
      O.carriedWitnessProtectionProcessRound
        (carriedWitnessProtectionRun O stream t) (stream t) (t + 1)

@[simp] theorem carriedWitnessProtectionRun_zero
    (stream : ℕ → ℕ) :
    O.carriedWitnessProtectionRun stream 0 =
      carriedWitnessProtectionInitial := rfl

@[simp] theorem carriedWitnessProtectionRun_succ
    (stream : ℕ → ℕ) (t : ℕ) :
    O.carriedWitnessProtectionRun stream (t + 1) =
      O.carriedWitnessProtectionProcessRound
        (O.carriedWitnessProtectionRun stream t) (stream t) (t + 1) :=
  rfl

theorem carriedWitnessProtectionRun_cutoff_mono
    (stream : ℕ → ℕ) (t : ℕ) :
    (O.carriedWitnessProtectionRun stream t).cutoff ≤
      (O.carriedWitnessProtectionRun stream (t + 1)).cutoff := by
  rw [O.carriedWitnessProtectionRun_succ]
  exact
    O.carriedWitnessProtectionProcessRound_cutoff_mono
      (O.carriedWitnessProtectionRun stream t) (stream t) (t + 1)

theorem carriedWitnessProtectionRun_congr
    {stream₁ stream₂ : ℕ → ℕ} :
    ∀ {t}, (∀ k, k < t → stream₁ k = stream₂ k) →
      O.carriedWitnessProtectionRun stream₁ t =
        O.carriedWitnessProtectionRun stream₂ t := by
  intro t hprefix
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [O.carriedWitnessProtectionRun_succ,
        O.carriedWitnessProtectionRun_succ,
        ih (fun k hk => hprefix k (Nat.lt.step hk)),
        hprefix t (Nat.lt_add_one t)]

/-- The executable literal carried-cutoff machine as a causal generator. -/
def carriedWitnessProtectionGenerator :
    Generic.Generator ℕ :=
  fun t history =>
    (O.carriedWitnessProtectionRun
      (witnessProtectionPrefixStream history) t).output

theorem output_carriedWitnessProtectionGenerator
    (stream : ℕ → ℕ) (t : ℕ) :
    Generic.output O.carriedWitnessProtectionGenerator stream t =
      (O.carriedWitnessProtectionRun stream t).output := by
  apply congrArg CarriedWitnessProtectionState.output
  apply O.carriedWitnessProtectionRun_congr
  intro k hk
  simp [witnessProtectionPrefixStream, hk]

/-- Active-round output equation, including the source's carried lower
bound. -/
theorem carriedWitnessProtectionRun_succ_output_of_active
    (stream : ℕ → ℕ) (t : ℕ)
    (hactive :
      O.HasReplayActive
        (witnessProtectionSureUpdate
          ⟨(O.carriedWitnessProtectionRun stream t).sure,
            (O.carriedWitnessProtectionRun stream t).pastOutputs,
            (O.carriedWitnessProtectionRun stream t).output⟩
          (stream t)) (t + 1)) :
    (O.carriedWitnessProtectionRun stream (t + 1)).output =
      O.replayCarriedRoundOutput
        (witnessProtectionSureUpdate
          ⟨(O.carriedWitnessProtectionRun stream t).sure,
            (O.carriedWitnessProtectionRun stream t).pastOutputs,
            (O.carriedWitnessProtectionRun stream t).output⟩
          (stream t))
        (O.carriedWitnessProtectionRun stream t).pastOutputs
        (t + 1)
        (replayCarriedStart
          (O.carriedWitnessProtectionRun stream t) (stream t))
        hactive := by
  rw [O.carriedWitnessProtectionRun_succ,
    O.carriedWitnessProtectionProcessRound_of_active
      (O.carriedWitnessProtectionRun stream t)
      (stream t) (t + 1) hactive]

theorem carriedWitnessProtectionRun_sure_mono
    (stream : ℕ → ℕ) (t : ℕ) :
    (O.carriedWitnessProtectionRun stream t).sure ⊆
      (O.carriedWitnessProtectionRun stream (t + 1)).sure := by
  rw [O.carriedWitnessProtectionRun_succ,
    O.carriedWitnessProtectionProcessRound_sure]
  exact witnessProtectionSureUpdate_mono
    ⟨(O.carriedWitnessProtectionRun stream t).sure,
      (O.carriedWitnessProtectionRun stream t).pastOutputs,
      (O.carriedWitnessProtectionRun stream t).output⟩
    (stream t)

theorem carriedWitnessProtectionRun_pastOutputs_mono
    (stream : ℕ → ℕ) (t : ℕ) :
    (O.carriedWitnessProtectionRun stream t).pastOutputs ⊆
      (O.carriedWitnessProtectionRun stream (t + 1)).pastOutputs := by
  rw [O.carriedWitnessProtectionRun_succ,
    O.carriedWitnessProtectionProcessRound_pastOutputs]
  exact Finset.subset_insert _ _

theorem carriedWitnessProtectionRun_sure_mono_of_le
    (stream : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    (O.carriedWitnessProtectionRun stream s).sure ⊆
      (O.carriedWitnessProtectionRun stream t).sure := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t _ ih =>
      exact ih.trans
        (O.carriedWitnessProtectionRun_sure_mono stream t)

theorem carriedWitnessProtectionRun_pastOutputs_mono_of_le
    (stream : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    (O.carriedWitnessProtectionRun stream s).pastOutputs ⊆
      (O.carriedWitnessProtectionRun stream t).pastOutputs := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t _ ih =>
      exact ih.trans
        (O.carriedWitnessProtectionRun_pastOutputs_mono stream t)

theorem carriedWitnessProtectionRun_output_mem
    (stream : ℕ → ℕ) {t : ℕ} (ht : 0 < t) :
    (O.carriedWitnessProtectionRun stream t).output ∈
      (O.carriedWitnessProtectionRun stream t).pastOutputs := by
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [O.carriedWitnessProtectionRun_succ,
    O.carriedWitnessProtectionProcessRound_pastOutputs]
  exact Finset.mem_insert_self _ _

theorem carriedWitnessProtection_output_mem_pastOutputs
    (stream : ℕ → ℕ) {k t : ℕ}
    (hk : 0 < k) (hkt : k ≤ t) :
    Generic.output O.carriedWitnessProtectionGenerator stream k ∈
      (O.carriedWitnessProtectionRun stream t).pastOutputs := by
  rw [O.output_carriedWitnessProtectionGenerator]
  exact
    O.carriedWitnessProtectionRun_pastOutputs_mono_of_le stream hkt
      (O.carriedWitnessProtectionRun_output_mem stream hk)

/-! ## Replay invariants and correctness of the literal machine -/

theorem carriedWitnessProtectionRun_sure_subset_target
    {z : ℕ} {stream : ℕ → ℕ}
    (hreplay :
      IsReplaySequence O.carriedWitnessProtectionGenerator
        (O.language z) stream) :
    ∀ t, (↑(O.carriedWitnessProtectionRun stream t).sure : Set ℕ) ⊆
      O.language z := by
  intro t
  induction t with
  | zero =>
      simp [carriedWitnessProtectionRun,
        carriedWitnessProtectionInitial]
  | succ t ih =>
      rw [O.carriedWitnessProtectionRun_succ,
        O.carriedWitnessProtectionProcessRound_sure]
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
            exact
              O.carriedWitnessProtection_output_mem_pastOutputs
                stream hkpos hkt
        · exact ih (by simpa using hy)

theorem carriedWitnessProtection_target_active
    {z t : ℕ} {stream : ℕ → ℕ}
    (hreplay :
      IsReplaySequence O.carriedWitnessProtectionGenerator
        (O.language z) stream)
    (hzt : z < t) :
    O.HasReplayActive
      (O.carriedWitnessProtectionRun stream t).sure t := by
  refine ⟨z, O.mem_replayActive.mpr ⟨hzt, ?_⟩⟩
  apply O.replayConsistentAt_iff.mpr
  exact O.carriedWitnessProtectionRun_sure_subset_target hreplay t

/-- One carried-cutoff induction step for the fixed protected witness from
Lemma 6.3. -/
theorem carriedWitnessProtectionRun_succ_protects_witness
    {z j r : ℕ} {stream : ℕ → ℕ}
    {basePast : Finset ℕ}
    (hreplay :
      IsReplaySequence O.carriedWitnessProtectionGenerator
        (O.language z) stream)
    (hzr : z < r + 1)
    (hjz : j < z)
    (hjconsistent :
      O.ReplayConsistentAt
        (O.carriedWitnessProtectionRun stream (r + 1)).sure j)
    (hbase :
      basePast ⊆
        (O.carriedWitnessProtectionRun stream r).pastOutputs)
    (hdiff : O.HasReplayDifference basePast z j)
    (hwPast :
      O.replayLeastDifference basePast z j ∉
        (O.carriedWitnessProtectionRun stream r).pastOutputs) :
    O.replayLeastDifference basePast z j ∉
      (O.carriedWitnessProtectionRun stream (r + 1)).pastOutputs := by
  let previous := O.carriedWitnessProtectionRun stream r
  let previousCore : WitnessProtectionState :=
    ⟨previous.sure, previous.pastOutputs, previous.output⟩
  let sure :=
    witnessProtectionSureUpdate previousCore (stream r)
  let lower := replayCarriedStart previous (stream r)
  let w := O.replayLeastDifference basePast z j
  have hsureEq :
      sure = (O.carriedWitnessProtectionRun stream (r + 1)).sure := by
    rw [O.carriedWitnessProtectionRun_succ,
      O.carriedWitnessProtectionProcessRound_sure]
  have hzCons : O.ReplayConsistentAt sure z := by
    apply O.replayConsistentAt_iff.mpr
    intro x hx
    apply
      O.carriedWitnessProtectionRun_sure_subset_target hreplay (r + 1)
    have hmemEq :
        (x ∈ sure) =
          (x ∈
            (O.carriedWitnessProtectionRun stream (r + 1)).sure) :=
      congrArg (fun S : Finset ℕ => x ∈ S) hsureEq
    exact hmemEq.mp hx
  have hactive : O.HasReplayActive sure (r + 1) :=
    ⟨z, O.mem_replayActive.mpr ⟨hzr, hzCons⟩⟩
  have hzActive : z ∈ O.replayActive sure (r + 1) :=
    O.mem_replayActive.mpr ⟨hzr, hzCons⟩
  have hjr : j < r + 1 := lt_trans hjz hzr
  have hjConsSure : O.ReplayConsistentAt sure j := by
    apply O.replayConsistentAt_iff.mpr
    intro x hx
    apply O.replayConsistentAt_iff.mp hjconsistent
    have hmemEq :
        (x ∈ sure) =
          (x ∈
            (O.carriedWitnessProtectionRun stream (r + 1)).sure) :=
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
      O.replayCarriedRoundOutput sure previous.pastOutputs
        (r + 1) lower hactive ≠ w := by
    exact O.replayCarriedRoundOutput_ne_leastDifference
      hactive hzActive hjActive hjz
      hwSpec.1 hwSpec.2.1 hwPast hleastCurrent
  have houtEq :
      (O.carriedWitnessProtectionRun stream (r + 1)).output =
        O.replayCarriedRoundOutput sure previous.pastOutputs
          (r + 1) lower hactive := by
    exact
      O.carriedWitnessProtectionRun_succ_output_of_active
        stream r hactive
  rw [O.carriedWitnessProtectionRun_succ,
    O.carriedWitnessProtectionProcessRound_pastOutputs]
  simp only [Finset.mem_insert, not_or]
  refine ⟨?_, hwPast⟩
  intro hwEq
  apply hroundNe
  rw [← houtEq]
  simpa [previous] using hwEq.symm

theorem carriedWitnessProtection_leastDifference_protected
    {z j : ℕ} {stream : ℕ → ℕ}
    (hreplay :
      IsReplaySequence O.carriedWitnessProtectionGenerator
        (O.language z) stream)
    (hjz : j < z)
    (hdiff :
      O.HasReplayDifference
        (O.carriedWitnessProtectionRun stream z).pastOutputs z j) :
    ∀ t, z + 1 ≤ t →
      O.ReplayConsistentAt
        (O.carriedWitnessProtectionRun stream t).sure j →
      O.replayLeastDifference
          (O.carriedWitnessProtectionRun stream z).pastOutputs z j ∉
        (O.carriedWitnessProtectionRun stream t).pastOutputs := by
  intro t hzt
  induction t, hzt using Nat.le_induction with
  | base =>
      intro hjconsistent
      apply O.carriedWitnessProtectionRun_succ_protects_witness
        hreplay (Nat.lt_succ_self z) hjz hjconsistent
        Finset.Subset.rfl hdiff
      exact (O.replayLeastDifference_spec hdiff).2.2
  | succ t hzt ih =>
      intro hjconsistent
      have hjPrevious :
          O.ReplayConsistentAt
            (O.carriedWitnessProtectionRun stream t).sure j := by
        exact O.replayConsistentAt_mono
          (O.carriedWitnessProtectionRun_sure_mono stream t)
          hjconsistent
      have hwPrevious := ih hjPrevious
      apply O.carriedWitnessProtectionRun_succ_protects_witness
        hreplay
        (Nat.lt.step
          (lt_of_lt_of_le (Nat.lt_succ_self z) hzt))
        hjz hjconsistent
        (O.carriedWitnessProtectionRun_pastOutputs_mono_of_le
          stream (Nat.le_of_succ_le hzt))
        hdiff hwPrevious

theorem carriedWitnessProtection_difference_eventually_inconsistent
    {z j : ℕ} {stream : ℕ → ℕ}
    (henum :
      IsReplayEnumeration O.carriedWitnessProtectionGenerator
        (O.language z) stream)
    (hjz : j < z)
    (hdiff :
      O.HasReplayDifference
        (O.carriedWitnessProtectionRun stream z).pastOutputs z j) :
    ∃ T, ∀ t, T ≤ t →
      ¬O.ReplayConsistentAt
        (O.carriedWitnessProtectionRun stream t).sure j := by
  let basePast :=
    (O.carriedWitnessProtectionRun stream z).pastOutputs
  let w := O.replayLeastDifference basePast z j
  have hwSpec := O.replayLeastDifference_spec hdiff
  obtain ⟨n, hn⟩ := henum.2 w hwSpec.1
  let T := max (z + 1) (n + 1)
  refine ⟨T, ?_⟩
  intro t hTt hjconsistent
  have hnT : n + 1 ≤ T := Nat.le_max_right _ _
  have hnt : n ≤ t :=
    Nat.le_trans (Nat.le_succ n) (hnT.trans hTt)
  have hwNotPast :
      w ∉ (O.carriedWitnessProtectionRun stream n).pastOutputs := by
    by_cases hnz : n ≤ z
    · intro hwPastN
      exact hwSpec.2.2
        (O.carriedWitnessProtectionRun_pastOutputs_mono_of_le
          stream hnz hwPastN)
    · have hzn : z + 1 ≤ n := by omega
      have hjconsistentN :
          O.ReplayConsistentAt
            (O.carriedWitnessProtectionRun stream n).sure j := by
        exact O.replayConsistentAt_mono
          (O.carriedWitnessProtectionRun_sure_mono_of_le
            stream hnt)
          hjconsistent
      exact O.carriedWitnessProtection_leastDifference_protected
        henum.1 hjz hdiff n hzn hjconsistentN
  have hwSureNext :
      w ∈ (O.carriedWitnessProtectionRun stream (n + 1)).sure := by
    rw [O.carriedWitnessProtectionRun_succ,
      O.carriedWitnessProtectionProcessRound_sure]
    simp [witnessProtectionSureUpdate, hn, hwNotPast]
  have hwSure :
      w ∈ (O.carriedWitnessProtectionRun stream t).sure := by
    exact O.carriedWitnessProtectionRun_sure_mono_of_le
      stream (hnT.trans hTt) hwSureNext
  have hwj : w ∈ O.language j :=
    O.replayConsistentAt_iff.mp hjconsistent
      (by simpa using hwSure)
  exact hwSpec.2.1 hwj

/-- Lemma 6.3 for the literal carried-cutoff execution. -/
theorem carriedWitnessProtection_target_eventually_critical
    {z : ℕ} {stream : ℕ → ℕ}
    (henum :
      IsReplayEnumeration O.carriedWitnessProtectionGenerator
        (O.language z) stream) :
    ∃ T, ∀ t, T ≤ t →
      O.ReplayCriticalAt
        (O.carriedWitnessProtectionRun stream t).sure
        (O.carriedWitnessProtectionRun stream (t - 1)).pastOutputs z := by
  classical
  let basePast :=
    (O.carriedWitnessProtectionRun stream z).pastOutputs
  let P : ℕ → ℕ → Prop :=
    fun j t =>
      O.ReplayConsistentAt
          (O.carriedWitnessProtectionRun stream t).sure j →
        ∀ x, x ∈ O.language z →
          x ∉
            (O.carriedWitnessProtectionRun
              stream (t - 1)).pastOutputs →
          x ∈ O.language j
  have hEach :
      ∀ j ∈ Finset.range z, ∃ T, ∀ t, T ≤ t → P j t := by
    intro j hj
    have hjz : j < z := Finset.mem_range.mp hj
    by_cases hdiff : O.HasReplayDifference basePast z j
    · obtain ⟨Tj, hTj⟩ :=
        O.carriedWitnessProtection_difference_eventually_inconsistent
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
      apply
        O.carriedWitnessProtectionRun_pastOutputs_mono_of_le stream
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
      ∃ T, ∀ t, T ≤ t → ∀ j ∈ Finset.range z, P j t :=
    finiteEventually (Finset.range z) hEach
  obtain ⟨T₀, hT₀⟩ := hAll
  refine ⟨max (z + 1) T₀, ?_⟩
  intro t ht
  have hT₀t : T₀ ≤ t :=
    (Nat.le_max_right (z + 1) T₀).trans ht
  refine ⟨?_, ?_⟩
  · apply O.replayConsistentAt_iff.mpr
    exact
      O.carriedWitnessProtectionRun_sure_subset_target henum.1 t
  · intro j hjz hjconsistent x hxz hxPast
    exact hT₀ t hT₀t j (Finset.mem_range.mpr hjz)
      hjconsistent x hxz hxPast

theorem carriedWitnessProtection_sample_covered :
    ∀ (stream : ℕ → ℕ) {t : ℕ}, 0 < t →
      Generic.sample stream t ⊆
        (O.carriedWitnessProtectionRun stream t).sure ∪
          (O.carriedWitnessProtectionRun
            stream (t - 1)).pastOutputs := by
  intro stream t ht x hx
  obtain ⟨s, hst, rfl⟩ := Generic.mem_sample_iff.mp hx
  have hsle : s + 1 ≤ t := Nat.succ_le_iff.mpr hst
  by_cases hout :
      stream s ∈
        (O.carriedWitnessProtectionRun stream s).pastOutputs
  · apply Finset.mem_union_right
    apply
      O.carriedWitnessProtectionRun_pastOutputs_mono_of_le stream
    · exact Nat.le_sub_one_of_lt hst
    · exact hout
  · apply Finset.mem_union_left
    apply O.carriedWitnessProtectionRun_sure_mono_of_le stream hsle
    rw [O.carriedWitnessProtectionRun_succ,
      O.carriedWitnessProtectionProcessRound_sure]
    simp [witnessProtectionSureUpdate, hout]

set_option maxHeartbeats 800000 in
theorem carriedWitnessProtection_output_fresh
    {z t : ℕ} {stream : ℕ → ℕ}
    (hreplay :
      IsReplaySequence O.carriedWitnessProtectionGenerator
        (O.language z) stream)
    (hzt : z < t) :
    Generic.output O.carriedWitnessProtectionGenerator stream t ∉
      Generic.sample stream t := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le z) hzt
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  let previous := O.carriedWitnessProtectionRun stream s
  let previousCore : WitnessProtectionState :=
    ⟨previous.sure, previous.pastOutputs, previous.output⟩
  let sure :=
    witnessProtectionSureUpdate previousCore (stream s)
  let lower := replayCarriedStart previous (stream s)
  have hsure :
      sure =
        (O.carriedWitnessProtectionRun stream (s + 1)).sure := by
    simp [sure, previous, previousCore,
      O.carriedWitnessProtectionProcessRound_sure]
  have hactive :
      O.HasReplayActive sure (s + 1) := by
    rw [hsure]
    exact O.carriedWitnessProtection_target_active hreplay hzt
  have hfresh :=
    O.replayCarriedRoundOutput_fresh
      (lower := lower) (pastOutputs := previous.pastOutputs) hactive
  have houtEq :
      Generic.output O.carriedWitnessProtectionGenerator
          stream (s + 1) =
        O.replayCarriedRoundOutput sure previous.pastOutputs
          (s + 1) lower hactive := by
    rw [O.output_carriedWitnessProtectionGenerator]
    exact
      O.carriedWitnessProtectionRun_succ_output_of_active
        stream s hactive
  rw [houtEq]
  intro houtSample
  have hcovered :=
    O.carriedWitnessProtection_sample_covered stream
      (t := s + 1) (Nat.zero_lt_succ s) houtSample
  rcases Finset.mem_union.mp hcovered with houtSure | houtPast
  · apply hfresh.1
    let out :=
      O.replayCarriedRoundOutput sure previous.pastOutputs
        (s + 1) lower hactive
    have hmemEq :
        (out ∈ sure) =
          (out ∈
            (O.carriedWitnessProtectionRun stream (s + 1)).sure) :=
      congrArg (fun S : Finset ℕ => out ∈ S) hsure
    exact hmemEq.mpr houtSure
  · exact hfresh.2 (by simpa [previous] using houtPast)

/-- Lemma 6.5 for the literal persistent-cutoff machine. -/
theorem carriedWitnessProtection_eventual_correctness
    {z : ℕ} {stream : ℕ → ℕ}
    (henum :
      IsReplayEnumeration O.carriedWitnessProtectionGenerator
        (O.language z) stream) :
    ∃ T, ∀ t, T ≤ t →
      Generic.CorrectAt O.carriedWitnessProtectionGenerator
        (O.language z) stream t := by
  obtain ⟨Tcritical, hcritical⟩ :=
    O.carriedWitnessProtection_target_eventually_critical henum
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
  let previous := O.carriedWitnessProtectionRun stream s
  let previousCore : WitnessProtectionState :=
    ⟨previous.sure, previous.pastOutputs, previous.output⟩
  let sure :=
    witnessProtectionSureUpdate previousCore (stream s)
  let lower := replayCarriedStart previous (stream s)
  have hsureEq :
      sure =
        (O.carriedWitnessProtectionRun stream (s + 1)).sure := by
    rw [O.carriedWitnessProtectionRun_succ,
      O.carriedWitnessProtectionProcessRound_sure]
  have hcritical' :
      O.ReplayCriticalAt sure previous.pastOutputs z := by
    have hsource := hcritical (s + 1) hTcritical
    simpa [previous, hsureEq] using hsource
  have hactive : O.HasReplayActive sure (s + 1) :=
    ⟨z, O.mem_replayActive.mpr ⟨hzt, hcritical'.1⟩⟩
  let m :=
    O.replayCarriedRoundCutoff
      sure previous.pastOutputs (s + 1) lower hactive
  have hzfinite :
      O.ReplayFinitelyCriticalAt sure previous.pastOutputs m z :=
    O.replayCriticalAt_finitelyCriticalAt hcritical' m
  have houtTarget :
      O.replayCarriedRoundOutput sure previous.pastOutputs
          (s + 1) lower hactive ∈ O.language z := by
    exact O.replayCarriedRoundOutput_mem_of_targetCritical
      hactive hzt hzfinite
  have houtEq :
      Generic.output O.carriedWitnessProtectionGenerator
          stream (s + 1) =
        O.replayCarriedRoundOutput sure previous.pastOutputs
          (s + 1) lower hactive := by
    rw [O.output_carriedWitnessProtectionGenerator]
    exact
      O.carriedWitnessProtectionRun_succ_output_of_active
        stream s hactive
  refine
    ⟨?_,
      O.carriedWitnessProtection_output_fresh henum.1 hzt⟩
  rw [houtEq]
  exact houtTarget

/-- Theorem 6.1's full semantic conclusion for the source's literal
persistent-cutoff Algorithm 2 on the normalized natural-number domain. -/
theorem theorem_6_1_carried :
    IsLimitReplayGenerator O.carriedWitnessProtectionGenerator
      (Set.range O.language) := by
  intro L hL stream henum
  obtain ⟨z, rfl⟩ := hL
  exact O.carriedWitnessProtection_eventual_correctness henum

/-- Existential source-facing form of the literal carried-cutoff semantic
Theorem 6.1. -/
theorem theorem_6_1_carried_paper :
    ∃ gen : Generic.Generator ℕ,
      IsLimitReplayGenerator gen (Set.range O.language) :=
  ⟨O.carriedWitnessProtectionGenerator, O.theorem_6_1_carried⟩

end OracleFamily

namespace Replay

/-- Paper-facing name for the literal carried-cutoff machine. -/
def carriedWitnessProtectionGenerator
    (O : GenLimit.OracleFamily) : Generic.Generator ℕ :=
  O.carriedWitnessProtectionGenerator

/-- Paper-facing correctness theorem for the literal carried-cutoff
Algorithm 2. -/
theorem theorem_6_1_carried (O : GenLimit.OracleFamily) :
    IsLimitReplayGenerator O.carriedWitnessProtectionGenerator
      (Set.range O.language) :=
  O.theorem_6_1_carried

/-- Paper-facing existential wrapper. -/
theorem theorem_6_1_carried_paper (O : GenLimit.OracleFamily) :
    ∃ gen : Generic.Generator ℕ,
      IsLimitReplayGenerator gen (Set.range O.language) :=
  O.theorem_6_1_carried_paper

namespace CountableDomainOracleFamily

variable {α : Type*}

/-- Pull the literal carried-cutoff machine back from `ℕ` to an explicitly
enumerated arbitrary domain. -/
def carriedWitnessProtectionGenerator
    (F : CountableDomainOracleFamily α) (e : α ≃ ℕ) :
    Generic.Generator α :=
  pullGenerator e ((F.encode e).carriedWitnessProtectionGenerator)

theorem carriedWitnessProtection_eventual_correctness
    (F : CountableDomainOracleFamily α) (e : α ≃ ℕ)
    {z : ℕ} {stream : Generic.Stream α}
    (henum :
      IsReplayEnumeration (F.carriedWitnessProtectionGenerator e)
        (F.language z) stream) :
    ∃ T, ∀ t, T ≤ t →
      Generic.CorrectAt (F.carriedWitnessProtectionGenerator e)
        (F.language z) stream t := by
  let O := F.encode e
  have hencoded :
      IsReplayEnumeration O.carriedWitnessProtectionGenerator
        (O.language z) (mapStream e stream) := by
    exact
      (isReplayEnumeration_pullGenerator_iff e
        O.carriedWitnessProtectionGenerator
        (F.language z) stream).mp henum
  obtain ⟨T, hT⟩ :=
    O.carriedWitnessProtection_eventual_correctness hencoded
  refine ⟨T, ?_⟩
  intro t ht
  exact
    (correctAt_pullGenerator_iff e
      O.carriedWitnessProtectionGenerator
      (F.language z) stream t).mpr (hT t ht)

/-- Theorem 6.1 with both semantic normalizations removed: the actual
carried-cutoff machine runs on an arbitrary domain identified with `ℕ`. -/
theorem theorem_6_1_carried_equiv
    (F : CountableDomainOracleFamily α) (e : α ≃ ℕ) :
    IsLimitReplayGenerator (F.carriedWitnessProtectionGenerator e)
      (Set.range F.language) := by
  intro L hL stream henum
  obtain ⟨z, rfl⟩ := hL
  exact F.carriedWitnessProtection_eventual_correctness e henum

noncomputable def countableCarriedWitnessProtectionGenerator
    (F : CountableDomainOracleFamily α) [Countable α] :
    Generic.Generator α :=
  F.carriedWitnessProtectionGenerator F.countableEquivNat

/-- Arbitrary-countable-domain semantic Theorem 6.1 for the literal
persistent-cutoff machine. -/
theorem theorem_6_1_countable_carried
    (F : CountableDomainOracleFamily α) [Countable α] :
    IsLimitReplayGenerator
      F.countableCarriedWitnessProtectionGenerator
      (Set.range F.language) := by
  exact F.theorem_6_1_carried_equiv F.countableEquivNat

theorem theorem_6_1_countable_carried_paper
    (F : CountableDomainOracleFamily α) [Countable α] :
    ∃ gen : Generic.Generator α,
      IsLimitReplayGenerator gen (Set.range F.language) :=
  ⟨F.countableCarriedWitnessProtectionGenerator,
    F.theorem_6_1_countable_carried⟩

end CountableDomainOracleFamily

end Replay
end GenLimit
