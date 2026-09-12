import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Selection
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic

/-!
# Witness Protection for generation in the limit with replay

Source: Giorgio Racca, Michal Valko, and Amartya Sanyal,
*Language Generation with Replay: A Learning-Theoretic View of Model
Collapse*, arXiv:2603.11784v2, Definition 6.2, Algorithm 2, and
Lemmas 6.3--6.5.

This file isolates the finite-oracle predicate and termination core at the
heart of Algorithm 2.  `sure` contains observations that cannot be explained by a
previous output, while `pastOutputs` is the set of outputs available for
replay.  All predicates used by the round are finite Boolean computations
against an `OracleFamily`.

The source uses the one-based prefix `{1, ..., m}`.  Lean uses the strict
zero-based prefix `{u | u < m}`.  Thus increasing `m` exposes one more
possible membership query, exactly as in the existing finite-query
Kleinberg--Mullainathan implementation.
-/

namespace GenLimit

namespace OracleFamily

variable (O : GenLimit.OracleFamily)

/-! ## Definition 6.2 -/

/-- Consistency with the observations known to come from the target.  This is
an executable finite conjunction of membership-oracle answers. -/
def ReplayConsistentAt (sure : Finset ℕ) (i : ℕ) : Prop :=
  ∀ x ∈ sure, O.query i x = true

instance replayConsistentAtDecidable (sure : Finset ℕ) (i : ℕ) :
    Decidable (O.ReplayConsistentAt sure i) := by
  unfold ReplayConsistentAt
  infer_instance

theorem replayConsistentAt_iff
    {sure : Finset ℕ} {i : ℕ} :
    O.ReplayConsistentAt sure i ↔
      (↑sure : Set ℕ) ⊆ O.language i := by
  constructor
  · intro h x hx
    exact (O.query_spec i x).mp (h x (by simpa using hx))
  · intro h x hx
    exact (O.query_spec i x).mpr (h (by simpa using hx))

theorem replayConsistentAt_mono
    {sure sure' : Finset ℕ} {i : ℕ}
    (hsub : sure ⊆ sure')
    (h : O.ReplayConsistentAt sure' i) :
    O.ReplayConsistentAt sure i := by
  intro x hx
  exact h x (hsub hx)

/-- Definition 6.2, restricted to the finite domain prefix inspected in the
current repeat-until iteration.  The source quantifies only over earlier
indices `j < i`, and permits failures already explained by `pastOutputs`. -/
def ReplayFinitelyCriticalAt
    (sure pastOutputs : Finset ℕ) (m i : ℕ) : Prop :=
  O.ReplayConsistentAt sure i ∧
    ∀ j ∈ Finset.range i, O.ReplayConsistentAt sure j →
      ∀ x ∈ Finset.range m, O.query i x = true →
        x ∉ pastOutputs → O.query j x = true

instance replayFinitelyCriticalAtDecidable
    (sure pastOutputs : Finset ℕ) (m i : ℕ) :
    Decidable (O.ReplayFinitelyCriticalAt sure pastOutputs m i) := by
  unfold ReplayFinitelyCriticalAt
  infer_instance

/-- Semantic reading of finite replay criticality. -/
theorem replayFinitelyCriticalAt_iff
    {sure pastOutputs : Finset ℕ} {m i : ℕ} :
    O.ReplayFinitelyCriticalAt sure pastOutputs m i ↔
      (↑sure : Set ℕ) ⊆ O.language i ∧
        ∀ j, j < i → (↑sure : Set ℕ) ⊆ O.language j →
          ∀ x, x < m → x ∈ O.language i →
            x ∉ pastOutputs → x ∈ O.language j := by
  simp only [ReplayFinitelyCriticalAt, O.replayConsistentAt_iff]
  constructor
  · rintro ⟨hi, hcrit⟩
    refine ⟨hi, ?_⟩
    intro j hji hj x hxm hxi hxout
    exact (O.query_spec j x).mp
      (hcrit j (Finset.mem_range.mpr hji) hj
        x (Finset.mem_range.mpr hxm)
        ((O.query_spec i x).mpr hxi) hxout)
  · rintro ⟨hi, hcrit⟩
    refine ⟨hi, ?_⟩
    intro j hjiRange hj x hxmRange hxi hxout
    exact (O.query_spec j x).mpr
      (hcrit j (Finset.mem_range.mp hjiRange) hj
        x (Finset.mem_range.mp hxmRange)
        ((O.query_spec i x).mp hxi) hxout)

/-- Increasing the inspected prefix can only destroy finite criticality. -/
theorem replayFinitelyCriticalAt_cutoff_mono
    {sure pastOutputs : Finset ℕ} {m m' i : ℕ}
    (hmm' : m' ≤ m)
    (h : O.ReplayFinitelyCriticalAt sure pastOutputs m i) :
    O.ReplayFinitelyCriticalAt sure pastOutputs m' i := by
  rcases h with ⟨hi, hcrit⟩
  refine ⟨hi, ?_⟩
  intro j hji hj x hxm' hxi hxout
  exact hcrit j hji hj x
    (Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hxm') hmm'))
    hxi hxout

/-- Full-domain replay criticality used in Lemma 6.3. -/
def ReplayCriticalAt
    (sure pastOutputs : Finset ℕ) (i : ℕ) : Prop :=
  O.ReplayConsistentAt sure i ∧
    ∀ j, j < i → O.ReplayConsistentAt sure j →
      ∀ x, x ∈ O.language i →
        x ∉ pastOutputs → x ∈ O.language j

theorem replayCriticalAt_finitelyCriticalAt
    {sure pastOutputs : Finset ℕ} {i : ℕ}
    (h : O.ReplayCriticalAt sure pastOutputs i) (m : ℕ) :
    O.ReplayFinitelyCriticalAt sure pastOutputs m i := by
  refine ⟨h.1, ?_⟩
  intro j hji hj x _hxm hxi hxout
  exact (O.query_spec j x).mpr
    (h.2 j (Finset.mem_range.mp hji) hj x
      ((O.query_spec i x).mp hxi) hxout)

/-- Candidate indices exposed at source round `t`; indices are zero-based. -/
def replayActive
    (sure : Finset ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun i => O.ReplayConsistentAt sure i)

@[simp] theorem mem_replayActive
    {sure : Finset ℕ} {t i : ℕ} :
    i ∈ O.replayActive sure t ↔
      i < t ∧ O.ReplayConsistentAt sure i := by
  simp [replayActive]

def HasReplayActive (sure : Finset ℕ) (t : ℕ) : Prop :=
  (O.replayActive sure t).Nonempty

instance hasReplayActiveDecidable (sure : Finset ℕ) (t : ℕ) :
    Decidable (O.HasReplayActive sure t) := by
  unfold HasReplayActive
  infer_instance

def replayCriticalCandidates
    (sure pastOutputs : Finset ℕ) (t m : ℕ) : Finset ℕ :=
  (Finset.range t).filter
    (fun i => O.ReplayFinitelyCriticalAt sure pastOutputs m i)

@[simp] theorem mem_replayCriticalCandidates
    {sure pastOutputs : Finset ℕ} {t m i : ℕ} :
    i ∈ O.replayCriticalCandidates sure pastOutputs t m ↔
      i < t ∧
        O.ReplayFinitelyCriticalAt sure pastOutputs m i := by
  simp [replayCriticalCandidates]

/-- The least active index is replay-critical at every cutoff. -/
theorem replayCriticalCandidates_nonempty
    {sure pastOutputs : Finset ℕ} {t : ℕ}
    (hactive : O.HasReplayActive sure t) (m : ℕ) :
    (O.replayCriticalCandidates sure pastOutputs t m).Nonempty := by
  let i := (O.replayActive sure t).min' hactive
  have hiActive : i ∈ O.replayActive sure t :=
    Finset.min'_mem _ hactive
  have hi := O.mem_replayActive.mp hiActive
  have hleast :
      ∀ j, j < i → ¬ O.ReplayConsistentAt sure j := by
    intro j hji hj
    have hjActive : j ∈ O.replayActive sure t :=
      O.mem_replayActive.mpr ⟨lt_trans hji hi.1, hj⟩
    have hij : i ≤ j :=
      Finset.min'_le _ j hjActive
    exact (Nat.not_le_of_lt hji) hij
  refine ⟨i, O.mem_replayCriticalCandidates.mpr ⟨hi.1, hi.2, ?_⟩⟩
  intro j hji hj
  exact False.elim ((hleast j (Finset.mem_range.mp hji)) hj)

/-- Algorithm 2's `n^(t,m)`: the largest active replay-critical index. -/
def replaySelected
    (sure pastOutputs : Finset ℕ) (t m : ℕ)
    (hactive : O.HasReplayActive sure t) : ℕ :=
  (O.replayCriticalCandidates sure pastOutputs t m).max'
    (O.replayCriticalCandidates_nonempty hactive m)

theorem replaySelected_mem
    {sure pastOutputs : Finset ℕ} {t m : ℕ}
    (hactive : O.HasReplayActive sure t) :
    O.replaySelected sure pastOutputs t m hactive ∈
      O.replayCriticalCandidates sure pastOutputs t m := by
  exact Finset.max'_mem _ _

theorem replaySelected_lt
    {sure pastOutputs : Finset ℕ} {t m : ℕ}
    (hactive : O.HasReplayActive sure t) :
    O.replaySelected sure pastOutputs t m hactive < t :=
  (O.mem_replayCriticalCandidates.mp
    (O.replaySelected_mem hactive)).1

theorem replaySelected_critical
    {sure pastOutputs : Finset ℕ} {t m : ℕ}
    (hactive : O.HasReplayActive sure t) :
    O.ReplayFinitelyCriticalAt sure pastOutputs m
      (O.replaySelected sure pastOutputs t m hactive) :=
  (O.mem_replayCriticalCandidates.mp
    (O.replaySelected_mem hactive)).2

theorem replaySelected_max
    {sure pastOutputs : Finset ℕ} {t m i : ℕ}
    (hactive : O.HasReplayActive sure t)
    (hit : i < t)
    (hi : O.ReplayFinitelyCriticalAt sure pastOutputs m i) :
    i ≤ O.replaySelected sure pastOutputs t m hactive := by
  exact Finset.le_max' _ i
    (O.mem_replayCriticalCandidates.mpr ⟨hit, hi⟩)

theorem replaySelected_antitone
    {sure pastOutputs : Finset ℕ} {t m m' : ℕ}
    (hactive : O.HasReplayActive sure t)
    (hmm' : m ≤ m') :
    O.replaySelected sure pastOutputs t m' hactive ≤
      O.replaySelected sure pastOutputs t m hactive := by
  apply O.replaySelected_max hactive
    (O.replaySelected_lt hactive)
  exact O.replayFinitelyCriticalAt_cutoff_mono hmm'
    (O.replaySelected_critical hactive)

theorem replaySelected_eventually_constant
    {sure pastOutputs : Finset ℕ} {t : ℕ}
    (hactive : O.HasReplayActive sure t) :
    ∃ M, ∀ m, M ≤ m →
      O.replaySelected sure pastOutputs t m hactive =
        O.replaySelected sure pastOutputs t M hactive := by
  apply antitone_nat_eventually_constant
  intro m m' hmm'
  exact O.replaySelected_antitone hactive hmm'

/-! ## Active witnesses -/

/-- The finite distinguishing set `Δᵢⱼ^(t,m)` from Algorithm 2. -/
def replayDifferencePrefix
    (pastOutputs : Finset ℕ) (i j m : ℕ) : Finset ℕ :=
  O.finitePrefix i m \ (O.finitePrefix j m ∪ pastOutputs)

@[simp] theorem mem_replayDifferencePrefix
    {pastOutputs : Finset ℕ} {i j m x : ℕ} :
    x ∈ O.replayDifferencePrefix pastOutputs i j m ↔
      x < m ∧ x ∈ O.language i ∧
        x ∉ O.language j ∧ x ∉ pastOutputs := by
  constructor
  · intro hx
    have hi := O.mem_finitePrefix.mp (Finset.mem_sdiff.mp hx).1
    have hnot := (Finset.mem_sdiff.mp hx).2
    have hj : x ∉ O.language j := by
      intro hxj
      apply hnot
      exact Finset.mem_union_left _
        (O.mem_finitePrefix.mpr ⟨hi.1, hxj⟩)
    have hout : x ∉ pastOutputs := by
      intro hxout
      apply hnot
      exact Finset.mem_union_right _ hxout
    exact ⟨hi.1, hi.2, hj, hout⟩
  · rintro ⟨hxm, hxi, hxj, hxout⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨O.mem_finitePrefix.mpr ⟨hxm, hxi⟩, ?_⟩
    intro hUnion
    rcases Finset.mem_union.mp hUnion with hj | hout
    · exact hxj (O.mem_finitePrefix.mp hj).2
    · exact hxout hout

/-- A total version of the paper's optional witness.  It is only used for
pairs whose finite difference is known to be nonempty. -/
def replayWitnessValue
    (pastOutputs : Finset ℕ) (i j m : ℕ) : ℕ :=
  if h : (O.replayDifferencePrefix pastOutputs i j m).Nonempty then
    (O.replayDifferencePrefix pastOutputs i j m).min' h
  else
    0

def replayActivePairs
    (sure : Finset ℕ) (t : ℕ) : Finset (ℕ × ℕ) :=
  ((O.replayActive sure t) ×ˢ (O.replayActive sure t)).filter
    (fun p => p.2 < p.1)

/-- The active witness set `W^(t,m)`. -/
def replayWitnesses
    (sure pastOutputs : Finset ℕ) (t m : ℕ) : Finset ℕ :=
  ((O.replayActivePairs sure t).filter (fun p =>
      (O.replayDifferencePrefix pastOutputs p.1 p.2 m).Nonempty)).image
    (fun p => O.replayWitnessValue pastOutputs p.1 p.2 m)

theorem replayWitnesses_card_le
    (sure pastOutputs : Finset ℕ) (t m : ℕ) :
    (O.replayWitnesses sure pastOutputs t m).card ≤
      (O.replayActive sure t).card *
        (O.replayActive sure t).card := by
  calc
    (O.replayWitnesses sure pastOutputs t m).card
        ≤ ((O.replayActivePairs sure t).filter (fun p =>
            (O.replayDifferencePrefix
              pastOutputs p.1 p.2 m).Nonempty)).card :=
      Finset.card_image_le
    _ ≤ (O.replayActivePairs sure t).card :=
      Finset.card_filter_le _ _
    _ ≤ ((O.replayActive sure t) ×ˢ
          (O.replayActive sure t)).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (O.replayActive sure t).card *
          (O.replayActive sure t).card := by
      exact Finset.card_product _ _

/-! ## Per-round termination -/

/-- The elements eligible for output at one cutoff of Algorithm 2. -/
def replayAdmissible
    (sure pastOutputs : Finset ℕ) (t m : ℕ)
    (hactive : O.HasReplayActive sure t) : Finset ℕ :=
  O.finitePrefix
      (O.replaySelected sure pastOutputs t m hactive) m \
    (sure ∪ pastOutputs ∪ O.replayWitnesses sure pastOutputs t m)

@[simp] theorem mem_replayAdmissible
    {sure pastOutputs : Finset ℕ} {t m x : ℕ}
    {hactive : O.HasReplayActive sure t} :
    x ∈ O.replayAdmissible sure pastOutputs t m hactive ↔
      x < m ∧
      x ∈ O.language
        (O.replaySelected sure pastOutputs t m hactive) ∧
      x ∉ sure ∧ x ∉ pastOutputs ∧
      x ∉ O.replayWitnesses sure pastOutputs t m := by
  simp [replayAdmissible, O.mem_finitePrefix, and_assoc]

/-- Restart-normalized core of Lemma 6.4: at every round with an active
candidate, some finite cutoff has an admissible output.  The proof follows
the paper's termination argument: the selected index eventually stabilizes,
while the excluded witness set has uniformly bounded cardinality. -/
theorem replayAdmissible_eventually_nonempty
    {sure pastOutputs : Finset ℕ} {t : ℕ}
    (hactive : O.HasReplayActive sure t) :
    ∃ m, (O.replayAdmissible sure pastOutputs t m hactive).Nonempty := by
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
  let m := max M (K.max' hKnonempty + 1)
  have hMm : M ≤ m := Nat.le_max_left _ _
  have hselected :
      O.replaySelected sure pastOutputs t m hactive = n := by
    exact hM m hMm
  have hKprefix : K ⊆ O.finitePrefix n m := by
    intro x hx
    apply O.mem_finitePrefix.mpr
    refine ⟨?_, hKsub (by simpa using hx)⟩
    have hxmax : x ≤ K.max' hKnonempty :=
      Finset.le_max' K x hx
    exact lt_of_le_of_lt hxmax
      (lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.le_max_right M (K.max' hKnonempty + 1)))
  refine ⟨m, ?_⟩
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

/-- The least terminating cutoff for a restart-normalized repeat-until loop.
The source carries its cutoff between rounds and first raises it past the new
observation.  Restarting the finite search at zero changes only query reuse
in the correctness argument: the witness exclusions themselves imply
freshness, and the semantic conclusions of Lemmas 6.3--6.5 are unchanged.
No run-equivalence with the literal carried-cutoff machine is asserted. -/
def replayRoundCutoff
    (sure pastOutputs : Finset ℕ) (t : ℕ)
    (hactive : O.HasReplayActive sure t) : ℕ :=
  Nat.find (O.replayAdmissible_eventually_nonempty
    (pastOutputs := pastOutputs) hactive)

theorem replayRoundCutoff_spec
    {sure pastOutputs : Finset ℕ} {t : ℕ}
    (hactive : O.HasReplayActive sure t) :
    (O.replayAdmissible sure pastOutputs t
      (O.replayRoundCutoff sure pastOutputs t hactive)
      hactive).Nonempty := by
  exact Nat.find_spec (O.replayAdmissible_eventually_nonempty
    (pastOutputs := pastOutputs) hactive)

/-- The first admissible output chosen at the first terminating cutoff.
This definition is executable relative to `O.query`; the source-facing
carried-cutoff query trace is exposed in `FiniteQueryTrace.lean`. -/
def replayRoundOutput
    (sure pastOutputs : Finset ℕ) (t : ℕ)
    (hactive : O.HasReplayActive sure t) : ℕ :=
  let m := O.replayRoundCutoff sure pastOutputs t hactive
  (O.replayAdmissible sure pastOutputs t m hactive).min'
    (O.replayRoundCutoff_spec hactive)

theorem replayRoundOutput_spec
    {sure pastOutputs : Finset ℕ} {t : ℕ}
    (hactive : O.HasReplayActive sure t) :
    let m := O.replayRoundCutoff sure pastOutputs t hactive
    let n := O.replaySelected sure pastOutputs t m hactive
    O.ReplayFinitelyCriticalAt sure pastOutputs m n ∧
      (∀ i, i < t →
        O.ReplayFinitelyCriticalAt sure pastOutputs m i →
          i ≤ n) ∧
      O.replayRoundOutput sure pastOutputs t hactive < m ∧
      O.replayRoundOutput sure pastOutputs t hactive ∈ O.language n ∧
      O.replayRoundOutput sure pastOutputs t hactive ∉ sure ∧
      O.replayRoundOutput sure pastOutputs t hactive ∉ pastOutputs ∧
      O.replayRoundOutput sure pastOutputs t hactive ∉
        O.replayWitnesses sure pastOutputs t m := by
  dsimp only
  let m := O.replayRoundCutoff sure pastOutputs t hactive
  let n := O.replaySelected sure pastOutputs t m hactive
  have hout :
      O.replayRoundOutput sure pastOutputs t hactive ∈
        O.replayAdmissible sure pastOutputs t m hactive := by
    exact Finset.min'_mem _
      (O.replayRoundCutoff_spec hactive)
  have hout' := O.mem_replayAdmissible.mp hout
  refine ⟨O.replaySelected_critical hactive, ?_, hout'.1,
    hout'.2.1, hout'.2.2.1, hout'.2.2.2.1, hout'.2.2.2.2⟩
  intro i hit hi
  exact O.replaySelected_max hactive hit hi

/-- Lemma 6.5's one-round validity argument.  Once the target index is
replay-critical, maximality puts the selected index at or after it; selected
criticality then transports every non-replayed output back into the target. -/
theorem replayRoundOutput_mem_of_targetCritical
    {sure pastOutputs : Finset ℕ} {t z : ℕ}
    (hactive : O.HasReplayActive sure t)
    (hzt : z < t)
    (hzcritical :
      O.ReplayFinitelyCriticalAt sure pastOutputs
        (O.replayRoundCutoff sure pastOutputs t hactive) z) :
    O.replayRoundOutput sure pastOutputs t hactive ∈
      O.language z := by
  let m := O.replayRoundCutoff sure pastOutputs t hactive
  let n := O.replaySelected sure pastOutputs t m hactive
  have hspec := O.replayRoundOutput_spec
    (pastOutputs := pastOutputs) hactive
  dsimp only at hspec
  rcases hspec with
    ⟨hncritical, hmax, houtlt, houtn, _houtSure,
      houtPast, _houtWitness⟩
  have hzn : z ≤ n := hmax z hzt hzcritical
  rcases eq_or_lt_of_le hzn with hznEq | hznLt
  · simpa [hznEq] using houtn
  · have hsemantic :=
      O.replayFinitelyCriticalAt_iff.mp hncritical
    exact hsemantic.2 z hznLt
      (O.replayFinitelyCriticalAt_iff.mp hzcritical).1
      (O.replayRoundOutput sure pastOutputs t hactive)
      houtlt houtn houtPast

/-- Every output of the terminating membership-query round is fresh relative
to both the sure observations and all previous outputs. -/
theorem replayRoundOutput_fresh
    {sure pastOutputs : Finset ℕ} {t : ℕ}
    (hactive : O.HasReplayActive sure t) :
    O.replayRoundOutput sure pastOutputs t hactive ∉ sure ∧
      O.replayRoundOutput sure pastOutputs t hactive ∉ pastOutputs := by
  have hspec := O.replayRoundOutput_spec
    (pastOutputs := pastOutputs) hactive
  dsimp only at hspec
  exact ⟨hspec.2.2.2.2.1, hspec.2.2.2.2.2.1⟩

/-- Witness-protection invariant for one round.  If `w` is the least
currently un-replayed point separating active `i` from earlier active `j`,
the round cannot output `w`: below the cutoff it is placed in `W^(t,m)`,
while at a smaller cutoff every eligible output is strictly below `w`. -/
theorem replayRoundOutput_ne_leastDifference
    {sure pastOutputs : Finset ℕ} {t i j w : ℕ}
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
    O.replayRoundOutput sure pastOutputs t hactive ≠ w := by
  let m := O.replayRoundCutoff sure pastOutputs t hactive
  have hspec := O.replayRoundOutput_spec
    (pastOutputs := pastOutputs) hactive
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
    exact hspec.2.2.2.2.2.2 (hout ▸ hwW)
  · intro hout
    have houtlt := hspec.2.2.1
    have hmw : m ≤ w := Nat.le_of_not_gt hwm
    rw [hout] at houtlt
    exact (Nat.not_lt_of_ge hmw) houtlt

/-! ## Stable witnesses used in Lemma 6.3 -/

def HasReplayDifference
    (pastOutputs : Finset ℕ) (i j : ℕ) : Prop :=
  ∃ x, x ∈ O.language i ∧
    x ∉ O.language j ∧ x ∉ pastOutputs

/-- The least full-domain witness at the first round exposing target index
`i`.  Algorithm 2 subsequently protects this fixed point. -/
noncomputable def replayLeastDifference
    (pastOutputs : Finset ℕ) (i j : ℕ) : ℕ := by
  classical
  exact if h : O.HasReplayDifference pastOutputs i j then
      Nat.find h
    else
      0

theorem replayLeastDifference_spec
    {pastOutputs : Finset ℕ} {i j : ℕ}
    (h : O.HasReplayDifference pastOutputs i j) :
    O.replayLeastDifference pastOutputs i j ∈ O.language i ∧
      O.replayLeastDifference pastOutputs i j ∉ O.language j ∧
      O.replayLeastDifference pastOutputs i j ∉ pastOutputs := by
  classical
  rw [replayLeastDifference, dif_pos h]
  exact Nat.find_spec h

theorem replayLeastDifference_minimal
    {pastOutputs : Finset ℕ} {i j : ℕ}
    (h : O.HasReplayDifference pastOutputs i j) :
    ∀ x, x < O.replayLeastDifference pastOutputs i j →
      x ∈ O.language i → x ∉ O.language j →
      x ∉ pastOutputs → False := by
  classical
  intro x hx hxi hxj hxout
  rw [replayLeastDifference, dif_pos h] at hx
  exact Nat.find_min h hx ⟨hxi, hxj, hxout⟩

end OracleFamily

end GenLimit
