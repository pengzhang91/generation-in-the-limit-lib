import GenLimit.Paper22_LanguageGenerationWithReplay.CarriedCutoff

/-!
# Finite-query realization of Witness Protection

This module supplies the operational access-model component of Theorem 6.1
in Racca--Valko--Sanyal, *Language Generation with Replay*.  The literal
carried-cutoff machine is executable relative to the Boolean membership
oracle in `OracleFamily`.  Here we additionally expose, at every round, a
finite answered-query trace sufficient to perform all finite consistency,
criticality, witness, and admissibility tests through the terminating cutoff.

The trace is deliberately exhaustive: at cutoff `m` it asks every query
`(i,x)` with `i < t` and either `x` in the current sure set or `x < m`.
This can ask more questions than a short-circuiting implementation, but it is
finite and contains every membership answer that Algorithm 2 may inspect.
No uniform query-count or running-time bound is claimed.

The arbitrary-countable-domain semantic theorem remains in
`CountableTransport.lean`.  Transporting this executable trace through an
abstract `[Countable α]` is not claimed: machine-level transport requires an
explicit effective encoding, rather than the classically chosen equivalence
used by the semantic wrapper.
-/

namespace GenLimit
namespace OracleFamily

open GenLimit.Replay

variable (O : GenLimit.OracleFamily)

/-- One membership query names a family index and a natural-number word. -/
abbrev ReplayMembershipQuery := ℕ × ℕ

/-- A query together with the Boolean answer returned by the family oracle. -/
abbrev AnsweredReplayMembershipQuery := ReplayMembershipQuery × Bool

/-- A finite, duplicate-free batch of answered membership queries. -/
abbrev ReplayMembershipTrace := Finset AnsweredReplayMembershipQuery

/-- Attach the truthful answer of `O` to a membership query. -/
def answerReplayMembershipQuery
    (q : ReplayMembershipQuery) : AnsweredReplayMembershipQuery :=
  (q, O.query q.1 q.2)

/-- Every answer in a finite trace is the answer returned by `O`. -/
def ReplayMembershipTraceValid
    (trace : ReplayMembershipTrace) : Prop :=
  ∀ qa ∈ trace, qa.2 = O.query qa.1.1 qa.1.2

/-- Queries sufficient for one fixed-cutoff test of Algorithm 2.

The first component ranges over every exposed family index.  The second
component contains both the current sure set (for consistency) and the
finite domain prefix (for finite criticality and witness construction). -/
def replayStageQueryPlan
    (sure : Finset ℕ) (t m : ℕ) : Finset ReplayMembershipQuery :=
  (Finset.range t) ×ˢ (sure ∪ Finset.range m)

/-- Truthful answered trace for one fixed cutoff. -/
def replayStageQueryTrace
    (sure : Finset ℕ) (t m : ℕ) :
    ReplayMembershipTrace :=
  (replayStageQueryPlan sure t m).image O.answerReplayMembershipQuery

@[simp] theorem replayStageQueryTrace_valid
    (sure : Finset ℕ) (t m : ℕ) :
    O.ReplayMembershipTraceValid (O.replayStageQueryTrace sure t m) := by
  intro qa hqa
  rw [replayStageQueryTrace, Finset.mem_image] at hqa
  obtain ⟨q, _hq, rfl⟩ := hqa
  rfl

theorem replayStageQueryPlan_contains_sure
    {sure : Finset ℕ} {t m i x : ℕ}
    (hi : i < t) (hx : x ∈ sure) :
    (i, x) ∈ replayStageQueryPlan sure t m := by
  simp [replayStageQueryPlan, hi, hx]

theorem replayStageQueryPlan_contains_prefix
    {sure : Finset ℕ} {t m i x : ℕ}
    (hi : i < t) (hx : x < m) :
    (i, x) ∈ replayStageQueryPlan sure t m := by
  simp [replayStageQueryPlan, hi, hx]

theorem replayStageQueryPlan_covers
    {sure : Finset ℕ} {t m i x : ℕ}
    (hi : i < t) (hx : x ∈ sure ∨ x < m) :
    (i, x) ∈ replayStageQueryPlan sure t m := by
  rcases hx with hx | hx
  · exact replayStageQueryPlan_contains_sure hi hx
  · exact replayStageQueryPlan_contains_prefix hi hx

theorem replayStageQueryPlan_card_le
    (sure : Finset ℕ) (t m : ℕ) :
    (replayStageQueryPlan sure t m).card ≤
      t * (sure.card + m) := by
  rw [replayStageQueryPlan, Finset.card_product, Finset.card_range]
  apply Nat.mul_le_mul_left t
  simpa using Finset.card_union_le sure (Finset.range m)

theorem replayStageQueryTrace_card_le
    (sure : Finset ℕ) (t m : ℕ) :
    (O.replayStageQueryTrace sure t m).card ≤
      t * (sure.card + m) := by
  exact (Finset.card_image_le.trans
    (replayStageQueryPlan_card_le sure t m))

/-- Query cache sufficient for every tested cutoff through `cutoff`.

The finite-prefix parts of the plans are nested, so the plan at the final
cutoff already contains every query needed at all earlier cutoffs. -/
def replayRoundQueryPlan
    (sure : Finset ℕ) (t cutoff : ℕ) :
    Finset ReplayMembershipQuery :=
  replayStageQueryPlan sure t cutoff

/-- Truthful finite trace through a terminating carried cutoff. -/
def replayRoundQueryTrace
    (sure : Finset ℕ) (t cutoff : ℕ) :
    ReplayMembershipTrace :=
  (replayRoundQueryPlan sure t cutoff).image
    O.answerReplayMembershipQuery

@[simp] theorem replayRoundQueryTrace_valid
    (sure : Finset ℕ) (t cutoff : ℕ) :
    O.ReplayMembershipTraceValid
      (O.replayRoundQueryTrace sure t cutoff) := by
  intro qa hqa
  rw [replayRoundQueryTrace, Finset.mem_image] at hqa
  obtain ⟨q, _hq, rfl⟩ := hqa
  rfl

theorem replayRoundQueryTrace_card_le
    (sure : Finset ℕ) (t cutoff : ℕ) :
    (O.replayRoundQueryTrace sure t cutoff).card ≤
      t * (sure.card + cutoff) := by
  exact (Finset.card_image_le.trans
    (replayStageQueryPlan_card_le sure t cutoff))

theorem replayStageQueryPlan_subset_round
    {sure : Finset ℕ} {t cutoff m : ℕ}
    (hcutoff : m ≤ cutoff) :
    ∀ q ∈ replayStageQueryPlan sure t m,
      q ∈ replayRoundQueryPlan sure t cutoff := by
  rintro ⟨i, x⟩ hq
  rw [replayStageQueryPlan] at hq
  rw [replayRoundQueryPlan, replayStageQueryPlan]
  have hi : i < t := Finset.mem_range.mp (Finset.mem_product.mp hq).1
  have hx := (Finset.mem_product.mp hq).2
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_range.mpr hi, ?_⟩
  rcases Finset.mem_union.mp hx with hxSure | hxPrefix
  · exact Finset.mem_union_left _ hxSure
  · exact Finset.mem_union_right _
      (Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hxPrefix) hcutoff))

theorem replayRoundQueryTrace_contains
    {sure : Finset ℕ} {t lower cutoff m i x : ℕ}
    (_hlower : lower ≤ m) (hcutoff : m ≤ cutoff)
    (hi : i < t) (hx : x ∈ sure ∨ x < m) :
    ((i, x), O.query i x) ∈
      O.replayRoundQueryTrace sure t cutoff := by
  rw [replayRoundQueryTrace, Finset.mem_image]
  refine ⟨(i, x), ?_, rfl⟩
  exact replayStageQueryPlan_subset_round hcutoff _
    (replayStageQueryPlan_covers hi hx)

/-! ## Extensional sufficiency of the finite cache -/

/-- Two family oracles agree on every query relevant to the current sure set
and finite-prefix cutoff. -/
def ReplayQueryRectangleAgrees
    (P : GenLimit.OracleFamily) (sure : Finset ℕ) (t cutoff : ℕ) : Prop :=
  ∀ i, i < t → ∀ x, x ∈ sure ∨ x < cutoff →
    O.query i x = P.query i x

theorem replayStageQueryTrace_forces_rectangle_agreement
    {P : GenLimit.OracleFamily} {sure : Finset ℕ} {t cutoff : ℕ}
    (hP : P.ReplayMembershipTraceValid
      (O.replayStageQueryTrace sure t cutoff)) :
    O.ReplayQueryRectangleAgrees P sure t cutoff := by
  intro i hi x hx
  have hmem :
      ((i, x), O.query i x) ∈
        O.replayStageQueryTrace sure t cutoff := by
    rw [replayStageQueryTrace, Finset.mem_image]
    refine ⟨(i, x), replayStageQueryPlan_covers hi hx, rfl⟩
  exact hP _ hmem

theorem replayRoundQueryTrace_forces_rectangle_agreement
    {P : GenLimit.OracleFamily} {sure : Finset ℕ} {t cutoff : ℕ}
    (hP : P.ReplayMembershipTraceValid
      (O.replayRoundQueryTrace sure t cutoff)) :
    O.ReplayQueryRectangleAgrees P sure t cutoff := by
  exact O.replayStageQueryTrace_forces_rectangle_agreement hP

theorem replayConsistentAt_iff_of_rectangle_agreement
    {P : GenLimit.OracleFamily} {sure : Finset ℕ} {t cutoff i : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hi : i < t) :
    O.ReplayConsistentAt sure i ↔ P.ReplayConsistentAt sure i := by
  constructor
  · intro h x hx
    rw [← hagree i hi x (Or.inl hx)]
    exact h x hx
  · intro h x hx
    rw [hagree i hi x (Or.inl hx)]
    exact h x hx

theorem replayActive_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily} {sure : Finset ℕ} {t cutoff : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff) :
    O.replayActive sure t = P.replayActive sure t := by
  apply Finset.ext
  intro i
  simp only [O.mem_replayActive, P.mem_replayActive]
  constructor
  · rintro ⟨hi, hconsistent⟩
    exact ⟨hi,
      (O.replayConsistentAt_iff_of_rectangle_agreement hagree hi).mp
        hconsistent⟩
  · rintro ⟨hi, hconsistent⟩
    exact ⟨hi,
      (O.replayConsistentAt_iff_of_rectangle_agreement hagree hi).mpr
        hconsistent⟩

theorem replayFinitelyCriticalAt_iff_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t cutoff m i : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hi : i < t) (hm : m ≤ cutoff) :
    O.ReplayFinitelyCriticalAt sure pastOutputs m i ↔
      P.ReplayFinitelyCriticalAt sure pastOutputs m i := by
  constructor
  · rintro ⟨hconsistent, hcritical⟩
    refine
      ⟨(O.replayConsistentAt_iff_of_rectangle_agreement hagree hi).mp
          hconsistent, ?_⟩
    intro j hjRange hjConsistent x hxRange hix hxPast
    have hj : j < t :=
      lt_trans (Finset.mem_range.mp hjRange) hi
    have hjConsistentO : O.ReplayConsistentAt sure j :=
      (O.replayConsistentAt_iff_of_rectangle_agreement hagree hj).mpr
        hjConsistent
    have hx : x < cutoff :=
      lt_of_lt_of_le (Finset.mem_range.mp hxRange) hm
    have hixO : O.query i x = true := by
      rw [hagree i hi x (Or.inr hx)]
      exact hix
    have hjxO :=
      hcritical j hjRange hjConsistentO x hxRange hixO hxPast
    rw [← hagree j hj x (Or.inr hx)]
    exact hjxO
  · rintro ⟨hconsistent, hcritical⟩
    refine
      ⟨(O.replayConsistentAt_iff_of_rectangle_agreement hagree hi).mpr
          hconsistent, ?_⟩
    intro j hjRange hjConsistent x hxRange hix hxPast
    have hj : j < t :=
      lt_trans (Finset.mem_range.mp hjRange) hi
    have hjConsistentP : P.ReplayConsistentAt sure j :=
      (O.replayConsistentAt_iff_of_rectangle_agreement hagree hj).mp
        hjConsistent
    have hx : x < cutoff :=
      lt_of_lt_of_le (Finset.mem_range.mp hxRange) hm
    have hixP : P.query i x = true := by
      rw [← hagree i hi x (Or.inr hx)]
      exact hix
    have hjxP :=
      hcritical j hjRange hjConsistentP x hxRange hixP hxPast
    rw [hagree j hj x (Or.inr hx)]
    exact hjxP

theorem replayCriticalCandidates_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t cutoff m : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hm : m ≤ cutoff) :
    O.replayCriticalCandidates sure pastOutputs t m =
      P.replayCriticalCandidates sure pastOutputs t m := by
  apply Finset.ext
  intro i
  simp only [O.mem_replayCriticalCandidates,
    P.mem_replayCriticalCandidates]
  constructor
  · rintro ⟨hi, hcritical⟩
    exact ⟨hi,
      (O.replayFinitelyCriticalAt_iff_of_rectangle_agreement
        hagree hi hm).mp hcritical⟩
  · rintro ⟨hi, hcritical⟩
    exact ⟨hi,
      (O.replayFinitelyCriticalAt_iff_of_rectangle_agreement
        hagree hi hm).mpr hcritical⟩

theorem replaySelected_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t cutoff m : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hm : m ≤ cutoff)
    (hactiveO : O.HasReplayActive sure t)
    (hactiveP : P.HasReplayActive sure t) :
    O.replaySelected sure pastOutputs t m hactiveO =
      P.replaySelected sure pastOutputs t m hactiveP := by
  apply Nat.le_antisymm
  · apply P.replaySelected_max hactiveP (O.replaySelected_lt hactiveO)
    exact
      (O.replayFinitelyCriticalAt_iff_of_rectangle_agreement
        hagree (O.replaySelected_lt hactiveO) hm).mp
        (O.replaySelected_critical hactiveO)
  · apply O.replaySelected_max hactiveO (P.replaySelected_lt hactiveP)
    exact
      (O.replayFinitelyCriticalAt_iff_of_rectangle_agreement
        hagree (P.replaySelected_lt hactiveP) hm).mpr
        (P.replaySelected_critical hactiveP)

theorem finitePrefix_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily} {sure : Finset ℕ}
    {t cutoff m i : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hi : i < t) (hm : m ≤ cutoff) :
    O.finitePrefix i m = P.finitePrefix i m := by
  apply Finset.ext
  intro x
  simp only [finitePrefix, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hx, hquery⟩
    refine ⟨hx, ?_⟩
    rw [← hagree i hi x (Or.inr (lt_of_lt_of_le hx hm))]
    exact hquery
  · rintro ⟨hx, hquery⟩
    refine ⟨hx, ?_⟩
    rw [hagree i hi x (Or.inr (lt_of_lt_of_le hx hm))]
    exact hquery

theorem replayDifferencePrefix_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t cutoff m i j : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hi : i < t) (hj : j < t) (hm : m ≤ cutoff) :
    O.replayDifferencePrefix pastOutputs i j m =
      P.replayDifferencePrefix pastOutputs i j m := by
  unfold replayDifferencePrefix
  rw [O.finitePrefix_eq_of_rectangle_agreement hagree hi hm,
    O.finitePrefix_eq_of_rectangle_agreement hagree hj hm]

theorem replayWitnessValue_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t cutoff m i j : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hi : i < t) (hj : j < t) (hm : m ≤ cutoff) :
    O.replayWitnessValue pastOutputs i j m =
      P.replayWitnessValue pastOutputs i j m := by
  unfold replayWitnessValue
  rw [O.replayDifferencePrefix_eq_of_rectangle_agreement
    hagree hi hj hm]

theorem replayActivePairs_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily} {sure : Finset ℕ} {t cutoff : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff) :
    O.replayActivePairs sure t = P.replayActivePairs sure t := by
  unfold replayActivePairs
  rw [O.replayActive_eq_of_rectangle_agreement hagree]

theorem replayWitnesses_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t cutoff m : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hm : m ≤ cutoff) :
    O.replayWitnesses sure pastOutputs t m =
      P.replayWitnesses sure pastOutputs t m := by
  let pairsO := O.replayActivePairs sure t
  let pairsP := P.replayActivePairs sure t
  have hpairs : pairsO = pairsP :=
    O.replayActivePairs_eq_of_rectangle_agreement hagree
  have hindicesO :
      ∀ p ∈ pairsO, p.1 < t ∧ p.2 < t := by
    intro p hp
    have hpProduct := (Finset.mem_filter.mp hp).1
    have hpActive := Finset.mem_product.mp hpProduct
    exact
      ⟨(O.mem_replayActive.mp hpActive.1).1,
        (O.mem_replayActive.mp hpActive.2).1⟩
  have hindicesP :
      ∀ p ∈ pairsP, p.1 < t ∧ p.2 < t := by
    intro p hp
    have hpProduct := (Finset.mem_filter.mp hp).1
    have hpActive := Finset.mem_product.mp hpProduct
    exact
      ⟨(P.mem_replayActive.mp hpActive.1).1,
        (P.mem_replayActive.mp hpActive.2).1⟩
  have hfiltered :
      pairsO.filter (fun p =>
          (O.replayDifferencePrefix
            pastOutputs p.1 p.2 m).Nonempty) =
        pairsP.filter (fun p =>
          (P.replayDifferencePrefix
            pastOutputs p.1 p.2 m).Nonempty) := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hnonempty⟩
      have hpP : p ∈ pairsP := by simpa [hpairs] using hp
      have hi := hindicesO p hp
      refine ⟨hpP, ?_⟩
      rw [← O.replayDifferencePrefix_eq_of_rectangle_agreement
        hagree hi.1 hi.2 hm]
      exact hnonempty
    · rintro ⟨hp, hnonempty⟩
      have hpO : p ∈ pairsO := by simpa [hpairs] using hp
      have hi := hindicesP p hp
      refine ⟨hpO, ?_⟩
      rw [O.replayDifferencePrefix_eq_of_rectangle_agreement
        hagree hi.1 hi.2 hm]
      exact hnonempty
  unfold replayWitnesses
  change
    (pairsO.filter (fun p =>
        (O.replayDifferencePrefix
          pastOutputs p.1 p.2 m).Nonempty)).image
        (fun p => O.replayWitnessValue pastOutputs p.1 p.2 m) =
      (pairsP.filter (fun p =>
        (P.replayDifferencePrefix
          pastOutputs p.1 p.2 m).Nonempty)).image
        (fun p => P.replayWitnessValue pastOutputs p.1 p.2 m)
  rw [hfiltered]
  apply Finset.image_congr
  intro p hp
  have hpPair : p ∈ pairsP := (Finset.mem_filter.mp hp).1
  have hi := hindicesP p hpPair
  exact O.replayWitnessValue_eq_of_rectangle_agreement
    hagree hi.1 hi.2 hm

theorem replayAdmissible_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t cutoff m : ℕ}
    (hagree : O.ReplayQueryRectangleAgrees P sure t cutoff)
    (hm : m ≤ cutoff)
    (hactiveO : O.HasReplayActive sure t)
    (hactiveP : P.HasReplayActive sure t) :
    O.replayAdmissible sure pastOutputs t m hactiveO =
      P.replayAdmissible sure pastOutputs t m hactiveP := by
  have hselected :=
    O.replaySelected_eq_of_rectangle_agreement
      (pastOutputs := pastOutputs) hagree hm hactiveO hactiveP
  have hprefix :
      O.finitePrefix
          (O.replaySelected sure pastOutputs t m hactiveO) m =
        P.finitePrefix
          (P.replaySelected sure pastOutputs t m hactiveP) m := by
    rw [hselected]
    exact O.finitePrefix_eq_of_rectangle_agreement
      hagree (P.replaySelected_lt hactiveP) hm
  unfold replayAdmissible
  rw [hprefix,
    O.replayWitnesses_eq_of_rectangle_agreement hagree hm]

theorem replayCarriedRoundCutoff_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t lower : ℕ}
    (hactiveO : O.HasReplayActive sure t)
    (hactiveP : P.HasReplayActive sure t)
    (hagree : O.ReplayQueryRectangleAgrees P sure t
      (O.replayCarriedRoundCutoff
        sure pastOutputs t lower hactiveO)) :
    O.replayCarriedRoundCutoff sure pastOutputs t lower hactiveO =
      P.replayCarriedRoundCutoff sure pastOutputs t lower hactiveP := by
  let cutoffO :=
    O.replayCarriedRoundCutoff sure pastOutputs t lower hactiveO
  let cutoffP :=
    P.replayCarriedRoundCutoff sure pastOutputs t lower hactiveP
  have hadmissible :
      ∀ m, m ≤ cutoffO →
        O.replayAdmissible sure pastOutputs t m hactiveO =
          P.replayAdmissible sure pastOutputs t m hactiveP := by
    intro m hm
    exact O.replayAdmissible_eq_of_rectangle_agreement
      hagree hm hactiveO hactiveP
  have hPleO : cutoffP ≤ cutoffO := by
    unfold cutoffP replayCarriedRoundCutoff
    apply Nat.find_min'
    refine ⟨(O.replayCarriedRoundCutoff_spec hactiveO).1, ?_⟩
    rw [← hadmissible cutoffO le_rfl]
    exact (O.replayCarriedRoundCutoff_spec hactiveO).2
  have hOleP : cutoffO ≤ cutoffP := by
    by_contra hnot
    have hlt : cutoffP < cutoffO := Nat.lt_of_not_ge hnot
    have hminimal := Nat.find_min
      (O.replayAdmissible_eventually_nonempty_from
        (pastOutputs := pastOutputs) hactiveO lower) hlt
    apply hminimal
    refine ⟨(P.replayCarriedRoundCutoff_spec hactiveP).1, ?_⟩
    rw [hadmissible cutoffP (Nat.le_of_lt hlt)]
    exact (P.replayCarriedRoundCutoff_spec hactiveP).2
  exact Nat.le_antisymm hOleP hPleO

theorem replayCarriedRoundOutput_eq_of_rectangle_agreement
    {P : GenLimit.OracleFamily}
    {sure pastOutputs : Finset ℕ} {t lower : ℕ}
    (hactiveO : O.HasReplayActive sure t)
    (hactiveP : P.HasReplayActive sure t)
    (hagree : O.ReplayQueryRectangleAgrees P sure t
      (O.replayCarriedRoundCutoff
        sure pastOutputs t lower hactiveO)) :
    O.replayCarriedRoundOutput sure pastOutputs t lower hactiveO =
      P.replayCarriedRoundOutput sure pastOutputs t lower hactiveP := by
  have hcutoff :=
    O.replayCarriedRoundCutoff_eq_of_rectangle_agreement
      hactiveO hactiveP hagree
  let cutoffO :=
    O.replayCarriedRoundCutoff sure pastOutputs t lower hactiveO
  let cutoffP :=
    P.replayCarriedRoundCutoff sure pastOutputs t lower hactiveP
  have hadmissible :
      O.replayAdmissible sure pastOutputs t cutoffO hactiveO =
        P.replayAdmissible sure pastOutputs t cutoffP hactiveP := by
    dsimp only [cutoffO, cutoffP]
    rw [← hcutoff]
    exact O.replayAdmissible_eq_of_rectangle_agreement
      hagree le_rfl hactiveO hactiveP
  unfold replayCarriedRoundOutput
  dsimp only
  let admissibleO :=
    O.replayAdmissible sure pastOutputs t cutoffO hactiveO
  let admissibleP :=
    P.replayAdmissible sure pastOutputs t cutoffP hactiveP
  have hadmissible' : admissibleO = admissibleP := by
    exact hadmissible
  have hOP : ∀ {z}, z ∈ admissibleO → z ∈ admissibleP := by
    intro z hz
    exact hadmissible' ▸ hz
  have hPO : ∀ {z}, z ∈ admissibleP → z ∈ admissibleO := by
    intro z hz
    exact hadmissible'.symm ▸ hz
  change
    admissibleO.min' _ = admissibleP.min' _
  apply Nat.le_antisymm
  · apply Finset.min'_le
    exact hPO (Finset.min'_mem _ _)
  · apply Finset.min'_le
    exact hOP (Finset.min'_mem _ _)

/-- The finite answered trace produced by the literal carried-cutoff
transition.  On an active round it covers every cutoff searched up to and
including the first admissible one.  On an inactive round it records the
finite consistency checks needed to discover that no index is active. -/
def carriedWitnessProtectionQueryTrace
    (state : CarriedWitnessProtectionState) (x t : ℕ) :
    ReplayMembershipTrace :=
  let sure :=
    witnessProtectionSureUpdate
      ⟨state.sure, state.pastOutputs, state.output⟩ x
  if hactive : O.HasReplayActive sure t then
    let lower := replayCarriedStart state x
    let cutoff :=
      O.replayCarriedRoundCutoff
        sure state.pastOutputs t lower hactive
    O.replayRoundQueryTrace sure t cutoff
  else
    O.replayStageQueryTrace sure t 0

theorem carriedWitnessProtectionQueryTrace_valid
    (state : CarriedWitnessProtectionState) (x t : ℕ) :
    O.ReplayMembershipTraceValid
      (O.carriedWitnessProtectionQueryTrace state x t) := by
  simp only [carriedWitnessProtectionQueryTrace]
  split
  · apply O.replayRoundQueryTrace_valid
  · apply O.replayStageQueryTrace_valid

/-- Extensional finite-query certificate: any second valid family oracle that
returns the same answers on the recorded finite cache produces exactly the
same literal carried-cutoff transition.  Thus the cache determines the round
result; the machine has no hidden access to unrecorded membership values. -/
theorem carriedWitnessProtectionProcessRound_eq_of_trace
    (P : GenLimit.OracleFamily)
    (state : CarriedWitnessProtectionState) (x t : ℕ)
    (hP : P.ReplayMembershipTraceValid
      (O.carriedWitnessProtectionQueryTrace state x t)) :
    P.carriedWitnessProtectionProcessRound state x t =
      O.carriedWitnessProtectionProcessRound state x t := by
  let sure :=
    witnessProtectionSureUpdate
      ⟨state.sure, state.pastOutputs, state.output⟩ x
  by_cases hactiveO : O.HasReplayActive sure t
  · let lower := replayCarriedStart state x
    let cutoff :=
      O.replayCarriedRoundCutoff
        sure state.pastOutputs t lower hactiveO
    have hPtrace :
        P.ReplayMembershipTraceValid
          (O.replayRoundQueryTrace sure t cutoff) := by
      simpa [carriedWitnessProtectionQueryTrace, sure, lower, cutoff,
        hactiveO] using hP
    have hagree : O.ReplayQueryRectangleAgrees P sure t cutoff :=
      O.replayRoundQueryTrace_forces_rectangle_agreement hPtrace
    have hactiveP : P.HasReplayActive sure t := by
      unfold HasReplayActive at hactiveO ⊢
      rw [← O.replayActive_eq_of_rectangle_agreement hagree]
      exact hactiveO
    have hcutoff :=
      O.replayCarriedRoundCutoff_eq_of_rectangle_agreement
        hactiveO hactiveP hagree
    have houtput :=
      O.replayCarriedRoundOutput_eq_of_rectangle_agreement
        hactiveO hactiveP hagree
    simp only [carriedWitnessProtectionProcessRound, sure,
      hactiveO, hactiveP, ↓reduceDIte]
    rw [← hcutoff, ← houtput]
  · have hPtrace :
        P.ReplayMembershipTraceValid
          (O.replayStageQueryTrace sure t 0) := by
      simpa [carriedWitnessProtectionQueryTrace, sure, hactiveO] using hP
    have hagree : O.ReplayQueryRectangleAgrees P sure t 0 :=
      O.replayStageQueryTrace_forces_rectangle_agreement hPtrace
    have hactiveP : ¬P.HasReplayActive sure t := by
      unfold HasReplayActive at hactiveO ⊢
      rw [← O.replayActive_eq_of_rectangle_agreement hagree]
      exact hactiveO
    simp [carriedWitnessProtectionProcessRound, sure,
      hactiveO, hactiveP]

/-- On every active round, the explicit finite trace contains every oracle
answer used at every cutoff examined by the repeat-until search. -/
theorem carriedWitnessProtectionQueryTrace_covers_active
    (state : CarriedWitnessProtectionState) (x t : ℕ)
    (hactive :
      O.HasReplayActive
        (witnessProtectionSureUpdate
          ⟨state.sure, state.pastOutputs, state.output⟩ x) t) :
    let sure :=
      witnessProtectionSureUpdate
        ⟨state.sure, state.pastOutputs, state.output⟩ x
    let lower := replayCarriedStart state x
    let cutoff :=
      O.replayCarriedRoundCutoff
        sure state.pastOutputs t lower hactive
    O.carriedWitnessProtectionProcessRound state x t = (
        let out :=
          O.replayCarriedRoundOutput
            sure state.pastOutputs t lower hactive
        ⟨sure, insert out state.pastOutputs, cutoff, out⟩) ∧
      lower ≤ cutoff ∧
      (O.carriedWitnessProtectionQueryTrace state x t).card ≤
        t * (sure.card + cutoff) ∧
      ∀ m, lower ≤ m → m ≤ cutoff →
        ∀ i, i < t → ∀ y, y ∈ sure ∨ y < m →
          ((i, y), O.query i y) ∈
            O.carriedWitnessProtectionQueryTrace state x t := by
  dsimp only
  let sure :=
    witnessProtectionSureUpdate
      ⟨state.sure, state.pastOutputs, state.output⟩ x
  let lower := replayCarriedStart state x
  let cutoff :=
    O.replayCarriedRoundCutoff
      sure state.pastOutputs t lower hactive
  have hlower : lower ≤ cutoff :=
    (O.replayCarriedRoundCutoff_spec hactive).1
  refine ⟨?_, hlower, ?_, ?_⟩
  · exact O.carriedWitnessProtectionProcessRound_of_active
      state x t hactive
  · rw [carriedWitnessProtectionQueryTrace]
    simp only [hactive, ↓reduceDIte]
    exact O.replayRoundQueryTrace_card_le sure t cutoff
  intro m hmLower hmCutoff i hi y hy
  rw [carriedWitnessProtectionQueryTrace]
  simp only [hactive, ↓reduceDIte]
  exact O.replayRoundQueryTrace_contains
    hmLower hmCutoff hi hy

/-- On an inactive round the finite trace contains all consistency queries
needed to determine that the active set is empty. -/
theorem carriedWitnessProtectionQueryTrace_covers_inactive
    (state : CarriedWitnessProtectionState) (x t : ℕ)
    (hinactive :
      ¬O.HasReplayActive
        (witnessProtectionSureUpdate
          ⟨state.sure, state.pastOutputs, state.output⟩ x) t) :
    let sure :=
      witnessProtectionSureUpdate
        ⟨state.sure, state.pastOutputs, state.output⟩ x
    O.carriedWitnessProtectionProcessRound state x t = (
        let out := witnessProtectionFallback sure
        ⟨sure, insert out state.pastOutputs, state.cutoff, out⟩) ∧
      (O.carriedWitnessProtectionQueryTrace state x t).card ≤
        t * sure.card ∧
      ∀ i, i < t → ∀ y, y ∈ sure →
        ((i, y), O.query i y) ∈
          O.carriedWitnessProtectionQueryTrace state x t := by
  dsimp only
  constructor
  · simp [carriedWitnessProtectionProcessRound, hinactive]
  constructor
  · rw [carriedWitnessProtectionQueryTrace]
    simp only [hinactive, ↓reduceDIte]
    simpa using O.replayStageQueryTrace_card_le
      (witnessProtectionSureUpdate
        ⟨state.sure, state.pastOutputs, state.output⟩ x) t 0
  intro i hi y hy
  rw [carriedWitnessProtectionQueryTrace]
  simp only [hinactive, ↓reduceDIte]
  rw [replayStageQueryTrace, Finset.mem_image]
  refine ⟨(i, y), replayStageQueryPlan_contains_sure hi hy, rfl⟩

/-- Operational finite-query property of the literal Algorithm 2
transition.  A finite valid trace exists at every round; it covers either the
inactive consistency test or every finite test through the terminating
active cutoff. -/
def CarriedWitnessProtectionUsesFiniteQueries : Prop :=
  ∀ state : CarriedWitnessProtectionState, ∀ x t : ℕ,
    ∃ trace : ReplayMembershipTrace,
      O.ReplayMembershipTraceValid trace ∧
      (∀ P : GenLimit.OracleFamily,
        P.ReplayMembershipTraceValid trace →
          P.carriedWitnessProtectionProcessRound state x t =
            O.carriedWitnessProtectionProcessRound state x t) ∧
      (if hactive :
          O.HasReplayActive
            (witnessProtectionSureUpdate
              ⟨state.sure, state.pastOutputs, state.output⟩ x) t then
        let sure :=
          witnessProtectionSureUpdate
            ⟨state.sure, state.pastOutputs, state.output⟩ x
        let lower := replayCarriedStart state x
        let cutoff :=
          O.replayCarriedRoundCutoff
            sure state.pastOutputs t lower hactive
        O.carriedWitnessProtectionProcessRound state x t = (
            let out :=
              O.replayCarriedRoundOutput
                sure state.pastOutputs t lower hactive
            ⟨sure, insert out state.pastOutputs, cutoff, out⟩) ∧
          lower ≤ cutoff ∧
          trace.card ≤ t * (sure.card + cutoff) ∧
          ∀ m, lower ≤ m → m ≤ cutoff →
            ∀ i, i < t → ∀ y, y ∈ sure ∨ y < m →
              ((i, y), O.query i y) ∈ trace
       else
        let sure :=
          witnessProtectionSureUpdate
            ⟨state.sure, state.pastOutputs, state.output⟩ x
        O.carriedWitnessProtectionProcessRound state x t = (
            let out := witnessProtectionFallback sure
            ⟨sure, insert out state.pastOutputs, state.cutoff, out⟩) ∧
          trace.card ≤ t * sure.card ∧
          ∀ i, i < t → ∀ y, y ∈ sure →
            ((i, y), O.query i y) ∈ trace)

/-- Every literal carried-cutoff transition has a valid finite membership-
query realization. -/
theorem carriedWitnessProtection_usesFiniteQueries :
    O.CarriedWitnessProtectionUsesFiniteQueries := by
  intro state x t
  refine ⟨O.carriedWitnessProtectionQueryTrace state x t,
    O.carriedWitnessProtectionQueryTrace_valid state x t, ?_, ?_⟩
  · intro P hP
    exact O.carriedWitnessProtectionProcessRound_eq_of_trace
      P state x t hP
  by_cases hactive :
      O.HasReplayActive
        (witnessProtectionSureUpdate
          ⟨state.sure, state.pastOutputs, state.output⟩ x) t
  · simp only [hactive, ↓reduceDIte]
    exact O.carriedWitnessProtectionQueryTrace_covers_active
      state x t hactive
  · simp only [hactive, ↓reduceDIte]
    exact O.carriedWitnessProtectionQueryTrace_covers_inactive
      state x t hactive

/-- Theorem 6.1 on the normalized natural-number domain, combining the
complete semantic correctness theorem with the explicit finite-query
realization of its literal carried-cutoff transition. -/
theorem theorem_6_1_finite_query :
    IsLimitReplayGenerator O.carriedWitnessProtectionGenerator
        (Set.range O.language) ∧
      O.CarriedWitnessProtectionUsesFiniteQueries :=
  ⟨O.theorem_6_1_carried,
    O.carriedWitnessProtection_usesFiniteQueries⟩

end OracleFamily

namespace Replay

/-- Paper-facing finite-query form of Theorem 6.1 on the source's normalized
natural-number universe. -/
theorem theorem_6_1_finite_query (O : GenLimit.OracleFamily) :
    IsLimitReplayGenerator O.carriedWitnessProtectionGenerator
        (Set.range O.language) ∧
      O.CarriedWitnessProtectionUsesFiniteQueries :=
  O.theorem_6_1_finite_query

end Replay
end GenLimit
