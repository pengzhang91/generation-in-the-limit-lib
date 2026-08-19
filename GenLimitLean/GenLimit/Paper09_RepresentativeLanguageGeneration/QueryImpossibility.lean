import GenLimit.Paper09_RepresentativeLanguageGeneration.FiniteQueryImpossibility
import GenLimit.Support.Fresh

/-!
# Representative generation from finite membership queries: Lemma 4.9

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Lemma 4.9 and Appendix D.4.

This module completes the infinitary diagonal whose finite-transcript core is
proved in `FiniteQueryImpossibility`.  The proof fixes the target to
`Set.univ` and adversarially constructs only the first set of a binary
partition.

At round `n`, the construction appends the scheduled point `n` and a fresh
first-group point.  It then runs the alleged universal algorithm against the
current finite first-group completion.  Every queried point outside that
completion is permanently blocked from the first group.  In addition, a
finite range carrying all but `ε` of the decoded distribution's mass is
blocked.  Such a range exists for every countable discrete distribution,
including distributions with infinite support.

The monotone finite histories determine a limit stream presenting `Set.univ`
exactly, while at least half of every round sample lies in the limiting first
group.  At a late consistency round, the output has zero mass on the
already-seen first-group points.  The finite high-mass block prevents future
first-group points from carrying more than `ε` mass, so the first coordinate
has error strictly larger than `alpha`.

This finite-mass blocking argument is a source-faithful repair of the printed
proof's under-specified FIFO/fairness passage.  It avoids assigning an entire
possibly infinite output support at one stage and does not use computability
of the dialogue transition; consequently the formal theorem is slightly
stronger than the stated computability lower bound.
-/

open scoped ENNReal

namespace GenLimit.RepresentativeGeneration
namespace MembershipQuery

theorem inputPrefix_historyThenFallback
    (history : List ℕ) (fallback : ℕ) :
    inputPrefix
        (GenLimit.Generic.historyThenFallback history fallback)
        history.length =
      history := by
  apply List.ext_get
  · simp [inputPrefix]
  · intro n hn₁ hn₂
    simp only [GenLimit.textPrefix, List.get_eq_getElem,
      List.getElem_map, List.getElem_range,
      GenLimit.Generic.historyThenFallback, dif_pos hn₂]

theorem groupMass_coe_finset
    (μ : DiscreteDistribution ℕ) (F : Finset ℕ) :
    groupMass μ (F : Set ℕ) = ∑ x ∈ F, μ.mass x := by
  classical
  rw [groupMass, tsum_eq_sum (s := F)]
  · apply Finset.sum_congr rfl
    intro x hx
    simp [restrictedMass, hx]
  · intro x hx
    simp [restrictedMass, hx]

theorem groupMass_le_groupMass_of_support_imp
    (μ : DiscreteDistribution ℕ) {A B : Set ℕ}
    (h : ∀ x, μ.mass x ≠ 0 → x ∈ A → x ∈ B) :
    groupMass μ A ≤ groupMass μ B := by
  classical
  unfold groupMass
  apply Summable.tsum_le_tsum
  · intro x
    by_cases hxA : x ∈ A
    · by_cases hx0 : μ.mass x = 0
      · simp [restrictedMass, hx0]
      · have hxB := h x hx0 hxA
        simp [restrictedMass, hxA, hxB]
    · by_cases hxB : x ∈ B
      · simpa [restrictedMass, hxA, hxB] using
          μ.mass_nonnegative x
      · simp [restrictedMass, hxA, hxB]
  · exact groupMass_summable μ A
  · exact groupMass_summable μ B

theorem exists_range_mass_gt
    (μ : DiscreteDistribution ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 - ε < ∑ x ∈ Finset.range N, μ.mass x := by
  have htend :
      Filter.Tendsto
        (fun N : ℕ => ∑ x ∈ Finset.range N, μ.mass x)
        Filter.atTop (nhds 1) := by
    have h := μ.summable_mass.hasSum.tendsto_sum_nat
    simpa [μ.total_mass] using h
  have hevent :
      ∀ᶠ N : ℕ in Filter.atTop,
        1 - ε < ∑ x ∈ Finset.range N, μ.mass x :=
    (tendsto_order.1 htend).1 _ (sub_lt_self 1 hε)
  exact Filter.Eventually.exists hevent

theorem exists_range_compl_mass_lt
    (μ : DiscreteDistribution ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ,
      groupMass μ ((Finset.range N : Set ℕ)ᶜ) < ε := by
  obtain ⟨N, hN⟩ := exists_range_mass_gt μ hε
  refine ⟨N, ?_⟩
  have hadd :=
    groupMass_add_compl μ (Finset.range N : Set ℕ)
  rw [groupMass_coe_finset] at hadd
  linarith

/-- The finite blocking estimate used at a late, consistent round. -/
theorem final_firstGroup_mass_lt
    (μ : DiscreteDistribution ℕ)
    (sample currentFirst blockedRange : Finset ℕ)
    (finalFirst : Set ℕ) {ε : ℝ}
    (hsupport :
      SupportedOn μ ((Set.univ : Set ℕ) \ (sample : Set ℕ)))
    (hcurrentSeen : currentFirst ⊆ sample)
    (hfutureAvoids :
      ∀ x, x ∈ finalFirst → x ∈ blockedRange →
        x ∈ currentFirst)
    (hsmall :
      groupMass μ ((blockedRange : Set ℕ)ᶜ) < ε) :
    groupMass μ finalFirst < ε := by
  apply lt_of_le_of_lt
    (groupMass_le_groupMass_of_support_imp μ ?_) hsmall
  intro x hxmass hxFinal
  have hxUnseen := hsupport x hxmass
  have hxNotCurrent : x ∉ currentFirst := by
    intro hxCurrent
    exact hxUnseen.2 (hcurrentSeen hxCurrent)
  show x ∈ (blockedRange : Set ℕ)ᶜ
  intro hxBlocked
  exact hxNotCurrent (hfutureAvoids x hxFinal hxBlocked)

/-- Once the eventual support condition removes the already-seen first-group
points, blocking a finite high-mass range forces an error strictly above
`alpha` on the first binary coordinate. -/
theorem alpha_lt_groupSupDistance_of_first_mass_lt
    (μ : DiscreteDistribution ℕ) (sample : Finset ℕ)
    (groups : ℕ → Set ℕ) (firstGroup : Set ℕ)
    {alpha ε : ℝ}
    (hgroups0 : groups 0 = firstGroup)
    (halpha : 0 < alpha)
    (hbudget : alpha + ε < 1 / 2)
    (hmass : groupMass μ firstGroup < ε)
    (hemp :
      (1 / 2 : ℝ) ≤
        empiricalGroupProbability sample groups 0) :
    ENNReal.ofReal alpha <
      groupSupDistance μ sample groups := by
  have hmassEmp :
      groupMass μ firstGroup <
        empiricalGroupProbability sample groups 0 := by
    linarith
  have hreal :
      alpha <
        |inducedGroupProbability μ groups 0 -
          empiricalGroupProbability sample groups 0| := by
    rw [inducedGroupProbability, hgroups0,
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hmassEmp))]
    linarith
  have habsPositive :
      0 <
        |inducedGroupProbability μ groups 0 -
          empiricalGroupProbability sample groups 0| := by
    rw [inducedGroupProbability, hgroups0,
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hmassEmp))]
    linarith
  exact
    ((ENNReal.ofReal_lt_ofReal_iff habsPositive).mpr hreal).trans_le
      (coordinate_le_groupSupDistance μ sample groups 0)

noncomputable def freshOutside (F : Finset ℕ) : ℕ :=
  GenLimit.Support.freshFromInfinite Set.univ Set.infinite_univ F

theorem freshOutside_not_mem (F : Finset ℕ) :
    freshOutside F ∉ F :=
  GenLimit.Support.freshFromInfinite_not_mem
    Set.univ Set.infinite_univ F

/-- Finite monotone information carried between adversarial rounds.
`first` consists of permanently first-group points and `blocked` of points
permanently excluded from that group. -/
structure PartialState where
  history : List ℕ
  first : Finset ℕ
  blocked : Finset ℕ
  first_disjoint_blocked : Disjoint first blocked
  history_assigned : history.toFinset ⊆ first ∪ blocked
  first_seen : first ⊆ history.toFinset
  balanced : history.toFinset.card ≤ 2 * first.card

/-- The only termination hypothesis the simplified diagonal construction
uses: every nonempty finite history terminates against every finite first-group
completion, with the target fixed to `univ`. -/
def TerminatesFiniteCompletions
    (M : Algorithm ℕ ℕ) : Prop :=
  ∀ s : PartialState, s.history ≠ [] →
    ∃ output : List (AnsweredQuery ℕ) × ℕ,
      TerminatesWith M Set.univ
        (binaryGroups (s.first : Set ℕ))
        s.history output.1 output.2

theorem terminatesFiniteCompletions_of_universal
    {M : Algorithm ℕ ℕ} {alpha : ℝ}
    (hM : UniversalBinaryAlgorithm M alpha) :
    TerminatesFiniteCompletions M := by
  intro s hs
  let stream :=
    GenLimit.Generic.historyThenFallback s.history 0
  have hlength : 0 < s.history.length :=
    List.length_pos_iff.mpr hs
  have hguarantee :=
    hM.2 Set.univ (s.first : Set ℕ) Set.infinite_univ
  obtain ⟨code, trace, hterm⟩ :=
    hguarantee.1 stream s.history.length hlength
  refine ⟨(trace, code), ?_⟩
  simpa [OutputsAt, stream,
    inputPrefix_historyThenFallback] using hterm

noncomputable def chosenExecution
    (M : Algorithm ℕ ℕ)
  (hterm : TerminatesFiniteCompletions M)
    (s : PartialState) :
    List (AnsweredQuery ℕ) × ℕ :=
  if hs : s.history ≠ [] then
    Classical.choose (hterm s hs)
  else
    ([], 0)

theorem chosenExecution_terminates
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (s : PartialState) (hs : s.history ≠ []) :
    TerminatesWith M Set.univ
      (binaryGroups (s.first : Set ℕ))
      s.history
      (chosenExecution M hterm s).1
      (chosenExecution M hterm s).2 := by
  rw [chosenExecution, dif_pos hs]
  exact Classical.choose_spec (hterm s hs)

noncomputable def chosenCutoff
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (ε : ℝ) (hε : 0 < ε)
    (s : PartialState) : ℕ :=
  Classical.choose
    (exists_range_compl_mass_lt
      (M.decode (chosenExecution M hterm s).2) hε)

theorem chosenCutoff_small
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (ε : ℝ) (hε : 0 < ε)
    (s : PartialState) :
    groupMass
        (M.decode (chosenExecution M hterm s).2)
        ((Finset.range
          (chosenCutoff M hterm ε hε s) : Set ℕ)ᶜ) <
      ε :=
  Classical.choose_spec
    (exists_range_compl_mass_lt
      (M.decode (chosenExecution M hterm s).2) hε)

/-- Query points and a finite high-mass range are permanently blocked from
all future first-group assignments. -/
noncomputable def outputBlocker
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (ε : ℝ) (hε : 0 < ε) :
    ℕ → PartialState → Finset ℕ :=
  fun _ s =>
    queriedPoints (chosenExecution M hterm s).1 ∪
      Finset.range (chosenCutoff M hterm ε hε s)

def initialState : PartialState where
  history := []
  first := ∅
  blocked := ∅
  first_disjoint_blocked := by simp
  history_assigned := by simp
  first_seen := by simp
  balanced := by simp

/-- Put the scheduled coverage point in the blocked side unless its status was
already permanently first-group. -/
def coverBlocked (s : PartialState) (n : ℕ) : Finset ℕ :=
  if n ∈ s.first then s.blocked else insert n s.blocked

/-- The fresh first-group point paired with coverage point `n`. -/
noncomputable def roundFresh (s : PartialState) (n : ℕ) : ℕ :=
  freshOutside (s.first ∪ coverBlocked s n)

theorem roundFresh_not_first (s : PartialState) (n : ℕ) :
    roundFresh s n ∉ s.first := by
  intro h
  exact freshOutside_not_mem (s.first ∪ coverBlocked s n)
    (Finset.mem_union_left _ h)

theorem roundFresh_not_coverBlocked (s : PartialState) (n : ℕ) :
    roundFresh s n ∉ coverBlocked s n := by
  intro h
  exact freshOutside_not_mem (s.first ∪ coverBlocked s n)
    (Finset.mem_union_right _ h)

theorem disjoint_first_coverBlocked (s : PartialState) (n : ℕ) :
    Disjoint s.first (coverBlocked s n) := by
  rw [Finset.disjoint_left]
  intro x hxFirst
  simp only [coverBlocked]
  split
  · exact (Finset.disjoint_left.mp s.first_disjoint_blocked)
      hxFirst
  · simp only [Finset.mem_insert]
    rintro (rfl | hxBlocked)
    · contradiction
    · exact (Finset.disjoint_left.mp s.first_disjoint_blocked)
        hxFirst hxBlocked

/-- Prepare round `n`: append the scheduled coverage point and a fresh
first-group point.  Query/output-dependent blocking is added afterwards. -/
noncomputable def prepareRound
    (s : PartialState) (n : ℕ) : PartialState where
  history := s.history ++ [n, roundFresh s n]
  first := insert (roundFresh s n) s.first
  blocked := coverBlocked s n
  first_disjoint_blocked := by
    rw [Finset.disjoint_left]
    intro x hxFirst
    simp only [Finset.mem_insert] at hxFirst
    rcases hxFirst with rfl | hxOld
    · exact roundFresh_not_coverBlocked s n
    · exact
        (Finset.disjoint_left.mp
          (disjoint_first_coverBlocked s n)) hxOld
  history_assigned := by
    intro x hx
    have hxList : x ∈ s.history ++ [n, roundFresh s n] :=
      List.mem_toFinset.mp hx
    have hcases :
        x ∈ s.history ∨ x = n ∨ x = roundFresh s n := by
      simpa using hxList
    rcases hcases with hxOld | hxn | hxa
    · have hxAssigned :=
        s.history_assigned (List.mem_toFinset.mpr hxOld)
      rcases Finset.mem_union.mp hxAssigned with hxFirst | hxBlocked
      · exact Finset.mem_union_left _
          (Finset.mem_insert_of_mem hxFirst)
      · by_cases hnFirst : n ∈ s.first
        · exact Finset.mem_union_right _ (by
            simpa [coverBlocked, hnFirst] using hxBlocked)
        · exact Finset.mem_union_right _ (by
            simp [coverBlocked, hnFirst, hxBlocked])
    · rw [hxn]
      by_cases hnFirst : n ∈ s.first
      · exact Finset.mem_union_left _
          (Finset.mem_insert_of_mem hnFirst)
      · exact Finset.mem_union_right _
          (by simp [coverBlocked, hnFirst])
    · rw [hxa]
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  first_seen := by
    intro x hx
    rw [Finset.mem_insert] at hx
    apply List.mem_toFinset.mpr
    rw [List.mem_append]
    rcases hx with rfl | hxOld
    · exact Or.inr (by simp)
    · exact Or.inl (List.mem_toFinset.mp (s.first_seen hxOld))
  balanced := by
    have hcardAppend :
        (s.history ++ [n, roundFresh s n]).toFinset.card ≤
          s.history.toFinset.card + 2 := by
      rw [List.toFinset_append]
      calc
        (s.history.toFinset ∪ [n, roundFresh s n].toFinset).card
            ≤ s.history.toFinset.card +
                [n, roundFresh s n].toFinset.card :=
          Finset.card_union_le _ _
        _ ≤ s.history.toFinset.card + 2 := by
          have hcard :=
            List.toFinset_card_le [n, roundFresh s n]
          norm_num at hcard ⊢
          omega
    have hbalanced := s.balanced
    rw [Finset.card_insert_of_notMem
      (roundFresh_not_first s n)]
    omega

/-- Add any finite query/output block on the second side.  Existing
first-group assignments are removed from the requested block. -/
def addBlock (s : PartialState) (F : Finset ℕ) : PartialState where
  history := s.history
  first := s.first
  blocked := s.blocked ∪ (F \ s.first)
  first_disjoint_blocked := by
    rw [Finset.disjoint_left]
    intro x hxFirst
    simp only [Finset.mem_union, Finset.mem_sdiff]
    rintro (hxBlocked | ⟨_, hxNotFirst⟩)
    · exact
        (Finset.disjoint_left.mp s.first_disjoint_blocked)
          hxFirst hxBlocked
    · exact hxNotFirst hxFirst
  history_assigned := by
    intro x hx
    have hxAssigned := s.history_assigned hx
    rcases Finset.mem_union.mp hxAssigned with hxFirst | hxBlocked
    · exact Finset.mem_union_left _ hxFirst
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ hxBlocked)
  first_seen := s.first_seen
  balanced := s.balanced

/-- Pure omega-stage recursion, parameterized by the finite set which the
query/output analysis asks to block after each prepared round. -/
noncomputable def states
    (blocker : ℕ → PartialState → Finset ℕ) :
    ℕ → PartialState
  | 0 => initialState
  | n + 1 =>
      let mid := prepareRound (states blocker n) n
      addBlock mid (blocker n mid)

noncomputable def midState
    (blocker : ℕ → PartialState → Finset ℕ)
    (n : ℕ) : PartialState :=
  prepareRound (states blocker n) n

theorem states_succ
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    states blocker (n + 1) =
      addBlock (midState blocker n)
        (blocker n (midState blocker n)) := by
  rfl

theorem state_first_mono_succ
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    (states blocker n).first ⊆
      (states blocker (n + 1)).first := by
  intro x hx
  rw [states_succ]
  exact Finset.mem_insert_of_mem hx

theorem state_blocked_mono_succ
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    (states blocker n).blocked ⊆
      (states blocker (n + 1)).blocked := by
  intro x hx
  rw [states_succ]
  apply Finset.mem_union_left
  change x ∈ coverBlocked (states blocker n) n
  unfold coverBlocked
  split
  · exact hx
  · exact Finset.mem_insert_of_mem hx

theorem state_history_succ
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    (states blocker (n + 1)).history =
      (states blocker n).history ++
        [n, roundFresh (states blocker n) n] := by
  rfl

theorem state_history_length
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    (states blocker n).history.length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [state_history_succ, List.length_append, ih]
      simp
      omega

theorem state_first_mono
    (blocker : ℕ → PartialState → Finset ℕ)
    {n m : ℕ} (hnm : n ≤ m) :
    (states blocker n).first ⊆
      (states blocker m).first := by
  induction m, hnm using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ m hnm ih =>
      exact Finset.Subset.trans ih
        (state_first_mono_succ blocker m)

theorem state_blocked_mono
    (blocker : ℕ → PartialState → Finset ℕ)
    {n m : ℕ} (hnm : n ≤ m) :
    (states blocker n).blocked ⊆
      (states blocker m).blocked := by
  induction m, hnm using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ m hnm ih =>
      exact Finset.Subset.trans ih
        (state_blocked_mono_succ blocker m)

/-- Limit first group determined by the monotone finite assignments. -/
def limitFirst
    (blocker : ℕ → PartialState → Finset ℕ) : Set ℕ :=
  {x | ∃ n, x ∈ (states blocker n).first}

theorem state_first_subset_limitFirst
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    ((states blocker n).first : Set ℕ) ⊆
      limitFirst blocker := by
  intro x hx
  exact ⟨n, hx⟩

theorem state_blocked_disjoint_limitFirst
    (blocker : ℕ → PartialState → Finset ℕ)
    (n : ℕ) :
    Disjoint ((states blocker n).blocked : Set ℕ)
      (limitFirst blocker) := by
  rw [Set.disjoint_left]
  intro x hxBlocked hxLimit
  obtain ⟨m, hxFirst⟩ := hxLimit
  by_cases hnm : n ≤ m
  · have hxBlockedM :=
      state_blocked_mono blocker hnm hxBlocked
    exact
      (Finset.disjoint_left.mp
        (states blocker m).first_disjoint_blocked)
        hxFirst hxBlockedM
  · have hmn : m ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hnm)
    have hxFirstN := state_first_mono blocker hmn hxFirst
    exact
      (Finset.disjoint_left.mp
        (states blocker n).first_disjoint_blocked)
        hxFirstN hxBlocked

theorem blocker_sdiff_first_subset_next_blocked
    (blocker : ℕ → PartialState → Finset ℕ)
    (n : ℕ) :
    blocker n (midState blocker n) \
          (midState blocker n).first ⊆
      (states blocker (n + 1)).blocked := by
  rw [states_succ]
  exact Finset.subset_union_right

theorem state_history_prefix_succ
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    (states blocker n).history <+:
      (states blocker (n + 1)).history := by
  rw [state_history_succ]
  exact List.prefix_append _ _

theorem state_history_prefix
    (blocker : ℕ → PartialState → Finset ℕ)
    {n m : ℕ} (hnm : n ≤ m) :
    (states blocker n).history <+:
      (states blocker m).history := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m hnm ih =>
      exact ih.trans (state_history_prefix_succ blocker m)

/-- The unique infinite stream determined by the nested finite histories. -/
noncomputable def limitStream
    (blocker : ℕ → PartialState → Finset ℕ) :
    GenLimit.Generic.Stream ℕ :=
  fun k =>
    (states blocker (k + 1)).history[k]'(by
      rw [state_history_length]
      omega)

theorem limitStream_eq_state_getElem
    (blocker : ℕ → PartialState → Finset ℕ)
    (n k : ℕ) (hk : k < (states blocker n).history.length) :
    limitStream blocker k =
      (states blocker n).history[k] := by
  unfold limitStream
  by_cases hnk : n ≤ k + 1
  · have hp := state_history_prefix blocker hnk
    exact (hp.getElem hk).symm
  · have hkn : k + 1 ≤ n :=
      Nat.le_of_lt (Nat.lt_of_not_ge hnk)
    have hp := state_history_prefix blocker hkn
    have hkShort :
        k < (states blocker (k + 1)).history.length := by
      rw [state_history_length]
      omega
    exact hp.getElem hkShort

theorem limitStream_prefix_agrees
    (blocker : ℕ → PartialState → Finset ℕ)
    (n k : ℕ) (hk : k < (states blocker n).history.length) :
    limitStream blocker k =
      GenLimit.Generic.historyThenFallback
        (states blocker n).history 0 k := by
  rw [limitStream_eq_state_getElem blocker n k hk]
  simp [GenLimit.Generic.historyThenFallback, hk]

theorem sample_limitStream_at_state
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    GenLimit.Generic.sample (limitStream blocker)
        (states blocker n).history.length =
      (states blocker n).history.toFinset := by
  calc
    _ = GenLimit.Generic.sample
        (GenLimit.Generic.historyThenFallback
          (states blocker n).history 0)
        (states blocker n).history.length := by
      apply GenLimit.Generic.sample_eq_of_eq_on_prefix
      intro k hk
      exact limitStream_prefix_agrees blocker n k hk
    _ = _ :=
      GenLimit.Generic.sample_historyThenFallback_length _ _

theorem scheduled_point_mem_state_history
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    n ∈ (states blocker (n + 1)).history := by
  rw [state_history_succ]
  simp

theorem limitStream_presents_univ
    (blocker : ℕ → PartialState → Finset ℕ) :
    GenLimit.Generic.Presents (limitStream blocker)
      (Set.univ : Set ℕ) := by
  apply Set.eq_univ_of_forall
  intro n
  have hnmem := scheduled_point_mem_state_history blocker n
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hnmem
  refine ⟨i, ?_⟩
  rw [limitStream_eq_state_getElem blocker (n + 1) i i.isLt]
  exact hi

theorem empirical_firstGroup_half_of_balanced
    (sample first : Finset ℕ)
    (groups : ℕ → Set ℕ) (firstGroup : Set ℕ)
    (hsample : sample.Nonempty)
    (hfirstSeen : first ⊆ sample)
    (hfirstLimit : (first : Set ℕ) ⊆ firstGroup)
    (hgroups0 : groups 0 = firstGroup)
    (hbalanced : sample.card ≤ 2 * first.card) :
    (1 / 2 : ℝ) ≤
      empiricalGroupProbability sample groups 0 := by
  classical
  rw [empiricalGroupProbability, if_pos hsample]
  have hsubset :
      first ⊆ sample.filter fun x => x ∈ groups 0 := by
    intro x hx
    rw [Finset.mem_filter, hgroups0]
    exact ⟨hfirstSeen hx, hfirstLimit hx⟩
  have hcard :
      first.card ≤
        (sample.filter fun x => x ∈ groups 0).card :=
    Finset.card_le_card hsubset
  have hsamplePos : (0 : ℝ) < sample.card := by
    exact_mod_cast Finset.card_pos.mpr hsample
  rw [le_div_iff₀ hsamplePos]
  have hbalancedReal :
      (sample.card : ℝ) ≤ 2 * first.card := by
    exact_mod_cast hbalanced
  have hcardReal :
      (first.card : ℝ) ≤
        (sample.filter fun x => x ∈ groups 0).card := by
    exact_mod_cast hcard
  nlinarith

theorem state_sample_nonempty
    (blocker : ℕ → PartialState → Finset ℕ)
    (n : ℕ) :
    (states blocker (n + 1)).history.toFinset.Nonempty := by
  rw [state_history_succ]
  simp

theorem empirical_limitFirst_half_at_round
    (blocker : ℕ → PartialState → Finset ℕ)
    (groups : ℕ → Set ℕ)
    (hgroups0 : groups 0 = limitFirst blocker)
    (n : ℕ) :
    (1 / 2 : ℝ) ≤
      empiricalGroupProbability
        (GenLimit.Generic.sample (limitStream blocker)
          (states blocker (n + 1)).history.length)
        groups 0 := by
  rw [sample_limitStream_at_state]
  exact empirical_firstGroup_half_of_balanced
    (states blocker (n + 1)).history.toFinset
    (states blocker (n + 1)).first
    groups (limitFirst blocker)
    (state_sample_nonempty blocker n)
    (states blocker (n + 1)).first_seen
    (state_first_subset_limitFirst blocker (n + 1))
    hgroups0
    (states blocker (n + 1)).balanced

theorem binaryGroups_pointwise_congr
    {A B : Set ℕ} {x : ℕ}
    (hAB : x ∈ A ↔ x ∈ B) (i : ℕ) :
    (x ∈ binaryGroups A i ↔ x ∈ binaryGroups B i) := by
  rcases i with _ | i
  · exact hAB
  · rcases i with _ | i
    · exact not_congr hAB
    · simp [binaryGroups]

theorem inputPrefix_limitStream_at_state
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    inputPrefix (limitStream blocker)
        (states blocker n).history.length =
      (states blocker n).history := by
  apply List.ext_get
  · simp [inputPrefix]
  · intro k hk₁ hk₂
    simpa only [inputPrefix, GenLimit.textPrefix, List.get_eq_getElem,
      List.getElem_map, List.getElem_range] using
      limitStream_eq_state_getElem blocker n k hk₂

theorem midState_history_ne_nil
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    (midState blocker n).history ≠ [] := by
  simp [midState, prepareRound]

theorem midState_first_eq_next
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    (midState blocker n).first =
      (states blocker (n + 1)).first := by
  rfl

theorem midState_history_eq_next
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    (midState blocker n).history =
      (states blocker (n + 1)).history := by
  rfl

theorem midState_first_subset_limitFirst
    (blocker : ℕ → PartialState → Finset ℕ) (n : ℕ) :
    ((midState blocker n).first : Set ℕ) ⊆
      limitFirst blocker := by
  rw [midState_first_eq_next]
  exact state_first_subset_limitFirst blocker (n + 1)

noncomputable abbrev queryBlocker
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (ε : ℝ) (hε : 0 < ε) :=
  outputBlocker M hterm ε hε

theorem queried_point_limitFirst_iff
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (ε : ℝ) (hε : 0 < ε)
    (n x : ℕ)
    (hx :
      x ∈ queriedPoints
        (chosenExecution M hterm
          (midState (queryBlocker M hterm ε hε) n)).1) :
    x ∈ limitFirst (queryBlocker M hterm ε hε) ↔
      x ∈
        (midState (queryBlocker M hterm ε hε) n).first := by
  let blocker := queryBlocker M hterm ε hε
  let mid := midState blocker n
  constructor
  · intro hxLimit
    by_contra hxNotFirst
    have hxOutputBlock :
        x ∈ blocker n mid := by
      exact Finset.mem_union_left _ hx
    have hxDiff :
        x ∈ blocker n mid \ mid.first :=
      Finset.mem_sdiff.mpr ⟨hxOutputBlock, hxNotFirst⟩
    have hxBlockedNext :
        x ∈ (states blocker (n + 1)).blocked :=
      blocker_sdiff_first_subset_next_blocked blocker n hxDiff
    exact
      Set.disjoint_left.mp
        (state_blocked_disjoint_limitFirst blocker (n + 1))
        hxBlockedNext hxLimit
  · intro hxFirst
    exact midState_first_subset_limitFirst blocker n hxFirst

theorem range_point_limitFirst_imp_midFirst
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (ε : ℝ) (hε : 0 < ε)
    (n x : ℕ)
    (hxLimit :
      x ∈ limitFirst (queryBlocker M hterm ε hε))
    (hxRange :
      x ∈ Finset.range
        (chosenCutoff M hterm ε hε
          (midState (queryBlocker M hterm ε hε) n))) :
    x ∈ (midState
      (queryBlocker M hterm ε hε) n).first := by
  let blocker := queryBlocker M hterm ε hε
  let mid := midState blocker n
  by_contra hxNotFirst
  have hxOutputBlock :
      x ∈ blocker n mid := by
    exact Finset.mem_union_right _ hxRange
  have hxDiff :
      x ∈ blocker n mid \ mid.first :=
    Finset.mem_sdiff.mpr ⟨hxOutputBlock, hxNotFirst⟩
  have hxBlockedNext :
      x ∈ (states blocker (n + 1)).blocked :=
    blocker_sdiff_first_subset_next_blocked blocker n hxDiff
  exact
    Set.disjoint_left.mp
      (state_blocked_disjoint_limitFirst blocker (n + 1))
      hxBlockedNext hxLimit

theorem chosenExecution_terminates_limit
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) :
    let blocker := queryBlocker M hterm ε hε
    let mid := midState blocker n
    TerminatesWith M Set.univ
      (binaryGroups (limitFirst blocker))
      mid.history
      (chosenExecution M hterm mid).1
      (chosenExecution M hterm mid).2 := by
  dsimp only
  let blocker := queryBlocker M hterm ε hε
  let mid := midState blocker n
  have hcompletion :=
    chosenExecution_terminates M hterm mid
      (midState_history_ne_nil blocker n)
  refine ⟨traceValid_of_agree_on_queried
    hcompletion.1 ?_ ?_, hcompletion.2⟩
  · intro x _
    simp
  · intro i x hx
    exact binaryGroups_pointwise_congr
      (queried_point_limitFirst_iff
        M hterm ε hε n x hx).symm i

theorem chosenExecution_outputsAt_limit
    (M : Algorithm ℕ ℕ)
    (hterm : TerminatesFiniteCompletions M)
    (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) :
    let blocker := queryBlocker M hterm ε hε
    let mid := midState blocker n
    OutputsAt M Set.univ
      (binaryGroups (limitFirst blocker))
      (limitStream blocker) mid.history.length
      (chosenExecution M hterm mid).2 := by
  dsimp only
  let blocker := queryBlocker M hterm ε hε
  let mid := midState blocker n
  refine ⟨(chosenExecution M hterm mid).1, ?_⟩
  have hp :
      inputPrefix (limitStream blocker) mid.history.length =
        mid.history := by
    rw [midState_history_eq_next blocker n]
    exact inputPrefix_limitStream_at_state blocker (n + 1)
  rw [hp]
  exact chosenExecution_terminates_limit M hterm ε hε n

/-- Full target-`univ` diagonal.  This is stronger than Lemma 4.9's stated
computability lower bound: computability of the dialogue is never used. -/
theorem finiteQuery_impossibility_via_finite_mass_blocking
    (alpha : ℝ) (halpha : 0 < alpha)
    (halphaHalf : alpha < 1 / 2) :
    ¬ ∃ M : Algorithm ℕ ℕ,
      UniversalBinaryAlgorithm M alpha := by
  rintro ⟨M, hM⟩
  let ε : ℝ := (1 / 2 - alpha) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hbudget : alpha + ε < 1 / 2 := by
    dsimp [ε]
    linarith
  let hterm : TerminatesFiniteCompletions M :=
    terminatesFiniteCompletions_of_universal hM
  let blocker := queryBlocker M hterm ε hε
  let firstGroup := limitFirst blocker
  let groups := binaryGroups firstGroup
  let stream := limitStream blocker
  have hguarantee :
      AlphaLimitGuarantee M Set.univ groups alpha := by
    exact hM.2 Set.univ firstGroup Set.infinite_univ
  have hpresents :
      GenLimit.Generic.Presents stream (Set.univ : Set ℕ) := by
    exact limitStream_presents_univ blocker
  obtain ⟨T, hconsistent⟩ :=
    hguarantee.2.2 stream hpresents
  let mid := midState blocker T
  let code := (chosenExecution M hterm mid).2
  have houtput :
      OutputsAt M Set.univ groups stream
        mid.history.length code := by
    exact chosenExecution_outputsAt_limit
      M hterm ε hε T
  have htimePositive : 0 < mid.history.length := by
    exact List.length_pos_iff.mpr
      (midState_history_ne_nil blocker T)
  have hTtime : T ≤ mid.history.length := by
    rw [midState_history_eq_next blocker T,
      state_history_length]
    omega
  have hsupport :
      SupportedOn (M.decode code)
        ((Set.univ : Set ℕ) \
          (GenLimit.Generic.sample stream
            mid.history.length : Set ℕ)) :=
    hconsistent mid.history.length hTtime code houtput
  have hsample :
      GenLimit.Generic.sample stream mid.history.length =
        mid.history.toFinset := by
    rw [midState_history_eq_next blocker T]
    exact sample_limitStream_at_state blocker (T + 1)
  have hcurrentSeen :
      mid.first ⊆
        GenLimit.Generic.sample stream mid.history.length := by
    rw [hsample]
    exact mid.first_seen
  have hmass :
      groupMass (M.decode code) firstGroup < ε := by
    apply final_firstGroup_mass_lt
      (M.decode code)
      (GenLimit.Generic.sample stream mid.history.length)
      mid.first
      (Finset.range
        (chosenCutoff M hterm ε hε mid))
      firstGroup
      hsupport hcurrentSeen
    · intro x hxLimit hxRange
      exact range_point_limitFirst_imp_midFirst
        M hterm ε hε T x hxLimit hxRange
    · exact chosenCutoff_small M hterm ε hε mid
  have hemp :
      (1 / 2 : ℝ) ≤
        empiricalGroupProbability
          (GenLimit.Generic.sample stream mid.history.length)
          groups 0 := by
    have h :=
      empirical_limitFirst_half_at_round
        blocker groups rfl T
    simpa [mid, stream] using h
  have hlower :
      ENNReal.ofReal alpha <
        groupSupDistance (M.decode code)
          (GenLimit.Generic.sample stream mid.history.length)
          groups :=
    alpha_lt_groupSupDistance_of_first_mass_lt
      (M.decode code)
      (GenLimit.Generic.sample stream mid.history.length)
      groups firstGroup rfl halpha hbudget hmass hemp
  have hupper :
      groupSupDistance (M.decode code)
          (GenLimit.Generic.sample stream mid.history.length)
          groups ≤
        ENNReal.ofReal alpha :=
    hguarantee.2.1 stream mid.history.length
      htimePositive code houtput
  exact (not_lt_of_ge hupper) hlower

theorem finiteQuery_impossibility :
    finiteQuery_impossibility_statement := by
  intro alpha halpha halphaHalf
  exact finiteQuery_impossibility_via_finite_mass_blocking
    alpha halpha halphaHalf

end MembershipQuery
end GenLimit.RepresentativeGeneration
