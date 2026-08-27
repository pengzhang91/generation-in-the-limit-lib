import GenLimit.Paper15_PartialEnumeration.RuleTwoReset
import GenLimit.Paper15_PartialEnumeration.ElementSemiIndex

/-!
# A raw-index stuttering realization of Algorithm 1

This module realizes the two local transition forms from
`RuleTwoReset.lean` as one total semantic recursion on uncompressed
original-index consistency-intersection chains.  It proves the paper's
theorem-level conclusions, but it is not a round-for-round copy of the
displayed compressed-list algorithm: eliminated original indices can add
stuttering rounds, and the initial `k* = 0` fallback is totalized at raw
scope one.

At an unchanged chain, the cursor advances by one exactly when the next
intersection is infinite.  At a changed chain, the cursor uses the source's
largest positive stable infinite position; before the target prefix
stabilizes, the source's `k* = 0` case is totalized by choosing the first
positive position.  After stabilization, the target prefix itself is an
eligible positive reset, so that fallback disappears.

The resulting run supplies an explicit global witness for Lemma 2.5:
the cursor reaches the stable target prefix, every later transition has one
of the two source forms, and identified intersections are therefore
eventually valid and pairwise comparable.  The final section proves the
source's full-infinitely-often dichotomy directly from presentations.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration

/-- The chain at time `t`, with a dummy cursor.  Rule 2 depends only on the
two chains, not on their cursor fields. -/
def consistencyChainState
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    IdentifiedIntersectionState :=
  consistencyIntersectionState C stream t 0

/-- A zero-based, raw-index stuttering realization of Algorithm 1.

Repeated adjacent intersections created by inconsistent original indices do
not affect the selected set.  They only make the stable branch spend an
additional round advancing its cursor. -/
noncomputable def algorithmOneChosen
    (C : LanguageFamily) (stream : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => by
      classical
      let old := consistencyChainState C stream t
      let new := consistencyChainState C stream (t + 1)
      exact
        if hChain : new.chain = old.chain then
          if (old.chain
                (algorithmOneChosen C stream t + 1)).Infinite then
            algorithmOneChosen C stream t + 1
          else
            algorithmOneChosen C stream t
        else
          let reset := ruleTwoResetIndex old new
          if reset = 0 then 1 else reset

/-- The complete identified-intersection state produced by the recursion. -/
noncomputable def algorithmOneState
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    IdentifiedIntersectionState :=
  consistencyIntersectionState C stream t
    (algorithmOneChosen C stream t)

@[simp] theorem algorithmOneState_chain
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (algorithmOneState C stream t).chain =
      (consistencyChainState C stream t).chain :=
  rfl

@[simp] theorem algorithmOneState_chosenIndex
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (algorithmOneState C stream t).chosenIndex =
      algorithmOneChosen C stream t :=
  rfl

theorem consistent_mono_time
    {C : LanguageFamily} {stream : ℕ → ℕ} {s t i : ℕ}
    (hst : s ≤ t) (hconsistent : Consistent C stream t i) :
    Consistent C stream s i := by
  intro u hu
  exact hconsistent (sample_mono hst hu)

/-- Once the finite prefix through the target has stabilized, it is an
eligible positive Rule-2 reset position whenever the whole chain changes. -/
theorem targetPrefix_isGreatestReset_lowerBound
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z t : ℕ}
    (hstable :
      prefixIntersection C stream t (z + 1) =
        targetPrefixCore C E z)
    (hstableNext :
      prefixIntersection C stream (t + 1) (z + 1) =
        targetPrefixCore C E z)
    (hE : E.Infinite)
    (hchange :
      (consistencyChainState C stream (t + 1)).chain ≠
        (consistencyChainState C stream t).chain) :
    z + 1 ≤
      ruleTwoResetIndex
        (consistencyChainState C stream t)
        (consistencyChainState C stream (t + 1)) := by
  classical
  let old := consistencyChainState C stream t
  let new := consistencyChainState C stream (t + 1)
  have hcandidate :
      RuleTwoCandidate old new (z + 1) := by
    refine ⟨by omega, ?_, ?_⟩
    · change
        prefixIntersection C stream t (z + 1) =
          prefixIntersection C stream (t + 1) (z + 1)
      rw [hstable, hstableNext]
    · change
        (prefixIntersection C stream t (z + 1)).Infinite
      rw [hstable]
      exact targetPrefixCore_infinite hE
  have hexists :
      ∃ k, IsGreatestRuleTwoCandidate old new k := by
    have helim :
          ∃ i,
            Consistent C stream t i ∧
              ¬Consistent C stream (t + 1) i := by
        by_contra hnone
        push_neg at hnone
        apply hchange
        funext s
        ext u
        constructor
        · intro hnew i hi hold
          exact hnew i hi (hnone i hold)
        · intro hold i hi hnew
          exact hold i hi
            (consistent_mono_time (Nat.le_succ t) hnew)
    let boundary := Nat.find helim
    have hboundary :
          Consistent C stream t boundary ∧
            ¬Consistent C stream (t + 1) boundary :=
      Nat.find_spec helim
    have htailNe :
          ∀ j, boundary < j → old.chain j ≠ new.chain j := by
        intro j hbj heq
        have holdMiss :
            stream t ∉ old.chain j := by
          intro hmem
          apply hboundary.2
          intro u hu
          obtain ⟨s, hs, rfl⟩ := mem_sample_iff.mp hu
          rcases Nat.lt_or_eq_of_le
              (Nat.le_of_lt_succ hs) with hst | rfl
          · exact hboundary.1 (value_mem_sample hst)
          · exact hmem boundary (by omega) hboundary.1
        have hnewMem : stream t ∈ new.chain j := by
          intro i _ hconsistent
          exact hconsistent
            (value_mem_sample (Nat.lt_succ_self t))
        rw [← heq] at hnewMem
        exact holdMiss hnewMem
    have hzBoundary : z + 1 ≤ boundary := by
        by_contra hnot
        exact htailNe (z + 1) (Nat.lt_of_not_ge hnot)
          hcandidate.2.1
    let candidates :=
        (Finset.range (boundary + 1)).filter
          (RuleTwoCandidate old new)
    have hzMem : z + 1 ∈ candidates := by
        simp only [candidates, Finset.mem_filter,
          Finset.mem_range]
        exact ⟨by omega, hcandidate⟩
    let greatest := candidates.max' ⟨z + 1, hzMem⟩
    have hgreatestMem : greatest ∈ candidates :=
      Finset.max'_mem candidates ⟨z + 1, hzMem⟩
    refine ⟨greatest, ?_, ?_⟩
    · exact (Finset.mem_filter.mp hgreatestMem).2
    · intro j hj
      have hjBoundary : j ≤ boundary := by
        by_contra hnot
        exact htailNe j (Nat.lt_of_not_ge hnot) hj.2.1
      apply Finset.le_max'
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hj⟩
  have hspec :=
    ruleTwoResetIndex_spec hexists
  exact hspec.2 (z + 1) hcandidate

/-!
The preceding existence proof is intentionally generic but longer than the
run needs.  The following specialized lemma derives the same reset bound
from an explicit changed-chain hypothesis and is the form used below.
-/

theorem algorithmOneChosen_step_ge_targetPrefix
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z t : ℕ}
    (hstable :
      prefixIntersection C stream t (z + 1) =
        targetPrefixCore C E z)
    (hstableNext :
      prefixIntersection C stream (t + 1) (z + 1) =
        targetPrefixCore C E z)
    (hE : E.Infinite) :
    min (algorithmOneChosen C stream t + 1) (z + 1) ≤
      algorithmOneChosen C stream (t + 1) := by
  rw [algorithmOneChosen]
  dsimp only
  split_ifs with hChain hInfinite hReset
  · omega
  · by_cases hcursor :
        z + 1 ≤ algorithmOneChosen C stream t
    · omega
    have hnextLe :
        algorithmOneChosen C stream t + 1 ≤ z + 1 := by
      omega
    exfalso
    apply hInfinite
    apply hE.mono
    intro u hu i hi hconsistent
    have hiz : i ≤ z := by omega
    have hcore :
        u ∈ prefixIntersection C stream t (z + 1) := by
      rw [hstable]
      exact enumerated_subset_targetPrefixCore C E z hu
    exact hcore i (by omega) hconsistent
  · have hbound :=
      targetPrefix_isGreatestReset_lowerBound
        hstable hstableNext hE hChain
    omega
  · have hbound :=
      targetPrefix_isGreatestReset_lowerBound
        hstable hstableNext hE hChain
    omega

/-- After at most `z+1` stabilized rounds, the recursive cursor reaches the
target prefix and never falls below it. -/
theorem algorithmOneChosen_eventually_ge_targetPrefix
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite) :
    ∃ T, ∀ t, T ≤ t →
      z + 1 ≤ algorithmOneChosen C stream t := by
  obtain ⟨T₀, hT₀⟩ :=
    prefixIntersection_eventually_eq_targetPrefixCore
      (C := C) (stream := stream) (E := E) (z := z) hP
  have hprogress :
      ∀ d, d ≤ z + 1 →
        d ≤ algorithmOneChosen C stream (T₀ + d) := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
        have ih' :
            d ≤ algorithmOneChosen C stream (T₀ + d) :=
          ih (by omega)
        have hstep :=
          algorithmOneChosen_step_ge_targetPrefix
            (hstable := hT₀ (T₀ + d) (by omega))
            (hstableNext := hT₀ (T₀ + d + 1) (by omega))
            hE
        have hleMin :
            d + 1 ≤
              min
                (algorithmOneChosen C stream (T₀ + d) + 1)
                (z + 1) :=
          Nat.le_min.mpr ⟨by omega, hd⟩
        have :
            d + 1 ≤
              algorithmOneChosen C stream (T₀ + d + 1) :=
          hleMin.trans hstep
        simpa [Nat.add_assoc] using this
  let T := T₀ + (z + 1)
  have hbase :
      z + 1 ≤ algorithmOneChosen C stream T := by
    simpa [T] using hprogress (z + 1) (Nat.le_refl _)
  have hpersist :
      ∀ d,
        z + 1 ≤ algorithmOneChosen C stream (T + d) := by
    intro d
    induction d with
    | zero => simpa using hbase
    | succ d ih =>
        have hstep :=
          algorithmOneChosen_step_ge_targetPrefix
            (hstable :=
              hT₀ (T + d) (by
                dsimp [T]
                omega))
            (hstableNext :=
              hT₀ (T + d + 1) (by
                dsimp [T]
                omega))
            hE
        have hmin :
            min
                (algorithmOneChosen C stream (T + d) + 1)
                (z + 1) =
              z + 1 := by
          exact Nat.min_eq_right (by omega)
        have :
            z + 1 ≤
              algorithmOneChosen C stream (T + d + 1) := by
          rw [← hmin]
          exact hstep
        simpa [Nat.add_assoc] using this
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact hpersist d

/-- Lemma 2.5 Item 1 for the concrete recursive run. -/
theorem algorithmOne_eventually_valid
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    ∃ T, ∀ t, T ≤ t →
      (algorithmOneState C stream t).identified ⊆ C z := by
  apply lemma_2_5_item_one_of_targetPrefix_bound hP hEz
    (fun t => (algorithmOneState C stream t).identified)
  obtain ⟨T, hT⟩ :=
    algorithmOneChosen_eventually_ge_targetPrefix
      (C := C) (stream := stream) (E := E) (z := z) hP hE
  refine ⟨T, ?_⟩
  intro t ht
  exact
    (algorithmOneState C stream t).descending (hT t ht)

/-- A nonzero totalized Rule-2 selector necessarily came from an actual
greatest-candidate proof. -/
theorem ruleTwoResetIndex_spec_of_ne_zero
    {old new : IdentifiedIntersectionState}
    (hne : ruleTwoResetIndex old new ≠ 0) :
    IsGreatestRuleTwoCandidate old new
      (ruleTwoResetIndex old new) := by
  classical
  by_cases h :
      ∃ k, IsGreatestRuleTwoCandidate old new k
  · exact ruleTwoResetIndex_spec h
  · simp [ruleTwoResetIndex, h] at hne

/-- Once the target prefix has stabilized, every transition of this
raw-index realization has one of Algorithm 1's two eventual transition
forms. -/
theorem algorithmOneStep_of_stableTargetPrefix
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z t : ℕ}
    (hstable :
      prefixIntersection C stream t (z + 1) =
        targetPrefixCore C E z)
    (hstableNext :
      prefixIntersection C stream (t + 1) (z + 1) =
        targetPrefixCore C E z)
    (hE : E.Infinite) :
    AlgorithmOneStep
      (algorithmOneState C stream t)
      (algorithmOneState C stream (t + 1)) := by
  classical
  let old := consistencyChainState C stream t
  let new := consistencyChainState C stream (t + 1)
  by_cases hChain : new.chain = old.chain
  · apply AlgorithmOneStep.stable
    · exact hChain
    · by_cases hInfinite :
          (old.chain
            (algorithmOneChosen C stream t + 1)).Infinite
      · right
        simp [algorithmOneChosen, old, new, hChain, hInfinite]
      · left
        simp [algorithmOneChosen, old, new, hChain, hInfinite]
  · let reset := ruleTwoResetIndex old new
    have hbound : z + 1 ≤ reset := by
      exact targetPrefix_isGreatestReset_lowerBound
        hstable hstableNext hE hChain
    have hne : reset ≠ 0 := by omega
    have hspec :
        IsGreatestRuleTwoCandidate old new reset := by
      exact ruleTwoResetIndex_spec_of_ne_zero hne
    apply AlgorithmOneStep.positiveReset
      (algorithmOneState C stream t)
      (algorithmOneState C stream (t + 1))
      reset (by omega)
    · exact hspec.1.2.1
    · simp [algorithmOneChosen, old, new, hChain, reset, hne]

/-- Lemma 2.5 Item 2 for the concrete raw-index realization. -/
theorem algorithmOne_eventually_comparable
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite) :
    ∃ T, ∀ t, T ≤ t →
      (algorithmOneState C stream t).identified ⊆
          (algorithmOneState C stream (t + 1)).identified ∨
        (algorithmOneState C stream (t + 1)).identified ⊆
          (algorithmOneState C stream t).identified := by
  obtain ⟨T, hT⟩ :=
    prefixIntersection_eventually_eq_targetPrefixCore
      (C := C) (stream := stream) (E := E) (z := z) hP
  exact lemma_2_5_item_two_comparability
    (fun t => algorithmOneState C stream t)
    ⟨T, fun t ht =>
      algorithmOneStep_of_stableTargetPrefix
        (hT t ht) (hT (t + 1) (by omega)) hE⟩

/-! ## Full intersections occur cofinally -/

/-- A candidate still consistent at `t` but not containing the whole
partially presented set. -/
def NonfullConsistentAt
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (E : Language) (t i : ℕ) : Prop :=
  Consistent C stream t i ∧ ¬E ⊆ C i

/-- If a nonfull candidate remains after the target prefix has stabilized,
the least such candidate is eventually eliminated.  At its first
elimination, the raw-index realization performs an exact full reset. -/
theorem exists_later_full_reset_of_nonfull
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z T₀ t₀ : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hscope :
      ∀ t, T₀ ≤ t → ∀ i, i < z + 1 →
        (Consistent C stream t i ↔ E ⊆ C i))
    (ht₀ : T₀ ≤ t₀)
    (hnonfull : ∃ i, NonfullConsistentAt C stream E t₀ i) :
    ∃ r, t₀ ≤ r ∧
      E ⊆ (algorithmOneState C stream (r + 1)).identified := by
  classical
  let boundary := Nat.find hnonfull
  have hboundary :
      NonfullConsistentAt C stream E t₀ boundary :=
    Nat.find_spec hnonfull
  have hearlier :
      ∀ i, i < boundary →
        Consistent C stream t₀ i → E ⊆ C i := by
    intro i hi hconsistent
    by_contra hnotFull
    exact (Nat.find_min hnonfull hi)
      ⟨hconsistent, hnotFull⟩
  have hpositive : 0 < boundary := by
    have hzlt : z < boundary := by
      by_contra hnot
      have hibound : boundary < z + 1 := by omega
      exact hboundary.2
        ((hscope t₀ ht₀ boundary hibound).mp hboundary.1)
    omega
  obtain ⟨Tbad, hTbad⟩ :=
    eventually_not_consistent_of_not_presented_subset
      (C := C) (stream := stream) hP hboundary.2
  have hexit :
      ∃ q, ¬Consistent C stream (t₀ + q) boundary := by
    exact ⟨Tbad, hTbad (t₀ + Tbad) (by omega)⟩
  let q := Nat.find hexit
  have hqBad :
      ¬Consistent C stream (t₀ + q) boundary :=
    Nat.find_spec hexit
  have hqPositive : 0 < q := by
    by_contra hnot
    have hqZero : q = 0 := by omega
    exact hqBad (by simpa [hqZero] using hboundary.1)
  obtain ⟨p, hq⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hqPositive)
  let r := t₀ + p
  have hOldConsistent :
      Consistent C stream r boundary := by
    have hnotBad :
        ¬¬Consistent C stream (t₀ + p) boundary :=
      Nat.find_min hexit (by omega)
    simpa [r] using Classical.not_not.mp hnotBad
  have hNewInconsistent :
      ¬Consistent C stream (r + 1) boundary := by
    simpa [r, hq, Nat.add_assoc] using hqBad
  have hstreamE : stream r ∈ E := by
    rw [← hP]
    exact ⟨r, rfl⟩
  have hmisses : stream r ∉ C boundary := by
    intro hmem
    apply hNewInconsistent
    intro u hu
    obtain ⟨s, hs, rfl⟩ := mem_sample_iff.mp hu
    rcases Nat.lt_or_eq_of_le
        (Nat.le_of_lt_succ hs) with hsr | rfl
    · exact hOldConsistent (value_mem_sample hsr)
    · exact hmem
  have hearlierSurvive :
      ∀ i, i < boundary →
        Consistent C stream r i → stream r ∈ C i := by
    intro i hi hconsistent
    have holdAtStart :
        Consistent C stream t₀ i :=
      consistent_mono_time (by
        dsimp [r]
        omega) hconsistent
    exact hearlier i hi holdAtStart hstreamE
  have hfullPrefix :
      E ⊆ prefixIntersection C stream r boundary := by
    intro u hu i hi hconsistent
    have holdAtStart :
        Consistent C stream t₀ i :=
      consistent_mono_time (by
        dsimp [r]
        omega) hconsistent
    exact hearlier i hi holdAtStart hu
  have hdata :
      LeftmostEliminationData C stream r boundary :=
    { positive := hpositive
      wasConsistent := hOldConsistent
      missesObservation := hmisses
      earlier_survive := hearlierSurvive
      stableInfinite := hE.mono hfullPrefix }
  have hChainNe :
      (consistencyChainState C stream (r + 1)).chain ≠
        (consistencyChainState C stream r).chain := by
    intro heq
    have heqAt := congrFun heq (boundary + 1)
    exact
      hdata.toObservationSeparatedResetData.tail_ne
        (Nat.lt_succ_self boundary) heqAt.symm
  have hreset :
      ruleTwoResetIndex
          (consistencyChainState C stream r)
          (consistencyChainState C stream (r + 1)) =
        boundary := by
    exact hdata.ruleTwoResetIndex_eq
      (oldChosen := 0) (newChosen := 0)
  have hchosen :
      algorithmOneChosen C stream (r + 1) = boundary := by
    rw [algorithmOneChosen]
    dsimp only
    split
    · next h => exact (hChainNe h).elim
    · rw [hreset, if_neg (Nat.ne_of_gt hpositive)]
  refine ⟨r, by
    dsimp [r]
    omega, ?_⟩
  change
    E ⊆ prefixIntersection C stream (r + 1)
      (algorithmOneChosen C stream (r + 1))
  rw [hchosen]
  exact hdata.reset_identified_full
    (oldChosen := algorithmOneChosen C stream r) hfullPrefix

/-- Lemma 2.5 Item 3 for the concrete recursive run: the identified
intersection contains the whole partially presented set at arbitrarily late
times. -/
theorem algorithmOne_fullInfinitelyOften
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite) :
    FullInfinitelyOften E (algorithmOneState C stream) := by
  classical
  obtain ⟨T₀, hscope⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := C) (stream := stream) (E := E) hP (z + 1)
  by_cases heventual :
      ∃ T, ∀ t, T ≤ t →
        ¬∃ i, NonfullConsistentAt C stream E t i
  · obtain ⟨T, hT⟩ := heventual
    intro start
    let t := max start T
    refine ⟨t, Nat.le_max_left _ _, ?_⟩
    change
      E ⊆ prefixIntersection C stream t
        (algorithmOneChosen C stream t)
    intro u hu i hi hconsistent
    have hfull : E ⊆ C i := by
      by_contra hnotFull
      exact hT t (Nat.le_max_right _ _)
        ⟨i, hconsistent, hnotFull⟩
    exact hfull hu
  · push_neg at heventual
    intro start
    obtain ⟨t₀, ht₀, i, hi⟩ :=
      heventual (max start T₀)
    obtain ⟨r, htr, hfull⟩ :=
      exists_later_full_reset_of_nonfull
        hP hE hscope
        (le_trans (Nat.le_max_right start T₀) ht₀)
        ⟨i, hi⟩
    exact ⟨r + 1, by omega, hfull⟩

/-- The complete three-part Lemma 2.5 package witnessed by the concrete
raw-index stuttering realization. -/
theorem lemma_2_5_concrete_algorithmOne
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    (∃ T, ∀ t, T ≤ t →
        (algorithmOneState C stream t).identified ⊆ C z) ∧
      (∃ T, ∀ t, T ≤ t →
        (algorithmOneState C stream t).identified ⊆
            (algorithmOneState C stream (t + 1)).identified ∨
          (algorithmOneState C stream (t + 1)).identified ⊆
            (algorithmOneState C stream t).identified) ∧
      FullInfinitelyOften E (algorithmOneState C stream) := by
  exact
    ⟨algorithmOne_eventually_valid hP hE hEz,
      algorithmOne_eventually_comparable
        (z := z) hP hE,
      algorithmOne_fullInfinitelyOften
        (z := z) hP hE⟩

/-! ## Source-facing finite semi-index package -/

/-- The finite set of currently consistent original indices whose
intersection is selected by the raw-index realization. -/
noncomputable def algorithmOneIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Finset ℕ := by
  classical
  exact
    (Finset.range (algorithmOneChosen C stream t)).filter
      (Consistent C stream t)

@[simp] theorem mem_algorithmOneIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i : ℕ} :
    i ∈ algorithmOneIndices C stream t ↔
      i < algorithmOneChosen C stream t ∧
        Consistent C stream t i := by
  classical
  simp [algorithmOneIndices]

theorem intersectionOf_algorithmOneIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    intersectionOf C (algorithmOneIndices C stream t) =
      (algorithmOneState C stream t).identified := by
  ext u
  constructor
  · intro hu i hi hconsistent
    exact hu i
      (mem_algorithmOneIndices.mpr ⟨hi, hconsistent⟩)
  · intro hu i hi
    exact hu i
      (mem_algorithmOneIndices.mp hi).1
      (mem_algorithmOneIndices.mp hi).2

/-- Every identified intersection in the recursive run is infinite, under
the paper's standing assumption that every indexed language is infinite. -/
theorem algorithmOne_identified_infinite
    {C : LanguageFamily} {stream : ℕ → ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite) :
    ∀ t, (algorithmOneState C stream t).identified.Infinite := by
  intro t
  induction t with
  | zero =>
      change (prefixIntersection C stream 0 0).Infinite
      simp [Set.infinite_univ]
  | succ t ih =>
      classical
      let old := consistencyChainState C stream t
      let new := consistencyChainState C stream (t + 1)
      by_cases hChain : new.chain = old.chain
      · by_cases hnext :
            (old.chain
              (algorithmOneChosen C stream t + 1)).Infinite
        · have hchosen :
              algorithmOneChosen C stream (t + 1) =
                algorithmOneChosen C stream t + 1 := by
            simp [algorithmOneChosen, old, new,
              hChain, hnext]
          change
            (new.chain
              (algorithmOneChosen C stream (t + 1))).Infinite
          rw [hchosen, hChain]
          exact hnext
        · have hchosen :
              algorithmOneChosen C stream (t + 1) =
                algorithmOneChosen C stream t := by
            simp [algorithmOneChosen, old, new,
              hChain, hnext]
          change
            (new.chain
              (algorithmOneChosen C stream (t + 1))).Infinite
          rw [hchosen, hChain]
          exact ih
      · let reset := ruleTwoResetIndex old new
        by_cases hreset : reset = 0
        · have hchosen :
              algorithmOneChosen C stream (t + 1) = 1 := by
            simp [algorithmOneChosen, old, new,
              hChain, reset, hreset]
          change
            (new.chain
              (algorithmOneChosen C stream (t + 1))).Infinite
          rw [hchosen]
          change
            (prefixIntersection C stream (t + 1) 1).Infinite
          by_cases hconsistent :
              Consistent C stream (t + 1) 0
          · apply (hLanguagesInfinite 0).mono
            intro u hu i hi _
            have hi0 : i = 0 := by omega
            simpa [hi0] using hu
          · apply Set.infinite_univ.mono
            intro u _ i hi hiConsistent
            have hi0 : i = 0 := by omega
            exact (hconsistent (by simpa [hi0] using hiConsistent)).elim
        · have hchosen :
              algorithmOneChosen C stream (t + 1) = reset := by
            simp [algorithmOneChosen, old, new,
              hChain, reset, hreset]
          have hspec :
              IsGreatestRuleTwoCandidate old new reset :=
            ruleTwoResetIndex_spec_of_ne_zero hreset
          change
            (new.chain
              (algorithmOneChosen C stream (t + 1))).Infinite
          rw [hchosen, ← hspec.1.2.1]
          exact hspec.1.2.2

/-- The source-facing strengthened generation theorem following Lemma 2.5:
the recursive algorithm always outputs a finite semi-index with infinite
intersection, is eventually valid, and is accurate at arbitrarily late
times. -/
theorem theorem_2_2_accurate_conjunction
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    (∀ t,
      (intersectionOf C
        (algorithmOneIndices C stream t)).Infinite) ∧
      (∃ T, ∀ t, T ≤ t →
        intersectionOf C
          (algorithmOneIndices C stream t) ⊆ C z) ∧
      (∀ T, ∃ t, T ≤ t ∧
        E ⊆ intersectionOf C
          (algorithmOneIndices C stream t) ∧
        intersectionOf C
          (algorithmOneIndices C stream t) ⊆ C z) := by
  have hinfinite :
      ∀ t,
        (intersectionOf C
          (algorithmOneIndices C stream t)).Infinite := by
    intro t
    rw [intersectionOf_algorithmOneIndices]
    exact algorithmOne_identified_infinite
      hLanguagesInfinite t
  obtain ⟨Tvalid, hvalid⟩ :=
    algorithmOne_eventually_valid hP hE hEz
  have hvalid' :
      ∃ T, ∀ t, T ≤ t →
        intersectionOf C
          (algorithmOneIndices C stream t) ⊆ C z := by
    exact
      ⟨Tvalid, fun t ht => by
        rw [intersectionOf_algorithmOneIndices]
        exact hvalid t ht⟩
  refine ⟨hinfinite, hvalid', ?_⟩
  intro T
  obtain ⟨t, ht, hfull⟩ :=
    algorithmOne_fullInfinitelyOften
      (z := z) hP hE (max T Tvalid)
  refine ⟨t, le_trans (Nat.le_max_left _ _) ht, ?_, ?_⟩
  · rw [intersectionOf_algorithmOneIndices]
    exact hfull
  · rw [intersectionOf_algorithmOneIndices]
    exact hvalid t
      (le_trans (Nat.le_max_right _ _) ht)

/-! ## Source-numbered generation wrappers -/

/-- The fresh element trace obtained from the concrete semi-index run. -/
noncomputable def algorithmOneFreshOutput
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite) :
    ℕ → ℕ :=
  semiIndexFreshOutput C stream
    (algorithmOneIndices C stream)
    (fun t => by
      rw [intersectionOf_algorithmOneIndices]
      exact algorithmOne_identified_infinite
        hLanguagesInfinite t)

theorem algorithmOneFreshOutput_spec
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (t : ℕ) :
    algorithmOneFreshOutput C stream hLanguagesInfinite t ∈
        intersectionOf C (algorithmOneIndices C stream t) ∧
      algorithmOneFreshOutput C stream hLanguagesInfinite t ∉
        sample stream t := by
  simpa [algorithmOneFreshOutput] using
    semiIndexFreshOutput_spec C stream
      (algorithmOneIndices C stream)
      (fun s => by
        rw [intersectionOf_algorithmOneIndices]
        exact algorithmOne_identified_infinite
          hLanguagesInfinite s)
      t

/-- Theorem 2.4 in the paper's semi-index formulation, witnessed by the
raw-index stuttering realization: every finite conjunction is infinite,
the conjunctions are eventually target-valid, and they contain the entire
partially enumerated set at arbitrarily late times. -/
theorem theorem_2_4_semiIndex
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    SemiIndexTraceGenerates C
        (algorithmOneIndices C stream) z ∧
      ∀ T, ∃ t, T ≤ t ∧
        E ⊆ intersectionOf C
          (algorithmOneIndices C stream t) := by
  obtain ⟨hinfinite, hvalid, hfull⟩ :=
    theorem_2_2_accurate_conjunction
      hLanguagesInfinite hP hE hEz
  refine ⟨⟨hinfinite, hvalid⟩, ?_⟩
  intro T
  obtain ⟨t, ht, hEt, _⟩ := hfull T
  exact ⟨t, ht, hEt⟩

/-- The element-trace consequence induced by Theorem 2.4 and the reverse
direction of Lemma 2.3.  Its output is unseen in the adversary sample at
every round and target-valid after a finite time. -/
theorem theorem_2_2_freshOutput
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    ElementTraceGenerates C stream
      (algorithmOneFreshOutput C stream hLanguagesInfinite) z := by
  have hsemi :
      SemiIndexTraceGenerates C
        (algorithmOneIndices C stream) z :=
    (theorem_2_4_semiIndex
      hLanguagesInfinite hP hE hEz).1
  simpa [algorithmOneFreshOutput] using
    lemma_2_3_semiIndex_to_element
      (stream := stream) hsemi

/-- Overview Theorem 1.8: conjunction-based generation whose identified
intersection contains the adversary's infinite partial enumeration at
arbitrarily late times. -/
theorem theorem_1_8
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    SemiIndexTraceGenerates C
        (algorithmOneIndices C stream) z ∧
      ∀ T, ∃ t, T ≤ t ∧
        E ⊆ intersectionOf C
          (algorithmOneIndices C stream t) :=
  theorem_2_4_semiIndex hLanguagesInfinite hP hE hEz

end PartialEnumeration
end KleinbergWei
end GenLimit
