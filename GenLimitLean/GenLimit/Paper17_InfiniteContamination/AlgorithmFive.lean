import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper17_InfiniteContamination.PriorityStabilization

/-!
# Algorithm 5 and set-based upper density

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Algorithm 5, Proposition 6.3, and Theorem 6.1.

At time `t`, `algorithmFiveIndices` takes the longest prefix of the current
active family whose membership did not change since time `t - 1` and whose
common intersection is infinite.  The set generator outputs that common core
minus the observed finite sample.  The proof below formalizes the paper's
fall-back argument: if the current core fails to contain the noiseless
enumerated subset, the first bad selected language eventually becomes
inconsistent; at that transition the maximal stable prefix falls back exactly
before it, and hence contains the entire enumerated subset.
-/

namespace GenLimit.InfiniteContamination

open Filter
open GenLimit.KleinbergWei

/-- A language is active when it lies in the current finite scope and is
consistent with every observation seen so far. -/
noncomputable def algorithmFiveActiveIndices
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter fun i =>
    (↑(GenLimit.Generic.sample stream t) : Set ℕ) ⊆ family i

@[simp] theorem mem_algorithmFiveActiveIndices
    {family : ℕ → Set ℕ}
    {stream : GenLimit.Generic.Stream ℕ} {t i : ℕ} :
    i ∈ algorithmFiveActiveIndices family stream t ↔
      i < t ∧
        (↑(GenLimit.Generic.sample stream t) : Set ℕ) ⊆ family i := by
  classical
  simp [algorithmFiveActiveIndices]

/-- Active languages among the first `k` family indices. -/
noncomputable def algorithmFivePrefixIndices
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t k : ℕ) : Finset ℕ :=
  algorithmFiveActiveIndices family stream t ∩ Finset.range k

@[simp] theorem mem_algorithmFivePrefixIndices
    {family : ℕ → Set ℕ}
    {stream : GenLimit.Generic.Stream ℕ} {t k i : ℕ} :
    i ∈ algorithmFivePrefixIndices family stream t k ↔
      i < t ∧ i < k ∧
        (↑(GenLimit.Generic.sample stream t) : Set ℕ) ⊆ family i := by
  classical
  simp only [algorithmFivePrefixIndices, Finset.mem_inter,
    mem_algorithmFiveActiveIndices, Finset.mem_range]
  tauto

/-- Membership of all candidates below `k` agrees between the two successive
active sets used by Algorithm 5. -/
def AlgorithmFiveStableThrough
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t k : ℕ) : Prop :=
  ∀ i, i < k →
    (i ∈ algorithmFiveActiveIndices family stream t ↔
      i ∈ algorithmFiveActiveIndices family stream (t - 1))

/-- The largest stable cutoff with infinite common intersection. -/
noncomputable def algorithmFiveCutoff
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k =>
      AlgorithmFiveStableThrough family stream t k ∧
        (finiteCommonCore
          (indexedLanguages family
            (algorithmFivePrefixIndices family stream t k))).Infinite)
    t

/-- Algorithm 5's selected active prefix. -/
noncomputable def algorithmFiveIndices
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) : Finset ℕ :=
  algorithmFivePrefixIndices family stream t
    (algorithmFiveCutoff family stream t)

theorem algorithmFiveCutoff_le
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    algorithmFiveCutoff family stream t ≤ t := by
  classical
  exact Nat.findGreatest_le t

theorem algorithmFive_zero_candidate
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    AlgorithmFiveStableThrough family stream t 0 ∧
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFivePrefixIndices family stream t 0))).Infinite := by
  constructor
  · intro i hi
    omega
  · simp [algorithmFivePrefixIndices, indexedLanguages,
      finiteCommonCore_empty]
    exact Set.infinite_univ

theorem algorithmFive_selectedCore_infinite
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    (finiteCommonCore
      (indexedLanguages family
        (algorithmFiveIndices family stream t))).Infinite := by
  classical
  simpa [algorithmFiveIndices, algorithmFiveCutoff] using
    (Nat.findGreatest_spec
      (P := fun k =>
        AlgorithmFiveStableThrough family stream t k ∧
          (finiteCommonCore
            (indexedLanguages family
              (algorithmFivePrefixIndices family stream t k))).Infinite)
      (show 0 ≤ t by omega)
      (algorithmFive_zero_candidate family stream t)).2

theorem algorithmFiveCutoff_stable
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    AlgorithmFiveStableThrough family stream t
      (algorithmFiveCutoff family stream t) := by
  classical
  simpa [algorithmFiveCutoff] using
    (Nat.findGreatest_spec
      (P := fun k =>
        AlgorithmFiveStableThrough family stream t k ∧
          (finiteCommonCore
            (indexedLanguages family
              (algorithmFivePrefixIndices family stream t k))).Infinite)
      (show 0 ≤ t by omega)
      (algorithmFive_zero_candidate family stream t)).1

theorem le_algorithmFiveCutoff
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) {t k : ℕ}
    (hkt : k ≤ t)
    (hstable : AlgorithmFiveStableThrough family stream t k)
    (hinfinite :
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFivePrefixIndices family stream t k))).Infinite) :
    k ≤ algorithmFiveCutoff family stream t := by
  classical
  exact Nat.le_findGreatest hkt ⟨hstable, hinfinite⟩

theorem algorithmFivePrefix_mono
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ)
    {k q : ℕ} (hkq : k ≤ q) :
    algorithmFivePrefixIndices family stream t k ⊆
      algorithmFivePrefixIndices family stream t q := by
  intro i hi
  rw [mem_algorithmFivePrefixIndices] at hi ⊢
  exact ⟨hi.1, hi.2.1.trans_le hkq, hi.2.2⟩

/-- Extend a finite history arbitrarily; Algorithm 5 only inspects its two
latest prefixes, so the fallback is observationally irrelevant. -/
def algorithmFivePrefixCompletion {t : ℕ} (history : Fin t → ℕ) :
    GenLimit.Generic.Stream ℕ :=
  GenLimit.Generic.historyThenFallback (List.ofFn history) 0

theorem algorithmFivePrefixCompletion_eq
    {t : ℕ} (history : Fin t → ℕ) {i : ℕ} (hi : i < t) :
    algorithmFivePrefixCompletion history i = history ⟨i, hi⟩ := by
  simp [algorithmFivePrefixCompletion,
    GenLimit.Generic.historyThenFallback, hi]

theorem algorithmFiveIndices_prefixCompletion
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    algorithmFiveIndices family
        (algorithmFivePrefixCompletion
          (fun i : Fin t => stream i)) t =
      algorithmFiveIndices family stream t := by
  have hcurrent :
      GenLimit.Generic.sample
          (algorithmFivePrefixCompletion
            (fun i : Fin t => stream i)) t =
        GenLimit.Generic.sample stream t :=
    GenLimit.Generic.sample_eq_of_eq_on_prefix
      (fun i hi => algorithmFivePrefixCompletion_eq _ hi)
  have hprevious :
      GenLimit.Generic.sample
          (algorithmFivePrefixCompletion
            (fun i : Fin t => stream i)) (t - 1) =
        GenLimit.Generic.sample stream (t - 1) :=
    GenLimit.Generic.sample_eq_of_eq_on_prefix
      (fun i hi => algorithmFivePrefixCompletion_eq _
        (hi.trans_le (Nat.sub_le t 1)))
  let completion :=
    algorithmFivePrefixCompletion (fun i : Fin t => stream i)
  have hactiveCurrent :
      algorithmFiveActiveIndices family completion t =
        algorithmFiveActiveIndices family stream t := by
    unfold algorithmFiveActiveIndices
    rw [hcurrent]
  have hactivePrevious :
      algorithmFiveActiveIndices family completion (t - 1) =
        algorithmFiveActiveIndices family stream (t - 1) := by
    unfold algorithmFiveActiveIndices
    rw [hprevious]
  have hprefix : ∀ k,
      algorithmFivePrefixIndices family completion t k =
        algorithmFivePrefixIndices family stream t k := by
    intro k
    simp [algorithmFivePrefixIndices, hactiveCurrent]
  have hstable : ∀ k,
      AlgorithmFiveStableThrough family completion t k ↔
        AlgorithmFiveStableThrough family stream t k := by
    intro k
    unfold AlgorithmFiveStableThrough
    simp only [hactiveCurrent, hactivePrevious]
  have hcutoff :
      algorithmFiveCutoff family completion t =
        algorithmFiveCutoff family stream t := by
    unfold algorithmFiveCutoff
    congr 1
    funext k
    rw [hstable k, hprefix k]
  unfold algorithmFiveIndices
  rw [hcutoff, hprefix]

/-- Literal finite-history set generator implementing Algorithm 5. -/
noncomputable def algorithmFiveGenerator
    (family : ℕ → Set ℕ) : SetGenerator ℕ :=
  fun t history =>
    finiteCommonCore
        (indexedLanguages family
          (algorithmFiveIndices family
            (algorithmFivePrefixCompletion history) t)) \
      (↑(GenLimit.Generic.sequenceSample history) : Set ℕ)

@[simp] theorem algorithmFiveGenerator_output
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    setOutput (algorithmFiveGenerator family) stream t =
      finiteCommonCore
          (indexedLanguages family
            (algorithmFiveIndices family stream t)) \
        (↑(GenLimit.Generic.sample stream t) : Set ℕ) := by
  simp [setOutput, algorithmFiveGenerator,
    algorithmFiveIndices_prefixCompletion,
    GenLimit.Generic.sequenceSample_prefix]

theorem algorithmFiveGenerator_infinite
    (family : ℕ → Set ℕ) :
    IsInfiniteSetGenerator (algorithmFiveGenerator family) := by
  intro t history
  rw [algorithmFiveGenerator]
  exact
    (algorithmFive_selectedCore_infinite family
      (algorithmFivePrefixCompletion history) t).diff
      (GenLimit.Generic.sequenceSample history).finite_toSet

/-! ## Stabilization below the target index -/

theorem candidate_eventually_consistent_iff_presented_subset
    (family : ℕ → Set ℕ)
    {stream : GenLimit.Generic.Stream ℕ} {presented : Set ℕ}
    (hpresents : GenLimit.Generic.Presents stream presented)
    (i : ℕ) :
    ∃ T, ∀ t, T ≤ t →
      ((↑(GenLimit.Generic.sample stream t) : Set ℕ) ⊆ family i ↔
        presented ⊆ family i) := by
  by_cases hsub : presented ⊆ family i
  · refine ⟨0, fun t _ => ⟨fun _ => hsub, ?_⟩⟩
    intro _ x hx
    change x ∈ GenLimit.Generic.sample stream t at hx
    rw [GenLimit.Generic.mem_sample_iff] at hx
    obtain ⟨s, _hs, rfl⟩ := hx
    apply hsub
    rw [← hpresents]
    exact ⟨s, rfl⟩
  · obtain ⟨x, hxPresented, hxFamily⟩ := Set.not_subset.mp hsub
    rw [← hpresents] at hxPresented
    obtain ⟨s, rfl⟩ := hxPresented
    refine ⟨s + 1, fun t ht => ?_⟩
    constructor
    · intro hconsistent
      exact False.elim
        (hxFamily (hconsistent
          (GenLimit.Generic.value_mem_sample
            (Nat.lt_succ_self s |>.trans_le ht))))
    · exact fun hsub' => False.elim (hsub hsub')

theorem finite_scope_eventually_consistent_iff_presented_subset
    (family : ℕ → Set ℕ)
    {stream : GenLimit.Generic.Stream ℕ} {presented : Set ℕ}
    (hpresents : GenLimit.Generic.Presents stream presented)
    (scope : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < scope →
      ((↑(GenLimit.Generic.sample stream t) : Set ℕ) ⊆ family i ↔
        presented ⊆ family i) := by
  induction scope with
  | zero => exact ⟨0, by omega⟩
  | succ scope ih =>
      obtain ⟨Tscope, hTscope⟩ := ih
      obtain ⟨Ti, hTi⟩ :=
        candidate_eventually_consistent_iff_presented_subset
          family hpresents scope
      refine ⟨max Tscope Ti, ?_⟩
      intro t ht i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hTscope t ((Nat.le_max_left _ _).trans ht) i hi
      · exact hTi t ((Nat.le_max_right _ _).trans ht)

/-! ## Proposition 6.3: eventual validity -/

theorem algorithmFive_consistency_antitone
    (family : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ)
    {s t i : ℕ} (hst : s ≤ t)
    (hconsistent :
      (↑(GenLimit.Generic.sample stream t) : Set ℕ) ⊆ family i) :
    (↑(GenLimit.Generic.sample stream s) : Set ℕ) ⊆ family i := by
  intro x hx
  exact hconsistent (GenLimit.Generic.sample_mono hst hx)

theorem presented_subset_finiteCommonCore
    (family : ℕ → Set ℕ) (indices : Finset ℕ)
    (presented : Set ℕ)
    (hsub : ∀ i ∈ indices, presented ⊆ family i) :
    presented ⊆ finiteCommonCore (indexedLanguages family indices) := by
  intro x hx L hL
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hL
  exact hsub i hi hx

theorem finiteCommonCore_subset_of_index
    (family : ℕ → Set ℕ) (indices : Finset ℕ) {i : ℕ}
    (hi : i ∈ indices) :
    finiteCommonCore (indexedLanguages family indices) ⊆ family i := by
  apply finiteCommonCore_subset_of_mem
  classical
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Once the finitely many candidates through the target index have
stabilized, Algorithm 5's maximal prefix contains the target and its common
core is therefore target-valid. -/
theorem algorithmFive_eventually_target_valid_core
    (family : ℕ → Set ℕ)
    {stream : GenLimit.Generic.Stream ℕ} {presented : Set ℕ}
    (hpresents : GenLimit.Generic.Presents stream presented)
    (hpresentedInfinite : presented.Infinite)
    (z : ℕ) (htarget : presented ⊆ family z) :
    ∃ T, ∀ t, T ≤ t →
      z ∈ algorithmFiveIndices family stream t ∧
        finiteCommonCore
            (indexedLanguages family
              (algorithmFiveIndices family stream t)) ⊆
          family z := by
  obtain ⟨Tstable, hTstable⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      family hpresents (z + 1)
  let T := max (Tstable + 1) (z + 2)
  refine ⟨T, ?_⟩
  intro t ht
  have htStable : Tstable ≤ t := by
    exact (Nat.le_succ Tstable).trans
      ((Nat.le_max_left _ _).trans ht)
  have htPredStable : Tstable ≤ t - 1 := by
    have : Tstable + 1 ≤ t :=
      (Nat.le_max_left _ _).trans ht
    omega
  have hzt : z < t := by
    have : z + 2 ≤ t :=
      (Nat.le_max_right _ _).trans ht
    omega
  have hzPred : z < t - 1 := by
    have : z + 2 ≤ t :=
      (Nat.le_max_right _ _).trans ht
    omega
  have hstable :
      AlgorithmFiveStableThrough family stream t (z + 1) := by
    intro i hi
    have hiz : i ≤ z := Nat.le_of_lt_succ hi
    rw [mem_algorithmFiveActiveIndices,
      mem_algorithmFiveActiveIndices]
    have hit : i < t := hiz.trans_lt hzt
    have hiPred : i < t - 1 := hiz.trans_lt hzPred
    simp only [hit, hiPred, true_and]
    exact
      (hTstable t htStable i hi).trans
        (hTstable (t - 1) htPredStable i hi).symm
  have hprefixSub :
      presented ⊆
        finiteCommonCore
          (indexedLanguages family
            (algorithmFivePrefixIndices family stream t (z + 1))) := by
    apply presented_subset_finiteCommonCore
    intro i hi
    rw [mem_algorithmFivePrefixIndices] at hi
    exact (hTstable t htStable i hi.2.1).1 hi.2.2
  have hprefixInfinite :
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFivePrefixIndices family stream t (z + 1)))).Infinite :=
    hpresentedInfinite.mono hprefixSub
  have hcutoff :
      z + 1 ≤ algorithmFiveCutoff family stream t :=
    le_algorithmFiveCutoff family stream
      (by omega) hstable hprefixInfinite
  have hzPrefix :
      z ∈ algorithmFivePrefixIndices family stream t (z + 1) := by
    rw [mem_algorithmFivePrefixIndices]
    refine ⟨hzt, Nat.lt_succ_self z, ?_⟩
    intro x hx
    apply htarget
    rw [← hpresents]
    change x ∈ GenLimit.Generic.sample stream t at hx
    rw [GenLimit.Generic.mem_sample_iff] at hx
    obtain ⟨s, _hs, rfl⟩ := hx
    exact ⟨s, rfl⟩
  have hzSelected : z ∈ algorithmFiveIndices family stream t := by
    exact algorithmFivePrefix_mono family stream t hcutoff hzPrefix
  exact ⟨hzSelected,
    finiteCommonCore_subset_of_index family
      (algorithmFiveIndices family stream t) hzSelected⟩

/-! ## Algorithm 5's fall-back transition -/

/-- If a selected core does not contain the exactly presented noiseless
subset, the first selected language missing a presented point eventually
leaves the active set.  At that transition Algorithm 5 falls back exactly to
the preceding prefix, all of whose languages contain the presented set. -/
theorem algorithmFive_fallback_step
    (family : ℕ → Set ℕ)
    {stream : GenLimit.Generic.Stream ℕ} {presented : Set ℕ}
    (hpresents : GenLimit.Generic.Presents stream presented)
    (hpresentedInfinite : presented.Infinite)
    (n : ℕ)
    (hnot :
      ¬presented ⊆
        finiteCommonCore
          (indexedLanguages family
            (algorithmFiveIndices family stream n))) :
    ∃ r, n < r ∧
      presented ⊆
        finiteCommonCore
          (indexedLanguages family
            (algorithmFiveIndices family stream r)) := by
  classical
  let selected := algorithmFiveIndices family stream n
  have hexistsBad :
      ∃ i, i ∈ selected ∧ ¬presented ⊆ family i := by
    by_contra hnone
    push_neg at hnone
    exact hnot
      (presented_subset_finiteCommonCore
        family selected presented hnone)
  let b := Nat.find hexistsBad
  have hbSpec : b ∈ selected ∧ ¬presented ⊆ family b :=
    Nat.find_spec hexistsBad
  have hbParts :
      b < n ∧ b < algorithmFiveCutoff family stream n ∧
        (↑(GenLimit.Generic.sample stream n) : Set ℕ) ⊆ family b := by
    simpa [selected, algorithmFiveIndices,
      mem_algorithmFivePrefixIndices] using hbSpec.1
  have hgoodBefore :
      ∀ i, i < b → i ∈ selected → presented ⊆ family i := by
    intro i hib hiSelected
    by_contra hiBad
    have hbLeI :=
      Nat.find_min' hexistsBad ⟨hiSelected, hiBad⟩
    omega
  obtain ⟨x, hxPresented, hxNotFamily⟩ :=
    Set.not_subset.mp hbSpec.2
  rw [← hpresents] at hxPresented
  obtain ⟨witnessTime, hwitness⟩ := hxPresented
  have hexBadTime : ∃ s, stream s ∉ family b :=
    ⟨witnessTime, by simpa [hwitness] using hxNotFamily⟩
  let s := Nat.find hexBadTime
  have hsBad : stream s ∉ family b := Nat.find_spec hexBadTime
  have hbeforeS : ∀ q, q < s → stream q ∈ family b := by
    intro q hqs
    by_contra hqBad
    have hsLeQ := Nat.find_min' hexBadTime hqBad
    omega
  have hns : n ≤ s := by
    by_contra hsn
    have hsn' : s < n := Nat.lt_of_not_ge hsn
    exact hsBad
      (hbParts.2.2
        (GenLimit.Generic.value_mem_sample hsn'))
  let r := s + 1
  have hnr : n < r := by
    dsimp [r]
    omega
  have hbActiveBefore :
      b ∈ algorithmFiveActiveIndices family stream (r - 1) := by
    rw [mem_algorithmFiveActiveIndices]
    have hbr : b < r - 1 := by
      dsimp [r]
      omega
    refine ⟨hbr, ?_⟩
    intro y hy
    change y ∈ GenLimit.Generic.sample stream s at hy
    rw [GenLimit.Generic.mem_sample_iff] at hy
    obtain ⟨q, hqs, rfl⟩ := hy
    exact hbeforeS q hqs
  have hbNotActiveNow :
      b ∉ algorithmFiveActiveIndices family stream r := by
    rw [mem_algorithmFiveActiveIndices]
    push_neg
    intro _hbScope
    intro hconsistent
    exact hsBad
      (hconsistent (by
        dsimp [r]
        exact GenLimit.Generic.value_mem_sample (Nat.lt_succ_self s)))
  have hstableBefore :
      AlgorithmFiveStableThrough family stream r b := by
    intro i hib
    rw [mem_algorithmFiveActiveIndices,
      mem_algorithmFiveActiveIndices]
    have hin : i < n := hib.trans hbParts.1
    have hir : i < r := hin.trans hnr
    have hiPred : i < r - 1 := by
      dsimp [r]
      omega
    simp only [hir, hiPred, true_and]
    by_cases hiConsistent :
        (↑(GenLimit.Generic.sample stream n) : Set ℕ) ⊆ family i
    · have hiSelected : i ∈ selected := by
        change i ∈ algorithmFiveIndices family stream n
        rw [algorithmFiveIndices,
          mem_algorithmFivePrefixIndices]
        exact ⟨hin, hib.trans hbParts.2.1, hiConsistent⟩
      have hiGood := hgoodBefore i hib hiSelected
      constructor <;> intro _
      · intro y hy
        apply hiGood
        rw [← hpresents]
        change y ∈ GenLimit.Generic.sample stream (r - 1) at hy
        rw [GenLimit.Generic.mem_sample_iff] at hy
        obtain ⟨q, _hq, rfl⟩ := hy
        exact ⟨q, rfl⟩
      · intro y hy
        apply hiGood
        rw [← hpresents]
        change y ∈ GenLimit.Generic.sample stream r at hy
        rw [GenLimit.Generic.mem_sample_iff] at hy
        obtain ⟨q, _hq, rfl⟩ := hy
        exact ⟨q, rfl⟩
    · constructor
      · intro hnow
        exact False.elim
          (hiConsistent
            (algorithmFive_consistency_antitone
              family stream (by omega) hnow))
      · intro hprevious
        exact False.elim
          (hiConsistent
            (algorithmFive_consistency_antitone
              family stream (by omega) hprevious))
  have hprefixSub :
      presented ⊆
        finiteCommonCore
          (indexedLanguages family
            (algorithmFivePrefixIndices family stream r b)) := by
    apply presented_subset_finiteCommonCore
    intro i hi
    rw [mem_algorithmFivePrefixIndices] at hi
    have hin : i < n := hi.2.1.trans hbParts.1
    have hiConsistentN :=
      algorithmFive_consistency_antitone
        family stream (show n ≤ r by omega) hi.2.2
    have hiSelected : i ∈ selected := by
      change i ∈ algorithmFiveIndices family stream n
      rw [algorithmFiveIndices,
        mem_algorithmFivePrefixIndices]
      exact ⟨hin, hi.2.1.trans hbParts.2.1, hiConsistentN⟩
    exact hgoodBefore i hi.2.1 hiSelected
  have hprefixInfinite :
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFivePrefixIndices family stream r b))).Infinite :=
    hpresentedInfinite.mono hprefixSub
  have hbLeCutoff : b ≤ algorithmFiveCutoff family stream r :=
    le_algorithmFiveCutoff family stream
      (by dsimp [r]; omega) hstableBefore hprefixInfinite
  have hcutoffLeB : algorithmFiveCutoff family stream r ≤ b := by
    by_contra hnotLe
    have hbLt : b < algorithmFiveCutoff family stream r :=
      Nat.lt_of_not_ge hnotLe
    have hstableAtB :=
      algorithmFiveCutoff_stable family stream r b hbLt
    exact hbNotActiveNow (hstableAtB.mpr hbActiveBefore)
  have hcutoffEq : algorithmFiveCutoff family stream r = b :=
    Nat.le_antisymm hcutoffLeB hbLeCutoff
  refine ⟨r, hnr, ?_⟩
  simpa [algorithmFiveIndices, hcutoffEq] using hprefixSub

/-- Algorithm 5 contains the entire noiseless presented subset at arbitrarily
late rounds. -/
theorem algorithmFive_frequently_presented_subset_core
    (family : ℕ → Set ℕ)
    {stream : GenLimit.Generic.Stream ℕ} {presented : Set ℕ}
    (hpresents : GenLimit.Generic.Presents stream presented)
    (hpresentedInfinite : presented.Infinite) :
    ∃ᶠ t : ℕ in atTop,
      presented ⊆
        finiteCommonCore
          (indexedLanguages family
            (algorithmFiveIndices family stream t)) := by
  rw [frequently_atTop]
  intro cutoff
  by_cases hgood :
      presented ⊆
        finiteCommonCore
          (indexedLanguages family
            (algorithmFiveIndices family stream cutoff))
  · exact ⟨cutoff, le_rfl, hgood⟩
  · obtain ⟨r, hcutoffR, hr⟩ :=
      algorithmFive_fallback_step
        family hpresents hpresentedInfinite cutoff hgood
    exact ⟨r, Nat.le_of_lt hcutoffR, hr⟩

/-- Density form of the fall-back conclusion after deleting the finite
observed sample from each output. -/
theorem algorithmFive_frequently_lowerDensity
    (family : ℕ → Set ℕ)
    (K : OrderedLanguage)
    {stream : GenLimit.Generic.Stream ℕ} {presented : Set ℕ}
    (hpresents : GenLimit.Generic.Presents stream presented)
    (hpresentedInfinite : presented.Infinite)
    (d : ℝ) (hdensity : d ≤ K.lowerDensity presented) :
    ∃ᶠ t : ℕ in atTop,
      d ≤ K.lowerDensity
        (setOutput (algorithmFiveGenerator family) stream t) := by
  exact
    (algorithmFive_frequently_presented_subset_core
      family hpresents hpresentedInfinite).mono fun t ht => by
        let core :=
          finiteCommonCore
            (indexedLanguages family
              (algorithmFiveIndices family stream t))
        have hcoreDensity : d ≤ K.lowerDensity core :=
          hdensity.trans (K.lowerDensity_mono ht)
        have hdelete :=
          K.lowerDensity_diff_finite core
            (GenLimit.Generic.sample stream t).finite_toSet
        rw [algorithmFiveGenerator_output]
        exact hcoreDensity.trans_eq hdelete.symm

/-- Proposition 6.3, stated with a separate ordered reference target.  This
slightly more general form is what Theorem 6.1 needs after adding finitely
many noisy points to the target language. -/
theorem proposition_6_3_algorithmFive
    (family : ℕ → Set ℕ)
    (K : OrderedLanguage)
    (z : ℕ)
    {stream : GenLimit.Generic.Stream ℕ}
    (hinjective : Function.Injective stream)
    (hnoNoise : Set.range stream ⊆ family z)
    (d : ℝ)
    (hdensity : d ≤ K.lowerDensity (Set.range stream)) :
    GeneratesInfiniteSetInLimitOn
        (algorithmFiveGenerator family) (family z) stream ∧
      d ≤ setBasedUpperDensity
        (algorithmFiveGenerator family) K stream := by
  have hpresents :
      GenLimit.Generic.Presents stream (Set.range stream) := rfl
  have hpresentedInfinite : (Set.range stream).Infinite :=
    Set.infinite_range_of_injective hinjective
  refine ⟨?_, ?_⟩
  · refine ⟨algorithmFiveGenerator_infinite family, ?_⟩
    obtain ⟨T, hT⟩ :=
      algorithmFive_eventually_target_valid_core
        family hpresents hpresentedInfinite z hnoNoise
    refine ⟨T, fun t ht => ?_⟩
    have hcoreSubset := (hT t ht).2
    unfold SetCorrectAt
    rw [algorithmFiveGenerator_output]
    refine ⟨?_, ?_⟩
    · exact fun _ hx => hcoreSubset hx.1
    · rw [Set.disjoint_left]
      exact fun _ hxOutput hxSample => hxOutput.2 hxSample
  · unfold setBasedUpperDensity
    apply le_limsup_of_frequently_le
    · exact algorithmFive_frequently_lowerDensity
        family K hpresents hpresentedInfinite d hdensity
    · exact isBoundedUnder_of
        ⟨1, fun t => K.lowerDensity_le_one
          (setOutput (algorithmFiveGenerator family) stream t)⟩

/-! ## Theorem 6.1: finite additive noise -/

/-- Coded add-only expansion used by Algorithm 3. -/
theorem exists_addOnlyExpansion_index
    (O : GenLimit.OracleFamily) (z : ℕ) (add : Finset ℕ) :
    ∃ j,
      finiteExpansionBaseIndex j = z ∧
        (finiteExpansionOracleFamily O).language j =
          O.language z ∪ (add : Set ℕ) := by
  let data : FiniteExpansionCode :=
    (z, Finset.equivBitIndices.symm add,
      Finset.equivBitIndices.symm ∅)
  let j := encodeFiniteExpansionCode data
  refine ⟨j, ?_, ?_⟩
  · simp [finiteExpansionBaseIndex, j, data]
  · change finiteExpansionLanguage O j =
      O.language z ∪ (add : Set ℕ)
    rw [finiteExpansionLanguage]
    simp only [j, data, finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    simp [finiteExpansion]

/-- Theorem 6.1 for an explicitly indexed countable family.  The omission
parameter appears only through the exact lower-density premise
`1 - c ≤ μ_low(range stream ∩ K, K)`; the generator itself does not know `c`.
-/
theorem theorem_6_1_algorithmFive
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = O.language i)
    (z : ℕ) (c : ℝ)
    {stream : GenLimit.Generic.Stream ℕ}
    (hinjective : Function.Injective stream)
    (hfiniteNoise : FiniteNoise stream (O.language z))
    (homissions : OmissionsAtMost stream (orders z) c) :
    GeneratesInfiniteSetInLimitOn
        (algorithmFiveGenerator
          (finiteExpansionOracleFamily O).language)
        (orders z).carrier stream ∧
      1 - c ≤ setBasedUpperDensity
        (algorithmFiveGenerator
          (finiteExpansionOracleFamily O).language)
        (orders z) stream := by
  let noiseFinite := displayedNoise_finite hfiniteNoise
  obtain ⟨j, hjBase, hjLanguage⟩ :=
    exists_addOnlyExpansion_index O z noiseFinite.toFinset
  have hnoiseCoe :
      (↑noiseFinite.toFinset : Set ℕ) =
        displayedNoise stream (O.language z) :=
    Set.Finite.coe_toFinset noiseFinite
  have hrangeSubset :
      Set.range stream ⊆
        (finiteExpansionOracleFamily O).language j := by
    rw [hjLanguage, hnoiseCoe]
    intro x hx
    by_cases hxTarget : x ∈ O.language z
    · exact Or.inl hxTarget
    · exact Or.inr ⟨hx, hxTarget⟩
  have hrun :=
    proposition_6_3_algorithmFive
      (finiteExpansionOracleFamily O).language
      (orders z) j hinjective hrangeSubset (1 - c)
      (by
        unfold OmissionsAtMost at homissions
        simpa using homissions)
  constructor
  · rw [hcarrier z]
    apply generatesInfiniteSetInLimitOn_of_finite_extraneous_seen
      (expanded := (finiteExpansionOracleFamily O).language j)
    · rw [hjLanguage, hnoiseCoe]
      apply noiseFinite.subset
      intro x hx
      exact hx.1.resolve_left hx.2
    · rw [hjLanguage, hnoiseCoe]
      intro x hx
      exact hx.1.resolve_left hx.2 |>.1
    · exact hrun.1
  · exact hrun.2

end GenLimit.InfiniteContamination
