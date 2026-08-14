import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.ExhaustiveCharacterization
import GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency
import GenLimit.Core.OracleFamily
import Mathlib.Order.Interval.Finset.Basic

/-!
# Charikar--Pabbaraju: exhaustive generation from membership queries

This file formalizes Weak Angluin's Condition with Enumeration and
Proposition 6.3 of Charikar--Pabbaraju, *Exploring Facets of Language
Generation in the Limit*, arXiv:2411.15364v2.

The distinction between the two oracles in Section 6 is kept at the type
level.  `O.query i x` is the ordinary membership oracle for `x in L_i`.
The finite tell-tales are supplied by one stage-by-stage computable procedure,
as required by the hypothesis of Proposition 6.3.  The algorithm below never
uses the subset or finite-difference oracles from Proposition 6.2.

The universe is `Nat`, the encoding used by the repository for the paper's
countable string universe.  Paper indices start at one; Lean indices start at
zero, so the paper's search through `L_1,...,L_n` is `range (n+1)` here.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit
open GenLimit.Generic

/-! ## Weak tell-tale enumeration -/

/-- The finite weak tell-tale property in equation (7), at one indexed
language. -/
def IsWeakTellTale
    (F : Generic.LanguageFamily Nat) (i : Nat) (T : Finset Nat) : Prop :=
  (T : Set Nat) ⊆ F i ∧
    ∀ j, (T : Set Nat) ⊆ F j → F j ⊂ F i → (F i \ F j).Finite

/-- Set-valued weak tell-tales, matching a stage-by-stage enumerator whose
finite output need not come with a halting signal. -/
def IsEnumeratedWeakTellTale
    (F : Generic.LanguageFamily Nat) (i : Nat) (T : Set Nat) : Prop :=
  T.Finite ∧ T ⊆ F i ∧
    ∀ j, T ⊆ F j → F j ⊂ F i → (F i \ F j).Finite

/-- Weak Angluin's Condition with Enumeration, equation (9) in Section 6.2.

The same total computable stage procedure `emit` works uniformly for every
index.  `none` means that a stage emits no new word. -/
def WeakAngluinEnumeration (O : OracleFamily) : Prop :=
  ∃ emit : Nat → Nat → Option Nat, Computable₂ emit ∧
    ∀ i, IsEnumeratedWeakTellTale O.language i
      (GenLimit.Angluin.enumeratedSet emit i)

/-- The semantic finite-stage facts used by the proof of Proposition 6.3.
They are derived below from the source-faithful computable enumeration. -/
def IsWeakTellTaleApproximation
    (F : Generic.LanguageFamily Nat) (A : Nat → Nat → Finset Nat) : Prop :=
  (∀ i n m, n ≤ m → A i n ⊆ A i m) ∧
    ∀ i, ∃ T : Finset Nat, IsWeakTellTale F i T ∧
      ∃ N, ∀ n, N ≤ n → A i n = T

/-- A finite stage enumeration yields the eventually stable approximation
used in the paper's algorithm. -/
theorem weakTellTaleApproximation_of_enumeration
    {F : Generic.LanguageFamily Nat}
    {emit : Nat → Nat → Option Nat}
    (hTell : ∀ i, IsEnumeratedWeakTellTale F i
      (GenLimit.Angluin.enumeratedSet emit i)) :
    IsWeakTellTaleApproximation F (GenLimit.Angluin.stageContents emit) := by
  classical
  constructor
  · intro i n m hnm
    exact GenLimit.Angluin.stageContents_mono hnm
  · intro i
    let hfinite : (GenLimit.Angluin.enumeratedSet emit i).Finite :=
      (hTell i).1
    let T : Finset Nat := hfinite.toFinset
    have hTmem {x : Nat} :
        x ∈ T ↔ x ∈ GenLimit.Angluin.enumeratedSet emit i := by
      exact hfinite.mem_toFinset
    have hWeak : IsWeakTellTale F i T := by
      constructor
      · intro x hx
        exact (hTell i).2.1 (hTmem.mp hx)
      · intro j hTj hproper
        apply (hTell i).2.2 j
        · intro x hx
          exact hTj (hTmem.mpr hx)
        · exact hproper
    have hEvery : ∀ x, x ∈ T → ∃ stage, emit i stage = some x := by
      intro x hx
      exact hTmem.mp hx
    obtain ⟨N, hN⟩ :=
      GenLimit.Angluin.finite_emissions_bounded T hEvery
    refine ⟨T, hWeak, N, ?_⟩
    intro n hn
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨stage, -, hout⟩ :=
        GenLimit.Angluin.mem_stageContents_iff.mp hx
      exact hTmem.mpr ⟨stage, hout⟩
    · intro x hx
      obtain ⟨stage, hstage, hout⟩ := hN x hx
      exact GenLimit.Angluin.mem_stageContents_iff.mpr
        ⟨stage, lt_of_lt_of_le hstage hn, hout⟩

/-! ## Finite membership-query stage test -/

/-- Boolean form of the two finite tests in Proposition 6.3.  The first test
checks that the current tell-tale approximation has appeared in the sample;
the second asks `O.query i x` once for each distinct observed word. -/
def weakStageTest
    (O : OracleFamily) (A : Nat → Nat → Finset Nat)
    (S : Finset Nat) (t i : Nat) : Bool :=
  decide (A i t ⊆ S) &&
    decide (∀ x, x ∈ S → O.query i x = true)

/-- Propositional form of the finite stage test. -/
def WeakStageEligible
    (O : OracleFamily) (A : Nat → Nat → Finset Nat)
    (S : Finset Nat) (t i : Nat) : Prop :=
  A i t ⊆ S ∧ (S : Set Nat) ⊆ O.language i

theorem weakStageTest_eq_true_iff
    {O : OracleFamily} {A : Nat → Nat → Finset Nat}
    {S : Finset Nat} {t i : Nat} :
    weakStageTest O A S t i = true ↔ WeakStageEligible O A S t i := by
  simp only [weakStageTest, Bool.and_eq_true, decide_eq_true_eq,
    WeakStageEligible]
  constructor
  · rintro ⟨hA, hS⟩
    refine ⟨hA, ?_⟩
    · intro x hx
      exact (O.query_spec i x).mp (hS x hx)
  · rintro ⟨hA, hS⟩
    exact ⟨hA, fun x hx => (O.query_spec i x).mpr (hS hx)⟩

/-- Candidate indices searched at time `t`. -/
def weakStageCandidates
    (O : OracleFamily) (A : Nat → Nat → Finset Nat)
    (S : Finset Nat) (t : Nat) : Finset Nat :=
  (Finset.range (t + 1)).filter fun i => weakStageTest O A S t i

@[simp] theorem mem_weakStageCandidates
    {O : OracleFamily} {A : Nat → Nat → Finset Nat}
    {S : Finset Nat} {t i : Nat} :
    i ∈ weakStageCandidates O A S t ↔
      i ≤ t ∧ WeakStageEligible O A S t i := by
  simp [weakStageCandidates, weakStageTest_eq_true_iff, Nat.lt_succ_iff]

/-- The least passing index in the paper's Proposition 6.3 algorithm. -/
def weakStageFocus
    (O : OracleFamily) (A : Nat → Nat → Finset Nat)
    (S : Finset Nat) (t : Nat) : Nat :=
  if h : (weakStageCandidates O A S t).Nonempty then
    (weakStageCandidates O A S t).min' h
  else 0

theorem weakStageFocus_mem
    {O : OracleFamily} {A : Nat → Nat → Finset Nat}
    {S : Finset Nat} {t z : Nat}
    (hz : z ∈ weakStageCandidates O A S t) :
    weakStageFocus O A S t ∈ weakStageCandidates O A S t := by
  have hne : (weakStageCandidates O A S t).Nonempty := ⟨z, hz⟩
  simp [weakStageFocus, hne, Finset.min'_mem]

theorem weakStageFocus_le
    {O : OracleFamily} {A : Nat → Nat → Finset Nat}
    {S : Finset Nat} {t z : Nat}
    (hz : z ∈ weakStageCandidates O A S t) :
    weakStageFocus O A S t ≤ z := by
  have hne : (weakStageCandidates O A S t).Nonempty := ⟨z, hz⟩
  simpa [weakStageFocus, hne] using
    Finset.min'_le (weakStageCandidates O A S t) z hz

/-! ## Enumerating one oracle language -/

theorem oracle_language_has_member_at_or_above
    (O : OracleFamily) (i n : Nat) :
    ∃ x, n ≤ x ∧ O.query i x = true := by
  obtain ⟨x, hx, hnot⟩ :=
    (O.infinite' i).exists_notMem_finset (Finset.range n)
  exact ⟨x, Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h)),
    (O.query_spec i x).mpr hx⟩

/-- Search the membership oracle for the first member of `L_i` at or above
`n`.  Every individual output uses a finite initial segment of membership
queries, and infinitude guarantees termination. -/
noncomputable def enumerateOracleLanguage
    (O : OracleFamily) (i n : Nat) : Nat :=
  Nat.find (oracle_language_has_member_at_or_above O i n)

theorem enumerateOracleLanguage_spec
    (O : OracleFamily) (i n : Nat) :
    n ≤ enumerateOracleLanguage O i n ∧
      enumerateOracleLanguage O i n ∈ O.language i := by
  have h := Nat.find_spec (oracle_language_has_member_at_or_above O i n)
  exact ⟨h.1, (O.query_spec i _).mp h.2⟩

theorem range_enumerateOracleLanguage
    (O : OracleFamily) (i : Nat) :
    Set.range (enumerateOracleLanguage O i) = O.language i := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact (enumerateOracleLanguage_spec O i n).2
  · intro x hx
    refine ⟨x, Nat.le_antisymm ?_ (enumerateOracleLanguage_spec O i x).1⟩
    apply Nat.find_min'
      (oracle_language_has_member_at_or_above O i x)
    exact ⟨Nat.le_refl x, (O.query_spec i x).mpr hx⟩

/-! ## Proposition 6.3 -/

/-- The explicit membership-query exhaustive algorithm from Proposition 6.3.
At time `t` it selects the least passing index and scans that language's
membership oracle in generate-only mode. -/
noncomputable def membershipExhaustiveAlgorithm
    (O : OracleFamily) (A : Nat → Nat → Finset Nat) :
    ExhaustiveAlgorithm Nat :=
  fun t xs =>
    enumerateOracleLanguage O
      (weakStageFocus O A (Generic.sequenceSample xs) t)

theorem generateOnly_membershipExhaustiveAlgorithm
    (O : OracleFamily) (A : Nat → Nat → Finset Nat)
    (stream : Generic.Stream Nat) (t : Nat) :
    generateOnly (membershipExhaustiveAlgorithm O A) stream t =
      O.language
        (weakStageFocus O A (Generic.sample stream t) t) := by
  simpa [generateOnly, generatorAt, membershipExhaustiveAlgorithm,
    Generic.sequenceSample_prefix] using
    range_enumerateOracleLanguage O
      (weakStageFocus O A (Generic.sample stream t) t)

theorem target_eventually_weakStageCandidate
    {O : OracleFamily} {A : Nat → Nat → Finset Nat}
    (hA : IsWeakTellTaleApproximation O.language A)
    {stream : Generic.Stream Nat} {z : Nat}
    (hP : Generic.Presents stream (O.language z)) :
    ∃ N, ∀ t, N ≤ t →
      z ∈ weakStageCandidates O A (Generic.sample stream t) t := by
  classical
  obtain ⟨T, hT, NA, hstable⟩ := hA.2 z
  obtain ⟨NS, hsample⟩ :=
    Generic.finset_eventually_subset_sample hP T hT.1
  refine ⟨max z (max NA NS), ?_⟩
  intro t ht
  apply mem_weakStageCandidates.mpr
  constructor
  · exact (Nat.le_max_left z (max NA NS)).trans ht
  · constructor
    · have hNA : NA ≤ t :=
        (Nat.le_max_left NA NS).trans
          ((Nat.le_max_right z (max NA NS)).trans ht)
      rw [hstable t hNA]
      exact hsample.trans (Generic.sample_mono
        ((Nat.le_max_right NA NS).trans
          ((Nat.le_max_right z (max NA NS)).trans ht)))
    · intro x hx
      exact Generic.mem_language_of_mem_sample_of_presents hP hx

/-- Every fixed index not above the target is eventually either rejected by
the stage test, or is a finite-error superset of the target. -/
theorem lower_weakStageCandidate_eventually_safe
    {O : OracleFamily} {A : Nat → Nat → Finset Nat}
    (hA : IsWeakTellTaleApproximation O.language A)
    {stream : Generic.Stream Nat} {z i : Nat}
    (hP : Generic.Presents stream (O.language z)) :
    ∃ N, ∀ t, N ≤ t →
      WeakStageEligible O A (Generic.sample stream t) t i →
        O.language z ⊆ O.language i ∧
          (O.language i \ O.language z).Finite := by
  classical
  by_cases hsub : O.language z ⊆ O.language i
  · obtain ⟨T, hT, NA, hstable⟩ := hA.2 i
    by_cases hTz : (T : Set Nat) ⊆ O.language z
    · refine ⟨0, ?_⟩
      intro t _ _
      refine ⟨hsub, ?_⟩
      by_cases heq : O.language z = O.language i
      · simp [heq]
      · have hproper : O.language z ⊂ O.language i :=
          Set.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩
        exact hT.2 z hTz hproper
    · obtain ⟨x, hxT, hxnot⟩ := Set.not_subset.mp hTz
      refine ⟨NA, ?_⟩
      intro t ht hEligible
      have hxA : x ∈ A i t := by
        rw [hstable t ht]
        exact hxT
      have hxSample : x ∈ Generic.sample stream t := hEligible.1 hxA
      exact (hxnot (Generic.mem_language_of_mem_sample_of_presents hP hxSample)).elim
  · obtain ⟨x, hxTarget, hxnot⟩ := Set.not_subset.mp hsub
    obtain ⟨N, hN⟩ := Generic.eventually_mem_sample_of_presents hP hxTarget
    refine ⟨N, ?_⟩
    intro t ht hEligible
    exact (hxnot (hEligible.2 (hN t ht))).elim

/-- Proposition 6.3 at the finite-stage semantic layer.  The constructed
algorithm is the explicit relative membership-query algorithm above. -/
theorem proposition6_3_of_weakTellTaleApproximation
    (O : OracleFamily) (A : Nat → Nat → Finset Nat)
    (hA : IsWeakTellTaleApproximation O.language A) :
    IsExhaustiveGenerator (membershipExhaustiveAlgorithm O A)
      (Set.range O.language) := by
  classical
  intro K hK stream hP
  obtain ⟨z, rfl⟩ := hK
  obtain ⟨Ntarget, htarget⟩ :=
    target_eventually_weakStageCandidate hA hP
  have hpointwise : ∀ i, i < z + 1 → ∃ N, ∀ t, N ≤ t →
      (WeakStageEligible O A (Generic.sample stream t) t i →
        O.language z ⊆ O.language i ∧
          (O.language i \ O.language z).Finite) := by
    intro i _
    exact lower_weakStageCandidate_eventually_safe hA hP
  obtain ⟨Nlower, hlower⟩ :=
    GenLimit.Angluin.eventually_all_lt hpointwise
  refine ⟨max Ntarget Nlower, ?_⟩
  intro t ht
  have htTarget : Ntarget ≤ t := (Nat.le_max_left _ _).trans ht
  have htLower : Nlower ≤ t := (Nat.le_max_right _ _).trans ht
  have hzmem := htarget t htTarget
  let g := weakStageFocus O A (Generic.sample stream t) t
  have hgmem : g ∈ weakStageCandidates O A (Generic.sample stream t) t :=
    weakStageFocus_mem hzmem
  have hgle : g ≤ z := weakStageFocus_le hzmem
  have hgEligible : WeakStageEligible O A (Generic.sample stream t) t g :=
    (mem_weakStageCandidates.mp hgmem).2
  have hsafe := hlower t htLower g (Nat.lt_succ_of_le hgle) hgEligible
  unfold ExhaustiveCorrectAt
  rw [generateOnly_membershipExhaustiveAlgorithm]
  constructor
  · simpa [g] using hsafe.2
  · intro x hx
    exact Or.inr (hsafe.1 hx)

/-- Proposition 6.3, with the paper's exact computable-enumeration hypothesis.
The witness algorithm uses only `O.query` and the emitted tell-tale content;
no semantic subset or finite-difference decision is used by its definition. -/
theorem proposition6_3_membership_query_sufficient
    (O : OracleFamily) (hWeak : WeakAngluinEnumeration O) :
    ∃ A : ExhaustiveAlgorithm Nat,
      IsExhaustiveGenerator A (Set.range O.language) := by
  obtain ⟨emit, _hcomputable, hTell⟩ := hWeak
  let A := GenLimit.Angluin.stageContents emit
  have hApprox : IsWeakTellTaleApproximation O.language A :=
    weakTellTaleApproximation_of_enumeration hTell
  exact ⟨membershipExhaustiveAlgorithm O A,
    proposition6_3_of_weakTellTaleApproximation O A hApprox⟩

end GenLimit.CharikarPabbaraju
