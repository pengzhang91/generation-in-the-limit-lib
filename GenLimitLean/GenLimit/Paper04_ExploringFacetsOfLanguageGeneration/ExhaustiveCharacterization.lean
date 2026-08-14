import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Exhaustive
import GenLimit.Support.EnumerationProgress
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Set.Finite.Lattice

/-!
# Charikar--Pabbaraju: characterization of exhaustive generation

This file formalizes Propositions 6.1 and 6.2 and overview Theorem 4 of
Charikar--Pabbaraju, *Exploring Facets of Language Generation in the Limit*,
arXiv:2411.15364v2.

The paper works with a countably indexed collection of infinite languages over
a countable string universe.  We represent that collection by `F : ℕ → Set α`;
its underlying collection is `Set.range F`.  Proposition 6.2 is a semantic
oracle theorem: the construction below uses classical tests for set inclusion
and finiteness of set differences.  This is precisely the strong-oracle
construction in the proposition, not the later membership-query construction.
-/

namespace GenLimit.CharikarPabbaraju

/-! ## The critical-language construction in Proposition 6.2 -/

/-- A language is consistent with a finite input history. -/
def ExhaustiveHistoryConsistent
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) (i : ℕ) : Prop :=
  (↑(GenLimit.Generic.sequenceSample xs) : Set α) ⊆ F i

/-- The paper's criticality condition among the indexed consistent languages. -/
def ExhaustiveHistoryCritical
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) (i : ℕ) : Prop :=
  ExhaustiveHistoryConsistent F xs i ∧
    ∀ j, j ≤ i → ExhaustiveHistoryConsistent F xs j → F i ⊆ F j

theorem exhaustiveHistoryCritical_subset_of_le
    {F : ℕ → Set α} {t : ℕ} {xs : Fin t → α} {i j : ℕ}
    (hij : i ≤ j) (hi : ExhaustiveHistoryCritical F xs i)
    (hj : ExhaustiveHistoryCritical F xs j) :
    F j ⊆ F i :=
  hj.2 i hij hi.1

/-- Critical indices in the finite scope `0, ..., t`. -/
noncomputable def exhaustiveCriticalIndices
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) : Finset ℕ := by
  classical
  exact (Finset.range (t + 1)).filter (ExhaustiveHistoryCritical F xs)

@[simp] theorem mem_exhaustiveCriticalIndices
    {F : ℕ → Set α} {t i : ℕ} {xs : Fin t → α} :
    i ∈ exhaustiveCriticalIndices F xs ↔
      i ≤ t ∧ ExhaustiveHistoryCritical F xs i := by
  classical
  simp [exhaustiveCriticalIndices, Nat.lt_succ_iff]

/-- The last critical language at this history.  The fallback is used only
before the scope contains a consistent candidate. -/
noncomputable def exhaustiveFocus
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) : ℕ := by
  classical
  let candidates := exhaustiveCriticalIndices F xs
  exact if h : candidates.Nonempty then candidates.max' h else 0

/-- Once a critical target index is in scope, the focus is critical and no
earlier than that target. -/
theorem exhaustiveFocus_spec
    {F : ℕ → Set α} {t z : ℕ} {xs : Fin t → α}
    (hzt : z ≤ t) (hz : ExhaustiveHistoryCritical F xs z) :
    exhaustiveFocus F xs ≤ t ∧
      ExhaustiveHistoryCritical F xs (exhaustiveFocus F xs) ∧
      z ≤ exhaustiveFocus F xs := by
  classical
  let candidates := exhaustiveCriticalIndices F xs
  have hzmem : z ∈ candidates := by
    simpa [candidates] using (mem_exhaustiveCriticalIndices.mpr ⟨hzt, hz⟩)
  have hne : candidates.Nonempty := ⟨z, hzmem⟩
  have hfmem : candidates.max' hne ∈ candidates := Finset.max'_mem candidates hne
  have hfocus : exhaustiveFocus F xs = candidates.max' hne := by
    simp [exhaustiveFocus, candidates, hne]
  rw [hfocus]
  have hparts : candidates.max' hne ≤ t ∧
      ExhaustiveHistoryCritical F xs (candidates.max' hne) := by
    simpa [candidates] using (mem_exhaustiveCriticalIndices.mp hfmem)
  exact ⟨hparts.1, hparts.2, Finset.le_max' candidates z hzmem⟩

theorem exhaustiveHistoryConsistent_prefix_iff
    {F : ℕ → Set α} {stream : GenLimit.Generic.Stream α} {t i : ℕ} :
    ExhaustiveHistoryConsistent F (fun j : Fin t ↦ stream j) i ↔
      (↑(GenLimit.Generic.sample stream t) : Set α) ⊆ F i := by
  rw [ExhaustiveHistoryConsistent, GenLimit.Generic.sequenceSample_prefix]

theorem exhaustiveCandidate_eventually_consistent_iff_target_subset
    {F : ℕ → Set α} {stream : GenLimit.Generic.Stream α} {z i : ℕ}
    (hP : GenLimit.Generic.Presents stream (F z)) :
    ∃ T, ∀ t, T ≤ t →
      (ExhaustiveHistoryConsistent F (fun j : Fin t ↦ stream j) i ↔
        F z ⊆ F i) := by
  classical
  by_cases hsub : F z ⊆ F i
  · refine ⟨0, ?_⟩
    intro t _
    constructor
    · intro _
      exact hsub
    · intro _ x hx
      have hxSample : x ∈ GenLimit.Generic.sample stream t := by
        rw [← GenLimit.Generic.sequenceSample_prefix stream t]
        exact hx
      exact hsub (GenLimit.Generic.mem_language_of_mem_sample_of_presents hP hxSample)
  · obtain ⟨x, hxz, hxi⟩ := Set.not_subset.mp hsub
    obtain ⟨T, hT⟩ := GenLimit.Generic.eventually_mem_sample_of_presents hP hxz
    refine ⟨T, ?_⟩
    intro t ht
    constructor
    · intro hcon
      exact (hxi (exhaustiveHistoryConsistent_prefix_iff.mp hcon (hT t ht))).elim
    · intro hsub'
      exact (hsub hsub').elim

/-- Uniform stabilization of consistency over a finite prefix of indices. -/
theorem exhaustiveFiniteScope_eventually_consistent_iff_target_subset
    {F : ℕ → Set α} {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (F z)) (scope : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < scope →
      (ExhaustiveHistoryConsistent F (fun j : Fin t ↦ stream j) i ↔
        F z ⊆ F i) := by
  induction scope with
  | zero =>
      exact ⟨0, by omega⟩
  | succ scope ih =>
      obtain ⟨Ts, hTs⟩ := ih
      obtain ⟨Ti, hTi⟩ :=
        exhaustiveCandidate_eventually_consistent_iff_target_subset
          (F := F) (stream := stream) (z := z) (i := scope) hP
      refine ⟨max Ts Ti, ?_⟩
      intro t ht i his
      rcases Nat.lt_succ_iff_lt_or_eq.mp his with his | rfl
      · exact hTs t ((Nat.le_max_left _ _).trans ht) i his
      · exact hTi t ((Nat.le_max_right _ _).trans ht)

/-- The target is eventually critical, the stability fact used in the proof
of Proposition 6.2. -/
theorem exhaustiveTarget_eventually_critical
    {F : ℕ → Set α} {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (F z)) :
    ∃ T, ∀ t, T ≤ t →
      ExhaustiveHistoryCritical F (fun j : Fin t ↦ stream j) z := by
  obtain ⟨T, hT⟩ :=
    exhaustiveFiniteScope_eventually_consistent_iff_target_subset hP (z + 1)
  refine ⟨T, ?_⟩
  intro t ht
  constructor
  · rw [exhaustiveHistoryConsistent_prefix_iff]
    intro x hx
    exact GenLimit.Generic.mem_language_of_mem_sample_of_presents hP hx
  · intro i hiz hicon
    exact (hT t ht i (Nat.lt_succ_of_le hiz)).mp hicon

/-- Earlier critical indices whose difference from the focus is finite. -/
noncomputable def exhaustiveAugmentationIndices
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) : Finset ℕ := by
  classical
  let f := exhaustiveFocus F xs
  exact (Finset.range (f + 1)).filter fun j ↦
    ExhaustiveHistoryCritical F xs j ∧ (F j \ F f).Finite

@[simp] theorem mem_exhaustiveAugmentationIndices
    {F : ℕ → Set α} {t j : ℕ} {xs : Fin t → α} :
    j ∈ exhaustiveAugmentationIndices F xs ↔
      j ≤ exhaustiveFocus F xs ∧
        ExhaustiveHistoryCritical F xs j ∧
        (F j \ F (exhaustiveFocus F xs)).Finite := by
  classical
  simp [exhaustiveAugmentationIndices, Nat.lt_succ_iff]

/-- The finite augmentation added to the last critical language. -/
noncomputable def exhaustiveAugmentationExtra
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) : Set α :=
  ⋃ j ∈ (↑(exhaustiveAugmentationIndices F xs) : Set ℕ),
    (F j \ F (exhaustiveFocus F xs))

/-- The set `Z_{≥t}` built in the proof of Proposition 6.2. -/
noncomputable def exhaustiveOracleSet
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) : Set α :=
  F (exhaustiveFocus F xs) ∪ exhaustiveAugmentationExtra F xs

theorem exhaustiveAugmentationExtra_finite
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) :
    (exhaustiveAugmentationExtra F xs).Finite := by
  classical
  apply (exhaustiveAugmentationIndices F xs).finite_toSet.biUnion
  intro j hj
  exact (mem_exhaustiveAugmentationIndices.mp hj).2.2

theorem exhaustiveOracleSet_infinite
    (F : ℕ → Set α) (hInfinite : ∀ i, (F i).Infinite)
    {t : ℕ} (xs : Fin t → α) :
    (exhaustiveOracleSet F xs).Infinite :=
  (hInfinite (exhaustiveFocus F xs)).mono Set.subset_union_left

theorem language_subset_exhaustiveOracleSet_of_augmented
    {F : ℕ → Set α} {t j : ℕ} {xs : Fin t → α}
    (hj : j ∈ exhaustiveAugmentationIndices F xs) :
    F j ⊆ exhaustiveOracleSet F xs := by
  intro x hx
  by_cases hfocus : x ∈ F (exhaustiveFocus F xs)
  · exact Or.inl hfocus
  · right
    exact Set.mem_iUnion_of_mem j
      (Set.mem_iUnion_of_mem (show j ∈ (↑(exhaustiveAugmentationIndices F xs) : Set ℕ) from hj)
        ⟨hx, hfocus⟩)

theorem exhaustiveOracleSet_diff_focus_finite
    (F : ℕ → Set α) {t : ℕ} (xs : Fin t → α) :
    (exhaustiveOracleSet F xs \ F (exhaustiveFocus F xs)).Finite := by
  apply (exhaustiveAugmentationExtra_finite F xs).subset
  rintro x ⟨hx, hnot⟩
  rcases hx with hx | hx
  · exact (hnot hx).elim
  · exact hx

/-- The paper's strong-oracle algorithm: select the last critical language,
add the finite differences certified by the finiteness oracle, and enumerate
the resulting set. -/
noncomputable def exhaustiveSemanticOracleAlgorithm
    [Countable α] (F : ℕ → Set α) (hInfinite : ∀ i, (F i).Infinite) :
    ExhaustiveAlgorithm α :=
  fun _ xs ↦ GenLimit.Support.infiniteEnumeration (exhaustiveOracleSet F xs)
    (exhaustiveOracleSet_infinite F hInfinite xs)

theorem generateOnly_exhaustiveSemanticOracleAlgorithm
    [Countable α] (F : ℕ → Set α) (hInfinite : ∀ i, (F i).Infinite)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    generateOnly (exhaustiveSemanticOracleAlgorithm F hInfinite) stream t =
      exhaustiveOracleSet F (fun j : Fin t ↦ stream j) := by
  simpa only [generateOnly, generatorAt, exhaustiveSemanticOracleAlgorithm] using
    GenLimit.Support.infiniteEnumeration_presents
      (exhaustiveOracleSet F (fun j : Fin t ↦ stream j))
      (exhaustiveOracleSet_infinite F hInfinite (fun j : Fin t ↦ stream j))

/-- Eventual correctness of the strong-oracle set for one presented target. -/
theorem exhaustiveOracleSet_eventually_approximates_target
    {F : ℕ → Set α} (hWeak : WeakAngluinExistence (Set.range F))
    {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (F z)) :
    ∃ T, ∀ t, T ≤ t →
      (exhaustiveOracleSet F (fun j : Fin t ↦ stream j) \ F z).Finite ∧
        F z ⊆ exhaustiveOracleSet F (fun j : Fin t ↦ stream j) := by
  classical
  obtain ⟨tell, htellTarget, htell⟩ := hWeak (F z) ⟨z, rfl⟩
  obtain ⟨Ttell, hTtell⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hP tell htellTarget
  obtain ⟨Tcritical, hTcritical⟩ := exhaustiveTarget_eventually_critical hP
  refine ⟨max (max Ttell Tcritical) z, ?_⟩
  intro t ht
  let xs : Fin t → α := fun j ↦ stream j
  let f := exhaustiveFocus F xs
  have htellTime : Ttell ≤ t :=
    (Nat.le_max_left Ttell Tcritical).trans
      ((Nat.le_max_left (max Ttell Tcritical) z).trans ht)
  have hcriticalTime : Tcritical ≤ t :=
    (Nat.le_max_right Ttell Tcritical).trans
      ((Nat.le_max_left (max Ttell Tcritical) z).trans ht)
  have hzt : z ≤ t := (Nat.le_max_right (max Ttell Tcritical) z).trans ht
  have hzcritical : ExhaustiveHistoryCritical F xs z := hTcritical t hcriticalTime
  have hfocus := exhaustiveFocus_spec hzt hzcritical
  have hfocusSub : F f ⊆ F z := by
    exact exhaustiveHistoryCritical_subset_of_le hfocus.2.2 hzcritical hfocus.2.1
  have htellSample : tell ⊆ GenLimit.Generic.sample stream t :=
    hTtell.trans (GenLimit.Generic.sample_mono htellTime)
  have hsampleFocus : (↑(GenLimit.Generic.sample stream t) : Set α) ⊆ F f := by
    simpa [xs, f, exhaustiveHistoryConsistent_prefix_iff] using hfocus.2.1.1
  have htellFocus : (↑tell : Set α) ⊆ F f := by
    intro x hx
    exact hsampleFocus (htellSample hx)
  have hdiff : (F z \ F f).Finite := by
    by_cases heq : F f = F z
    · simp [heq]
    · exact htell (F f) ⟨f, rfl⟩ htellFocus
        (Set.ssubset_iff_subset_ne.mpr ⟨hfocusSub, heq⟩)
  have hzaugmented : z ∈ exhaustiveAugmentationIndices F xs := by
    exact mem_exhaustiveAugmentationIndices.mpr
      ⟨hfocus.2.2, hzcritical, by simpa [f] using hdiff⟩
  have htargetSubset : F z ⊆ exhaustiveOracleSet F xs :=
    language_subset_exhaustiveOracleSet_of_augmented hzaugmented
  constructor
  · apply (exhaustiveOracleSet_diff_focus_finite F xs).subset
    rintro x ⟨hx, hxz⟩
    exact ⟨hx, fun hxf ↦ hxz (hfocusSub hxf)⟩
  · exact htargetSubset

/-- Proposition 6.2, at exactly the semantic strong-oracle level described in
the paper. -/
theorem proposition6_2_exhaustive_sufficient_semantic_oracle
    [Countable α] (F : ℕ → Set α) (hInfinite : ∀ i, (F i).Infinite)
    (hWeak : WeakAngluinExistence (Set.range F)) :
    ExhaustivelyGeneratable (Set.range F) := by
  refine ⟨exhaustiveSemanticOracleAlgorithm F hInfinite, ?_⟩
  intro K hK stream hP
  obtain ⟨z, rfl⟩ := hK
  obtain ⟨T, hT⟩ := exhaustiveOracleSet_eventually_approximates_target hWeak hP
  refine ⟨T, ?_⟩
  intro t ht
  have hApprox := hT t ht
  constructor
  · simpa [generateOnly_exhaustiveSemanticOracleAlgorithm] using hApprox.1
  · intro x hx
    right
    simpa [generateOnly_exhaustiveSemanticOracleAlgorithm] using hApprox.2 hx

/-! ## The adversarial diagonal in Proposition 6.1 -/

/-- Equation (8) in the paper: `L` has no weak Angluin tell-tale. -/
def WeakAngluinFailureAt
    (C : GenLimit.Generic.LanguageClass α) (L : GenLimit.Generic.Language α) : Prop :=
  ∀ T : Finset α, (↑T : Set α) ⊆ L →
    ∃ L', L' ∈ C ∧ (↑T : Set α) ⊆ L' ∧ L' ⊂ L ∧ (L \ L').Infinite

theorem not_weakAngluinExistence_iff_exists_failureAt
    (C : GenLimit.Generic.LanguageClass α) :
    ¬ WeakAngluinExistence C ↔
      ∃ L, L ∈ C ∧ WeakAngluinFailureAt C L := by
  classical
  rw [WeakAngluinExistence]
  push_neg
  rfl

/-- All data needed for the infinite diagonal in Proposition 6.1. -/
structure ExhaustiveDiagonalProblem (α : Type*) [Countable α] where
  collection : GenLimit.Generic.LanguageClass α
  target : GenLimit.Generic.Language α
  target_mem : target ∈ collection
  targetEnumeration : GenLimit.Generic.Stream α
  targetEnumeration_presents :
    GenLimit.Generic.Presents targetEnumeration target
  languages_infinite : ∀ K, K ∈ collection → K.Infinite
  algorithm : ExhaustiveAlgorithm α
  algorithm_correct : IsExhaustiveGenerator algorithm collection
  failure : WeakAngluinFailureAt collection target

/-- A finite committed prefix of the adversarial target presentation. -/
structure ExhaustiveDiagonalPrefix
    [Countable α] (D : ExhaustiveDiagonalProblem α) where
  length : ℕ
  stream : GenLimit.Generic.Stream α
  mem_target : ∀ n < length, stream n ∈ D.target

/-- Extend a committed prefix by a fixed enumeration of `K`. -/
noncomputable def exhaustivePrefixExtension
    [Countable α] (D : ExhaustiveDiagonalProblem α)
    (P : ExhaustiveDiagonalPrefix D) (K : Set α) (hK : K.Infinite) :
    GenLimit.Generic.Stream α :=
  fun n ↦ if n < P.length then P.stream n
    else GenLimit.Support.infiniteEnumeration K hK (n - P.length)

theorem exhaustivePrefixExtension_agrees
    [Countable α] (D : ExhaustiveDiagonalProblem α)
    (P : ExhaustiveDiagonalPrefix D) (K : Set α) (hK : K.Infinite)
    {n : ℕ} (hn : n < P.length) :
    exhaustivePrefixExtension D P K hK n = P.stream n := by
  simp [exhaustivePrefixExtension, hn]

theorem exhaustivePrefixExtension_mem
    [Countable α] (D : ExhaustiveDiagonalProblem α)
    (P : ExhaustiveDiagonalPrefix D) (K : Set α) (hK : K.Infinite)
    (hprefix : ∀ n < P.length, P.stream n ∈ K) (n : ℕ) :
    exhaustivePrefixExtension D P K hK n ∈ K := by
  by_cases hn : n < P.length
  · simpa [exhaustivePrefixExtension, hn] using hprefix n hn
  · simp only [exhaustivePrefixExtension, if_neg hn]
    exact GenLimit.Support.infiniteEnumeration_mem K hK (n - P.length)

theorem exhaustivePrefixExtension_presents
    [Countable α] (D : ExhaustiveDiagonalProblem α)
    (P : ExhaustiveDiagonalPrefix D) (K : Set α) (hK : K.Infinite)
    (hprefix : ∀ n < P.length, P.stream n ∈ K) :
    GenLimit.Generic.Presents (exhaustivePrefixExtension D P K hK) K := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact exhaustivePrefixExtension_mem D P K hK hprefix n
  · intro x hx
    obtain ⟨n, rfl⟩ :=
      GenLimit.Support.infiniteEnumeration_surjective K hK hx
    refine ⟨P.length + n, ?_⟩
    have hnot : ¬ P.length + n < P.length :=
      Nat.not_lt_of_ge (Nat.le_add_right P.length n)
    simp [exhaustivePrefixExtension, hnot]

/-- One phase of the diagonal.  Its witness language contains the old prefix,
the algorithm is allowed to settle on that witness, and the next element of a
fixed target enumeration is then appended. -/
structure ExhaustiveDiagonalStep
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ)
    (P : ExhaustiveDiagonalPrefix D) where
  witness : Set α
  witness_mem : witness ∈ D.collection
  witness_subset_target : witness ⊂ D.target
  target_gap_infinite : (D.target \ witness).Infinite
  endpoint : ℕ
  next : ExhaustiveDiagonalPrefix D
  next_length : next.length = endpoint + 1
  growth : P.length + 1 ≤ next.length
  endpoint_lt : endpoint < next.length
  agrees : ∀ n < P.length, next.stream n = P.stream n
  future_finite :
    (generateOnly D.algorithm next.stream endpoint \ witness).Finite
  appended_value : next.stream endpoint = D.targetEnumeration i

/-- Carry out one phase of Proposition 6.1's adversarial construction. -/
noncomputable def buildExhaustiveDiagonalStep
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ)
    (P : ExhaustiveDiagonalPrefix D) : ExhaustiveDiagonalStep D i P := by
  classical
  let T := GenLimit.Generic.sample P.stream P.length
  have hTtarget : (↑T : Set α) ⊆ D.target := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hx
    exact P.mem_target n hn
  let hWitness := D.failure T hTtarget
  let K := Classical.choose hWitness
  have hKparts := Classical.choose_spec hWitness
  have hKmem : K ∈ D.collection := hKparts.1
  have hTK : (↑T : Set α) ⊆ K := hKparts.2.1
  have hKproper : K ⊂ D.target := hKparts.2.2.1
  have hGap : (D.target \ K).Infinite := hKparts.2.2.2
  have hKInfinite : K.Infinite := D.languages_infinite K hKmem
  have hprefixK : ∀ n < P.length, P.stream n ∈ K := by
    intro n hn
    exact hTK (GenLimit.Generic.value_mem_sample hn)
  let phaseStream := exhaustivePrefixExtension D P K hKInfinite
  have hPhasePresents : GenLimit.Generic.Presents phaseStream K :=
    exhaustivePrefixExtension_presents D P K hKInfinite hprefixK
  let hSettles := D.algorithm_correct K hKmem phaseStream hPhasePresents
  let tStar := Classical.choose hSettles
  have hAfter := Classical.choose_spec hSettles
  let e := max tStar P.length
  have heStar : tStar ≤ e := Nat.le_max_left _ _
  have heLength : P.length ≤ e := Nat.le_max_right _ _
  have hFuturePhase :
      (generateOnly D.algorithm phaseStream e \ K).Finite :=
    (hAfter e heStar).1
  let nextStream : GenLimit.Generic.Stream α := fun n ↦
    if n < e then phaseStream n else D.targetEnumeration i
  have hEnumTarget : D.targetEnumeration i ∈ D.target := by
    rw [← D.targetEnumeration_presents]
    exact Set.mem_range_self i
  have hnextTarget : ∀ n < e + 1, nextStream n ∈ D.target := by
    intro n hn
    by_cases hne : n < e
    · have hmemK : phaseStream n ∈ K :=
        exhaustivePrefixExtension_mem D P K hKInfinite hprefixK n
      simpa only [nextStream, if_pos hne] using hKproper.subset hmemK
    · have hne' : n = e := by omega
      subst n
      simp [nextStream, hEnumTarget]
  let next : ExhaustiveDiagonalPrefix D := ⟨e + 1, nextStream, hnextTarget⟩
  have hagrees : ∀ n < P.length, next.stream n = P.stream n := by
    intro n hn
    have hne : n < e := lt_of_lt_of_le hn heLength
    simp only [next, nextStream, if_pos hne]
    exact exhaustivePrefixExtension_agrees D P K hKInfinite hn
  have hHistory :
      (fun j : Fin e ↦ next.stream j) = (fun j : Fin e ↦ phaseStream j) := by
    funext j
    simp only [next, nextStream, if_pos j.isLt]
  have hFutureEq :
      generateOnly D.algorithm next.stream e =
        generateOnly D.algorithm phaseStream e := by
    simp only [generateOnly, generatorAt]
    rw [hHistory]
  refine
    { witness := K
      witness_mem := hKmem
      witness_subset_target := hKproper
      target_gap_infinite := hGap
      endpoint := e
      next := next
      next_length := rfl
      growth := by simp only [next]; omega
      endpoint_lt := by simp [next]
      agrees := hagrees
      future_finite := ?_
      appended_value := by simp [next, nextStream]
    }
  rwa [hFutureEq]

/-- The empty initial prefix. -/
def initialExhaustiveDiagonalPrefix
    [Countable α] (D : ExhaustiveDiagonalProblem α) :
    ExhaustiveDiagonalPrefix D where
  length := 0
  stream := D.targetEnumeration
  mem_target := by omega

/-- The nested prefixes generated by Proposition 6.1's phases. -/
noncomputable def exhaustiveDiagonalPrefix
    [Countable α] (D : ExhaustiveDiagonalProblem α) :
    ℕ → ExhaustiveDiagonalPrefix D
  | 0 => initialExhaustiveDiagonalPrefix D
  | i + 1 =>
      (buildExhaustiveDiagonalStep D i (exhaustiveDiagonalPrefix D i)).next

/-- The step attached to phase `i`. -/
noncomputable def exhaustiveDiagonalStep
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ) :
    ExhaustiveDiagonalStep D i (exhaustiveDiagonalPrefix D i) :=
  buildExhaustiveDiagonalStep D i (exhaustiveDiagonalPrefix D i)

@[simp] theorem exhaustiveDiagonalPrefix_succ
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ) :
    exhaustiveDiagonalPrefix D (i + 1) = (exhaustiveDiagonalStep D i).next := by
  rfl

theorem exhaustiveDiagonalPrefix_length_lowerBound
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ) :
    i ≤ (exhaustiveDiagonalPrefix D i).length := by
  induction i with
  | zero => simp [exhaustiveDiagonalPrefix, initialExhaustiveDiagonalPrefix]
  | succ i ih =>
      rw [exhaustiveDiagonalPrefix_succ]
      exact (Nat.succ_le_succ ih).trans (exhaustiveDiagonalStep D i).growth

theorem exhaustiveDiagonalPrefix_length_mono
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ) :
    (exhaustiveDiagonalPrefix D i).length ≤
      (exhaustiveDiagonalPrefix D (i + 1)).length := by
  rw [exhaustiveDiagonalPrefix_succ]
  exact (Nat.le_succ _).trans (exhaustiveDiagonalStep D i).growth

theorem exhaustiveDiagonalPrefix_length_mono_iterate
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i k : ℕ) :
    (exhaustiveDiagonalPrefix D i).length ≤
      (exhaustiveDiagonalPrefix D (i + k)).length := by
  induction k with
  | zero => simp
  | succ k ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using exhaustiveDiagonalPrefix_length_mono D (i + k))

theorem exhaustiveDiagonalPrefix_agrees_iterate
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i k n : ℕ)
    (hn : n < (exhaustiveDiagonalPrefix D i).length) :
    (exhaustiveDiagonalPrefix D (i + k)).stream n =
      (exhaustiveDiagonalPrefix D i).stream n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show i + (k + 1) = (i + k) + 1 by omega,
        exhaustiveDiagonalPrefix_succ]
      rw [(exhaustiveDiagonalStep D (i + k)).agrees n
        (lt_of_lt_of_le hn (exhaustiveDiagonalPrefix_length_mono_iterate D i k))]
      exact ih

theorem exhaustiveDiagonalPrefix_agrees_of_le
    [Countable α] (D : ExhaustiveDiagonalProblem α) {i j n : ℕ}
    (hij : i ≤ j) (hn : n < (exhaustiveDiagonalPrefix D i).length) :
    (exhaustiveDiagonalPrefix D j).stream n =
      (exhaustiveDiagonalPrefix D i).stream n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact exhaustiveDiagonalPrefix_agrees_iterate D i k n hn

/-- The limiting adversarial presentation. -/
noncomputable def exhaustiveDiagonalStream
    [Countable α] (D : ExhaustiveDiagonalProblem α) :
    GenLimit.Generic.Stream α :=
  fun n ↦ (exhaustiveDiagonalPrefix D (n + 1)).stream n

theorem exhaustiveDiagonalStream_agrees
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i n : ℕ)
    (hn : n < (exhaustiveDiagonalPrefix D i).length) :
    exhaustiveDiagonalStream D n = (exhaustiveDiagonalPrefix D i).stream n := by
  unfold exhaustiveDiagonalStream
  by_cases hni : i ≤ n + 1
  · exact exhaustiveDiagonalPrefix_agrees_of_le D hni hn
  · have hle : n + 1 ≤ i := by omega
    symm
    apply exhaustiveDiagonalPrefix_agrees_of_le D hle
    have hbound := exhaustiveDiagonalPrefix_length_lowerBound D (n + 1)
    omega

theorem exhaustiveDiagonalStream_mem_target
    [Countable α] (D : ExhaustiveDiagonalProblem α) (n : ℕ) :
    exhaustiveDiagonalStream D n ∈ D.target := by
  unfold exhaustiveDiagonalStream
  apply (exhaustiveDiagonalPrefix D (n + 1)).mem_target
  have hbound := exhaustiveDiagonalPrefix_length_lowerBound D (n + 1)
  omega

theorem exhaustiveDiagonalStream_hits_targetEnumeration
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ) :
    ∃ n, exhaustiveDiagonalStream D n = D.targetEnumeration i := by
  let e := (exhaustiveDiagonalStep D i).endpoint
  refine ⟨e, ?_⟩
  rw [exhaustiveDiagonalStream_agrees D (i + 1) e]
  · rw [exhaustiveDiagonalPrefix_succ]
    exact (exhaustiveDiagonalStep D i).appended_value
  · rw [exhaustiveDiagonalPrefix_succ]
    exact (exhaustiveDiagonalStep D i).endpoint_lt

theorem exhaustiveDiagonalStream_presents_target
    [Countable α] (D : ExhaustiveDiagonalProblem α) :
    GenLimit.Generic.Presents (exhaustiveDiagonalStream D) D.target := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact exhaustiveDiagonalStream_mem_target D n
  · intro x hx
    rw [← D.targetEnumeration_presents] at hx
    obtain ⟨i, rfl⟩ := hx
    exact exhaustiveDiagonalStream_hits_targetEnumeration D i

theorem exhaustiveDiagonalStream_generateOnly_at_endpoint
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ) :
    generateOnly D.algorithm (exhaustiveDiagonalStream D)
        (exhaustiveDiagonalStep D i).endpoint =
      generateOnly D.algorithm (exhaustiveDiagonalPrefix D (i + 1)).stream
        (exhaustiveDiagonalStep D i).endpoint := by
  simp only [generateOnly, generatorAt]
  congr 2
  funext j
  apply exhaustiveDiagonalStream_agrees D (i + 1) j
  rw [exhaustiveDiagonalPrefix_succ]
  exact lt_trans j.isLt (exhaustiveDiagonalStep D i).endpoint_lt

theorem exhaustiveDiagonal_endpoint_future_finite
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ) :
    (generateOnly D.algorithm (exhaustiveDiagonalStream D)
      (exhaustiveDiagonalStep D i).endpoint \
        (exhaustiveDiagonalStep D i).witness).Finite := by
  rw [exhaustiveDiagonalStream_generateOnly_at_endpoint D i]
  rw [exhaustiveDiagonalPrefix_succ]
  exact (exhaustiveDiagonalStep D i).future_finite

theorem exhaustiveDiagonal_endpoint_ge_phase
    [Countable α] (D : ExhaustiveDiagonalProblem α) (i : ℕ) :
    i ≤ (exhaustiveDiagonalStep D i).endpoint := by
  have hlen := exhaustiveDiagonalPrefix_length_lowerBound D i
  have hgrowth := (exhaustiveDiagonalStep D i).growth
  rw [(exhaustiveDiagonalStep D i).next_length] at hgrowth
  omega

/-- The diagonal data are contradictory: the finite history and past outputs
cannot cover an infinite target gap after finitely many future errors. -/
theorem exhaustiveDiagonalProblem_false
    [Countable α] (D : ExhaustiveDiagonalProblem α) : False := by
  let stream := exhaustiveDiagonalStream D
  have hPresents : GenLimit.Generic.Presents stream D.target :=
    exhaustiveDiagonalStream_presents_target D
  obtain ⟨tStar, hAfter⟩ :=
    D.algorithm_correct D.target D.target_mem stream hPresents
  let i := tStar
  let e := (exhaustiveDiagonalStep D i).endpoint
  let K := (exhaustiveDiagonalStep D i).witness
  have hei : i ≤ e := exhaustiveDiagonal_endpoint_ge_phase D i
  have hCorrect := hAfter e hei
  have hFutureFinite : (generateOnly D.algorithm stream e \ K).Finite := by
    simpa [stream, e, K] using exhaustiveDiagonal_endpoint_future_finite D i
  have hGapInfinite : (D.target \ K).Infinite :=
    (exhaustiveDiagonalStep D i).target_gap_infinite
  have hUncoveredInfinite :
      ((D.target \ K) \ (generateOnly D.algorithm stream e \ K)).Infinite :=
    hGapInfinite.diff hFutureFinite
  have hEarlierFinite :
      ((↑(GenLimit.Generic.sample stream e) : Set α) ∪
        generatedBefore D.algorithm stream e).Finite :=
    (GenLimit.Generic.sample stream e).finite_toSet.union
      (generatedBefore_finite D.algorithm stream e)
  apply hUncoveredInfinite
  apply hEarlierFinite.subset
  intro x hx
  have hxCover := hCorrect.2 hx.1.1
  rcases hxCover with hxEarlier | hxFuture
  · exact hxEarlier
  · exact (hx.2 ⟨hxFuture, hx.1.2⟩).elim

/-- Proposition 6.1: exhaustive generation implies Weak Angluin's Condition
with Existence. -/
theorem proposition6_1_exhaustive_necessary
    [Countable α] (C : GenLimit.Generic.LanguageClass α)
    (hInfinite : ∀ K, K ∈ C → K.Infinite)
    (hGenerate : ExhaustivelyGeneratable C) :
    WeakAngluinExistence C := by
  by_contra hWeak
  obtain ⟨L, hLC, hFailure⟩ :=
    (not_weakAngluinExistence_iff_exists_failureAt C).mp hWeak
  obtain ⟨A, hA⟩ := hGenerate
  let base := GenLimit.Support.infiniteEnumeration L (hInfinite L hLC)
  have hBase : GenLimit.Generic.Presents base L := by
    exact GenLimit.Support.infiniteEnumeration_presents L (hInfinite L hLC)
  let D : ExhaustiveDiagonalProblem α :=
    { collection := C
      target := L
      target_mem := hLC
      targetEnumeration := base
      targetEnumeration_presents := hBase
      languages_infinite := hInfinite
      algorithm := A
      algorithm_correct := hA
      failure := hFailure }
  exact exhaustiveDiagonalProblem_false D

/-! ## Overview Theorem 4 -/

/-- Overview Theorem 4 for a countably indexed collection of infinite
languages over a countable universe. -/
theorem theorem4_exhaustive_generation_characterization
    [Countable α] (F : ℕ → Set α) (hInfinite : ∀ i, (F i).Infinite) :
    ExhaustivelyGeneratable (Set.range F) ↔
      WeakAngluinExistence (Set.range F) := by
  constructor
  · apply proposition6_1_exhaustive_necessary
    intro K hK
    obtain ⟨i, rfl⟩ := hK
    exact hInfinite i
  · exact proposition6_2_exhaustive_sufficient_semantic_oracle F hInfinite

end GenLimit.CharikarPabbaraju
