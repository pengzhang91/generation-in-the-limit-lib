import GenLimit.Paper21_GenerationInMetricSpaces.NonuniformCharacterization
import GenLimit.Paper21_GenerationInMetricSpaces.Common.WeightedStarMetric
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Sequences

/-!
# Diagnostic for the printed necessity in metric Theorem 3.3

The ambient space is a countable weighted star.  Its leaves consist of a
shared core and one leaf for every finite Boolean word.  A target indexed by
an infinite Boolean stream contains the shared core and exactly the leaves
labelled by its finite prefixes.

The common core gives one uniform generator for the entire uncountable
class.  Distinct targets have only finitely many common prefix leaves, so
every subclass containing two targets has infinite scale-closure dimension.
Consequently the class cannot be a countable increasing union of subclasses
with finite scale-closure dimension.
-/

namespace GenLimit.MetricSpaces.Theorem33Counterexample

/-- The separable weighted-prefix star. -/
inductive PrefixPoint where
  | hub
  | core (n : ℕ)
  | branch (word : List Bool)
  deriving DecidableEq

open PrefixPoint

private def pointCode :
    PrefixPoint → Unit ⊕ (ℕ ⊕ List Bool)
  | hub => Sum.inl ()
  | core n => Sum.inr (Sum.inl n)
  | branch word => Sum.inr (Sum.inr word)

private theorem pointCode_injective :
    Function.Injective pointCode := by
  intro x y h
  cases x <;> cases y <;>
    simp_all [pointCode]

instance instCountablePrefixPoint : Countable PrefixPoint :=
  pointCode_injective.countable

private def weight : PrefixPoint → ℝ
  | hub => 0
  | core _ => 1
  | branch _ => 3

/-- Distinct points have distance equal to the sum of their edge weights
to the hub. -/
def prefixStarDistance
    (x y : PrefixPoint) : ℝ :=
  if x = y then 0 else weight x + weight y

private theorem weight_nonneg (x : PrefixPoint) :
    0 ≤ weight x := by
  cases x <;> norm_num [weight]

private theorem weight_pos_of_ne_hub
    {x : PrefixPoint} (hx : x ≠ hub) :
    0 < weight x := by
  cases x <;> simp_all [weight]

@[simp] private theorem prefixStarDistance_self
    (x : PrefixPoint) :
    prefixStarDistance x x = 0 :=
  WeightedStar.distance_self weight x

private theorem prefixStarDistance_comm
    (x y : PrefixPoint) :
    prefixStarDistance x y =
      prefixStarDistance y x :=
  WeightedStar.distance_comm weight x y

private theorem prefixStarDistance_triangle
    (x y z : PrefixPoint) :
    prefixStarDistance x z ≤
      prefixStarDistance x y +
        prefixStarDistance y z :=
  WeightedStar.distance_triangle weight weight_nonneg x y z

private theorem weight_pair_pos
    {x y : PrefixPoint} (hxy : x ≠ y) :
    0 < weight x + weight y := by
  have hnotBothHub : x ≠ hub ∨ y ≠ hub := by
    by_contra h
    push_neg at h
    exact hxy (h.1.trans h.2.symm)
  rcases hnotBothHub with hx | hy
  · exact add_pos_of_pos_of_nonneg
      (weight_pos_of_ne_hub hx) (weight_nonneg y)
  · exact add_pos_of_nonneg_of_pos
      (weight_nonneg x) (weight_pos_of_ne_hub hy)

/-- The kernel used below is a genuine metric. -/
instance instMetricSpacePrefixPoint :
    MetricSpace PrefixPoint where
  dist := prefixStarDistance
  dist_self := prefixStarDistance_self
  dist_comm := prefixStarDistance_comm
  dist_triangle := prefixStarDistance_triangle
  eq_of_dist_eq_zero :=
    WeightedStar.eq_of_distance_eq_zero weight weight_pair_pos

/-- The example space is countable, hence separable. -/
theorem prefixPoint_separable :
    TopologicalSpace.SeparableSpace PrefixPoint := by
  infer_instance

/-- The Boolean word of length `n` cut from an infinite stream. -/
def bitPrefix (bits : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn fun i : Fin n ↦ bits i

@[simp] private theorem prefix_length
    (bits : ℕ → Bool) (n : ℕ) :
    (bitPrefix bits n).length = n := by
  simp [bitPrefix]

private theorem prefix_get
    (bits : ℕ → Bool) {n k : ℕ} (hk : k < n) :
    (bitPrefix bits n).get ⟨k, by simpa using hk⟩ =
      bits k := by
  simp [bitPrefix]

/-- A target contains the shared core and the branch leaves labelled by all
finite prefixes of `bits`; it omits the hub. -/
def target (bits : ℕ → Bool) : Set PrefixPoint
  | hub => False
  | core _ => True
  | branch word => ∃ n, word = bitPrefix bits n

/-- The uncountable target class. -/
def prefixStarClass :
    GenLimit.Generic.LanguageClass PrefixPoint :=
  Set.range target

@[simp] private theorem core_mem_target
    (bits : ℕ → Bool) (n : ℕ) :
    core n ∈ target bits := by
  trivial

@[simp] private theorem hub_not_mem_target
    (bits : ℕ → Bool) :
    hub ∉ target bits := by
  intro h
  exact h

private theorem branch_mem_target_iff
    (bits : ℕ → Bool) (word : List Bool) :
    branch word ∈ target bits ↔
      ∃ n, word = bitPrefix bits n := by
  rfl

private theorem prefix_eq_forces_bit_eq
    {bits other : ℕ → Bool} {n k : ℕ}
    (hk : k < n)
    (heq : bitPrefix bits n = bitPrefix other n) :
    bits k = other k := by
  have hget :=
    congrArg
      (fun word : List Bool => word[k]?) heq
  simpa [bitPrefix, hk] using hget

/-- Different bit streams determine different target languages. -/
theorem target_injective :
    Function.Injective target := by
  intro bits other htarget
  funext k
  have hmem :
      branch (bitPrefix bits (k + 1)) ∈ target bits :=
    (branch_mem_target_iff bits _).2
      ⟨k + 1, rfl⟩
  have hmemOther :
      branch (bitPrefix bits (k + 1)) ∈
        target other := by
    rw [← htarget]
    exact hmem
  obtain ⟨n, hn⟩ :=
    (branch_mem_target_iff other _).1 hmemOther
  have hnlen : n = k + 1 := by
    have :=
      congrArg List.length hn
    simpa using this.symm
  subst n
  exact
    prefix_eq_forces_bit_eq
      (Nat.lt_succ_self k) hn

private def coreSet : Set PrefixPoint
  | core _ => True
  | _ => False

private theorem core_injective :
    Function.Injective core := by
  intro n m h
  cases h
  rfl

private theorem coreSet_infinite :
    coreSet.Infinite := by
  have hrange :
      (Set.range core).Infinite :=
    Set.infinite_range_of_injective core_injective
  apply hrange.mono
  rintro x ⟨n, rfl⟩
  trivial

/-- Choose a shared core leaf absent from the finite history. -/
noncomputable def freshCoreGenerator :
    GenLimit.Generic.Generator PrefixPoint :=
  fun _ xs =>
    Classical.choose
      (coreSet_infinite.exists_notMem_finset
        (GenLimit.Generic.sequenceSample xs))

private theorem freshCoreGenerator_spec
    {t : ℕ} (xs : Fin t → PrefixPoint) :
    freshCoreGenerator t xs ∈ coreSet ∧
      freshCoreGenerator t xs ∉
        GenLimit.Generic.sequenceSample xs :=
  Classical.choose_spec
    (coreSet_infinite.exists_notMem_finset
      (GenLimit.Generic.sequenceSample xs))

private theorem coreSet_subset_target
    (bits : ℕ → Bool) :
    coreSet ⊆ target bits := by
  intro x hx
  cases x with
  | hub => exact False.elim hx
  | core n => exact core_mem_target bits n
  | branch word => exact False.elim hx

private theorem target_distinct_core_distance_ge_two
    {bits : ℕ → Bool} {x : PrefixPoint} {n : ℕ}
    (hx : x ∈ target bits) (hne : x ≠ core n) :
    2 ≤ prefixStarDistance x (core n) := by
  cases x with
  | hub => exact (hub_not_mem_target bits hx).elim
  | core m =>
      rw [prefixStarDistance, if_neg hne]
      norm_num [weight]
  | branch word =>
      rw [prefixStarDistance, if_neg (by simp)]
      norm_num [weight]

private theorem fresh_core_not_near_target_sample
    {bits : ℕ → Bool} {S : Finset PrefixPoint}
    (hS : (S : Set PrefixPoint) ⊆ target bits)
    {x : PrefixPoint} (hxCore : x ∈ coreSet)
    (hxFresh : x ∉ S) :
    x ∉ closedNeighborhood prefixStarDistance
      (S : Set PrefixPoint) 1 := by
  intro hnear
  cases x with
  | hub => exact hxCore
  | core n =>
      obtain ⟨y, hyS, hydist⟩ :=
        hnear (3 / 2 : ℝ) (by norm_num)
      have hyTarget : y ∈ target bits := hS hyS
      have hyNe : y ≠ core n := by
        intro hy
        subst y
        exact hxFresh hyS
      have hge :=
        target_distinct_core_distance_ge_two
          hyTarget hyNe
      linarith
  | branch word => exact hxCore

/-- One generator is uniformly correct for the entire uncountable class. -/
theorem freshCoreGenerator_isUniform :
    IsUniformGeneratorAt prefixStarDistance
      (1 / 2 : ℝ) 1 freshCoreGenerator
      prefixStarClass 1 := by
  intro L hL stream hstream _t _htrigger s _hts
  obtain ⟨bits, rfl⟩ := hL
  have hsampleTarget :
      (GenLimit.Generic.sample stream s : Set PrefixPoint) ⊆
        target bits := by
    intro x hx
    obtain ⟨i, _his, rfl⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hx
    exact hstream ⟨i, rfl⟩
  have hspec :=
    freshCoreGenerator_spec
      (fun i : Fin s ↦ stream i)
  rw [GenLimit.Generic.sequenceSample_prefix] at hspec
  change
    freshCoreGenerator s
        (fun i : Fin s ↦ stream i) ∈ target bits ∧
      freshCoreGenerator s
          (fun i : Fin s ↦ stream i) ∉
        closedNeighborhood prefixStarDistance
          (GenLimit.Generic.sample stream s : Set PrefixPoint) 1
  exact
    ⟨coreSet_subset_target bits hspec.1,
      fresh_core_not_near_target_sample
        hsampleTarget hspec.1 hspec.2⟩

theorem uniformlyGeneratable :
    UniformlyGeneratableAt prefixStarDistance
      (1 / 2 : ℝ) 1 prefixStarClass :=
  ⟨freshCoreGenerator, 1,
    freshCoreGenerator_isUniform⟩

private theorem prefix_injective
    (bits : ℕ → Bool) :
    Function.Injective (bitPrefix bits) := by
  intro n m h
  have := congrArg List.length h
  simpa using this

private theorem branch_prefix_injective
    (bits : ℕ → Bool) :
    Function.Injective
      (fun n ↦ branch (bitPrefix bits n)) :=
  by
    intro n m h
    apply prefix_injective bits
    exact branch.inj h

private theorem distinct_branch_distance_ge_three
    {x : PrefixPoint} {word : List Bool}
    (hne : x ≠ branch word) :
    3 ≤ prefixStarDistance x (branch word) := by
  cases x with
  | hub =>
      rw [prefixStarDistance, if_neg hne]
      norm_num [weight]
  | core n =>
      rw [prefixStarDistance, if_neg hne]
      norm_num [weight]
  | branch other =>
      rw [prefixStarDistance, if_neg hne]
      norm_num [weight]

private theorem target_not_hasFiniteCover_one
    (bits : ℕ → Bool) :
    ¬ HasFiniteCover prefixStarDistance 1
      (target bits) := by
  rintro ⟨centers, hcover⟩
  have hrange :
      (Set.range
        (fun n ↦ branch (bitPrefix bits n))).Infinite :=
    Set.infinite_range_of_injective
      (branch_prefix_injective bits)
  obtain ⟨x, ⟨n, rfl⟩, hxCenters⟩ :=
    hrange.exists_notMem_finset centers
  have hxTarget :
      branch (bitPrefix bits n) ∈ target bits :=
    (branch_mem_target_iff bits _).2 ⟨n, rfl⟩
  obtain ⟨y, hyCenters, hydist⟩ :=
    hcover hxTarget 2 (by norm_num)
  have hyNe : y ≠ branch (bitPrefix bits n) := by
    intro hy
    subst y
    exact hxCenters hyCenters
  have hge :=
    distinct_branch_distance_ge_three hyNe
  linarith

/-- Every target has infinite radius-one covering number. -/
theorem uniformlyUnboundedSupport :
    UniformlyUnboundedSupportAt
      prefixStarDistance 1 prefixStarClass := by
  intro L hL
  obtain ⟨bits, rfl⟩ := hL
  exact target_not_hasFiniteCover_one bits

private def corePrefix (d : ℕ) : Finset PrefixPoint :=
  (Finset.range d).image core

@[simp] private theorem corePrefix_card (d : ℕ) :
    (corePrefix d).card = d := by
  calc
    (corePrefix d).card =
        (Finset.range d).card := by
      exact Finset.card_image_of_injective
        (Finset.range d) core_injective
    _ = d := Finset.card_range d

private theorem corePrefix_subset_target
    (bits : ℕ → Bool) (d : ℕ) :
    (corePrefix d : Set PrefixPoint) ⊆ target bits := by
  intro x hx
  obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hx
  exact core_mem_target bits n

private theorem core_mem_closedNeighborhood_half_iff
    (A : Set PrefixPoint) (n : ℕ) :
    core n ∈ closedNeighborhood
      prefixStarDistance A (1 / 2 : ℝ) ↔
        core n ∈ A := by
  constructor
  · intro hnear
    obtain ⟨x, hxA, hdist⟩ :=
      hnear (3 / 4 : ℝ) (by norm_num)
    have hx : x = core n := by
      cases x with
      | hub =>
          rw [prefixStarDistance,
            if_neg (by simp)] at hdist
          norm_num [weight] at hdist
      | core m =>
          by_cases hmn : m = n
          · subst m
            rfl
          · norm_num
              [prefixStarDistance, weight, hmn] at hdist
      | branch word =>
          rw [prefixStarDistance,
            if_neg (by simp)] at hdist
          norm_num [weight] at hdist
    rwa [hx] at hxA
  · intro hxA η hη
    exact
      ⟨core n, hxA,
        by
          rw [prefixStarDistance_self]
          linarith⟩

private theorem corePrefix_coveringNumberEq (d : ℕ) :
    CoveringNumberEq prefixStarDistance
      (1 / 2 : ℝ) (corePrefix d : Set PrefixPoint) d := by
  constructor
  · intro centers hcover
    have hsubset : corePrefix d ⊆ centers := by
      intro x hx
      obtain ⟨n, _hn, rfl⟩ :=
        Finset.mem_image.mp hx
      exact
        (core_mem_closedNeighborhood_half_iff
          (centers : Set PrefixPoint) n).mp
          (hcover hx)
    simpa using Finset.card_le_card hsubset
  · refine
      ⟨corePrefix d, corePrefix_card d, ?_⟩
    intro x hx
    obtain ⟨n, _hn, rfl⟩ :=
      Finset.mem_image.mp hx
    exact
      (core_mem_closedNeighborhood_half_iff
        (corePrefix d : Set PrefixPoint) n).2 hx

private theorem exists_bit_ne
    {bits other : ℕ → Bool} (hne : bits ≠ other) :
    ∃ k, bits k ≠ other k := by
  by_contra h
  push_neg at h
  exact hne (funext h)

private theorem common_target_hasFiniteCover_one
    {bits other : ℕ → Bool} (hne : bits ≠ other) :
    HasFiniteCover prefixStarDistance 1
      (target bits ∩ target other) := by
  obtain ⟨k, hk⟩ := exists_bit_ne hne
  let branchCenters : Finset PrefixPoint :=
    (Finset.range (k + 1)).image
      (fun n ↦ branch (bitPrefix bits n))
  let centers : Finset PrefixPoint :=
    insert hub branchCenters
  refine ⟨centers, ?_⟩
  intro x hx
  rcases hx with ⟨hxBits, hxOther⟩
  cases x with
  | hub => exact (hub_not_mem_target bits hxBits).elim
  | core n =>
      intro η hη
      refine ⟨hub, by simp [centers], ?_⟩
      simpa [prefixStarDistance, weight] using hη
  | branch word =>
      obtain ⟨n, hn⟩ :=
        (branch_mem_target_iff bits word).1 hxBits
      obtain ⟨m, hm⟩ :=
        (branch_mem_target_iff other word).1 hxOther
      have hnm : n = m := by
        have hlen :=
          congrArg List.length (hn.symm.trans hm)
        simpa using hlen
      subst m
      have hnk : n ≤ k := by
        by_contra hnot
        have hkn : k < n := Nat.lt_of_not_ge hnot
        have heq :
            bitPrefix bits n = bitPrefix other n :=
          hn.symm.trans hm
        exact hk
          (prefix_eq_forces_bit_eq hkn heq)
      have hxCenter :
          branch word ∈ centers := by
        simp only [centers, branchCenters,
          Finset.mem_insert, Finset.mem_image,
          Finset.mem_range]
        right
        exact
          ⟨n, Nat.lt_succ_iff.mpr hnk,
            by rw [← hn]⟩
      intro η hη
      exact
        ⟨branch word, hxCenter,
          by
            rw [prefixStarDistance_self]
            linarith⟩

private theorem pair_corePrefix_scaleClosureWitness
    {K : GenLimit.Generic.LanguageClass PrefixPoint}
    {bits other : ℕ → Bool}
    (hbits : target bits ∈ K)
    (hother : target other ∈ K)
    (hne : bits ≠ other)
    (d : ℕ) :
    IsScaleClosureWitness prefixStarDistance
      (1 / 2 : ℝ) 1 K (corePrefix d) d := by
  refine ⟨?_, corePrefix_coveringNumberEq d, ?_⟩
  · exact
      ⟨target bits,
        hbits, corePrefix_subset_target bits d⟩
  · obtain ⟨centers, hcenters⟩ :=
      common_target_hasFiniteCover_one hne
    refine ⟨centers, ?_⟩
    intro x hxCore
    apply hcenters
    constructor
    · exact
        hxCore (target bits)
          ⟨hbits, corePrefix_subset_target bits d⟩
    · exact
        hxCore (target other)
          ⟨hother, corePrefix_subset_target other d⟩

/-- Any subclass of the example class having finite scale-closure dimension
contains at most one target. -/
theorem finite_scaleClosureDimension_subsingleton
    {K : GenLimit.Generic.LanguageClass PrefixPoint}
    (hK : K ⊆ prefixStarClass)
    (hfinite :
      HasFiniteScaleClosureDimension prefixStarDistance
        (1 / 2 : ℝ) 1 K) :
    K.Subsingleton := by
  intro L hLK M hMK
  obtain ⟨bits, rfl⟩ := hK hLK
  obtain ⟨other, rfl⟩ := hK hMK
  by_contra htargets
  have hne : bits ≠ other := by
    intro h
    subst other
    exact htargets rfl
  obtain ⟨D, hD⟩ := hfinite
  exact
    hD (D + 1) (Nat.lt_succ_self D)
      ⟨corePrefix (D + 1),
        pair_corePrefix_scaleClosureWitness
          hLK hMK hne (D + 1)⟩

private theorem uncountable_bool_streams :
    Uncountable (ℕ → Bool) := by
  rw [uncountable_iff_not_countable]
  intro hCountable
  letI : Countable (ℕ → Bool) := hCountable
  obtain ⟨enumerate, henumerate⟩ :=
    countable_iff_exists_surjective.mp hCountable
  let diagonal : ℕ → Bool :=
    fun n ↦ !(enumerate n n)
  obtain ⟨n, hn⟩ := henumerate diagonal
  have hpoint := congrFun hn n
  simp [diagonal] at hpoint

local instance : Uncountable (ℕ → Bool) :=
  uncountable_bool_streams

/-- The target class itself is uncountable. -/
theorem prefixStarClass_uncountable :
    ¬ prefixStarClass.Countable := by
  intro hcount
  have hpreimage :=
    hcount.preimage target_injective
  have huniv :
      target ⁻¹' prefixStarClass =
        (Set.univ : Set (ℕ → Bool)) := by
    ext bits
    simp [prefixStarClass]
  have :
      (Set.univ : Set (ℕ → Bool)).Countable := by
    rwa [huniv] at hpreimage
  exact Set.not_countable_univ this

/-- No countable nondecreasing cover of the class can have finite
scale-closure dimension at every stage. -/
theorem no_finite_scaleClosure_nondecreasing_cover :
    ¬ ∃ classes :
        ℕ → GenLimit.Generic.LanguageClass PrefixPoint,
      IsNondecreasingMetricCover prefixStarClass classes ∧
      ∀ n,
        HasFiniteScaleClosureDimension
          prefixStarDistance (1 / 2 : ℝ) 1
          (classes n) := by
  rintro ⟨classes, hcover, hfinite⟩
  have hsubset :
      ∀ n, classes n ⊆ prefixStarClass := by
    intro n L hLn
    rw [hcover.2]
    exact Set.mem_iUnion.mpr ⟨n, hLn⟩
  have hcountClasses :
      ∀ n, (classes n).Countable := by
    intro n
    exact
      (finite_scaleClosureDimension_subsingleton
        (hsubset n) (hfinite n)).countable
  have hcountUnion :
      (⋃ n, classes n).Countable :=
    Set.countable_iUnion hcountClasses
  apply prefixStarClass_uncountable
  rwa [hcover.2]

/-- The printed `(i) → (ii)` direction of Theorem 3.3 is false under
ambient-center covers, even on a countable (therefore separable) genuine
metric space. -/
theorem theorem_3_3_necessity_counterexample :
    UniformlyUnboundedSupportAt
        prefixStarDistance 1 prefixStarClass ∧
      NonuniformlyGeneratableAt
        prefixStarDistance (1 / 2 : ℝ) 1
          prefixStarClass ∧
      ¬ ∃ classes :
          ℕ → GenLimit.Generic.LanguageClass PrefixPoint,
        IsNondecreasingMetricCover prefixStarClass classes ∧
        ∀ n,
          HasFiniteScaleClosureDimension
            prefixStarDistance (1 / 2 : ℝ) 1
            (classes n) := by
  refine
    ⟨uniformlyUnboundedSupport, ?_,
      no_finite_scaleClosure_nondecreasing_cover⟩
  obtain ⟨gen, d, hgen⟩ := uniformlyGeneratable
  exact ⟨gen, fun L hL ↦ ⟨d, hgen L hL⟩⟩

end GenLimit.MetricSpaces.Theorem33Counterexample
