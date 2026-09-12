import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import GenLimit.Paper21_GenerationInMetricSpaces.Common.WeightedStarMetric
import Mathlib.Topology.MetricSpace.Basic

/-!
# Source diagnostic for metric uniform-generation necessity

This module audits `lem:closnecc`, the necessity direction of Theorem 3.1
in Li--Raman--Tewari, *On Generation in Metric Spaces*,
arXiv:2602.07710v1.

The source defines a cover using centers from the ambient metric space.
Its necessity proof then appends those centers to a positive target stream,
which requires the stronger fact that the centers lie in the common core.
The first section isolates that missing same-radius internalization premise
and proves the corrected necessity implication.

The second section shows that the premise is essential.  A genuine weighted
star metric has infinitely many common-core leaves covered at radius one by
the ambient hub, although no finite same-radius internal cover exists.  Two
targets share the core and have separate unbounded tails.  An explicit
generator uniformly chooses fresh common-core leaves while the source's
scale-closure dimension is infinite.
-/

namespace GenLimit.MetricSpaces

/-! ## Corrected necessity under internal cover centers -/

/-- A finite cover whose centers themselves belong to the covered set.

This is stronger than the paper-facing `HasFiniteCover`, whose centers may
be arbitrary points of the ambient space. -/
def HasFiniteInternalCover
    (ρ : Distance α) (r : ℝ) (A : Set α) : Prop :=
  ∃ centers : Finset α,
    (centers : Set α) ⊆ A ∧
      A ⊆ closedNeighborhood ρ (centers : Set α) r

/-- The exact missing premise in the printed necessity proof, restricted to
the witnesses where it is used: every scale-closure witness has a
same-novelty-radius finite cover whose centers lie in its common core. -/
def ScaleClosureWitnessCoverInternalizationAt
    (ρ : Distance α) (ε ε' : ℝ)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ (S : Finset α) (d : ℕ),
    IsScaleClosureWitness ρ ε ε' H S d →
      HasFiniteInternalCover ρ ε' (commonCore H S)

private theorem coveringNumberAtLeast_of_eq_of_le
    {ρ : Distance α} {ε : ℝ} {A : Set α}
    {k d : ℕ} (hkd : k ≤ d)
    (hEq : CoveringNumberEq ρ ε A d) :
    CoveringNumberAtLeast ρ ε A k := by
  intro centers hcover
  exact hkd.trans (hEq.1 centers hcover)

private theorem positive_coveringNumber_forces_nonempty
    {ρ : Distance α} {ε : ℝ}
    {S : Finset α} {d : ℕ}
    (hd : 0 < d)
    (hEq :
      CoveringNumberEq ρ ε (S : Set α) d) :
    S.Nonempty := by
  classical
  by_contra hS
  have hSEmpty : S = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hS
  subst S
  have hd0 : d ≤ 0 :=
    hEq.1 ∅ (by
      intro x hx
      simp at hx)
  omega

/-- A large scale-closure witness with an internal same-radius cover defeats
the proposed generator at its proposed uniform threshold.

This is the sound mathematical core of source lemma `lem:closnecc`. -/
theorem internal_scaleClosureWitness_defeats_uniform_threshold
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    {gen : GenLimit.Generic.Generator α}
    {k d : ℕ} (hkd : k < d)
    {S : Finset α}
    (hversion : (versionSpace H S).Nonempty)
    (hEq :
      CoveringNumberEq ρ ε (S : Set α) d)
    (hinternal :
      HasFiniteInternalCover ρ ε' (commonCore H S)) :
    ¬ IsUniformGeneratorAt ρ ε ε' gen H k := by
  classical
  rintro hgen
  obtain ⟨centers, hcentersCore, hcoverCore⟩ :=
    hinternal
  let history : List α := S.toList ++ centers.toList
  have hhistoryFinset :
      history.toFinset = S ∪ centers := by
    simp [history]
  let xhat : α := gen history.length history.get
  obtain ⟨L, hLVersion, hbad⟩ :
      ∃ L, L ∈ versionSpace H S ∧
        (xhat ∈ commonCore H S ∨ xhat ∉ L) := by
    by_cases hx : xhat ∈ commonCore H S
    · obtain ⟨L, hL⟩ := hversion
      exact ⟨L, hL, Or.inl hx⟩
    · change
        ¬ ∀ K, K ∈ versionSpace H S → xhat ∈ K at hx
      push_neg at hx
      obtain ⟨L, hL, hxL⟩ := hx
      exact ⟨L, hL, Or.inr hxL⟩
  have hdPositive : 0 < d :=
    lt_of_le_of_lt (Nat.zero_le k) hkd
  have hSNonempty : S.Nonempty :=
    positive_coveringNumber_forces_nonempty hdPositive hEq
  let fallback : α := Classical.choose hSNonempty
  have hfallbackS : fallback ∈ S :=
    Classical.choose_spec hSNonempty
  have hfallbackL : fallback ∈ L :=
    hLVersion.2 hfallbackS
  let stream : GenLimit.Generic.Stream α :=
    GenLimit.Generic.historyThenFallback history fallback
  have hhistoryL :
      (history.toFinset : Set α) ⊆ L := by
    rw [hhistoryFinset]
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxCenters
    · exact hLVersion.2 hxS
    · exact
        (show x ∈ commonCore H S from
          hcentersCore hxCenters) L hLVersion
  have hstream :
      GenLimit.Generic.StreamIn stream L := by
    rintro x ⟨n, rfl⟩
    by_cases hn : n < history.length
    · apply hhistoryL
      change stream n ∈ history.toFinset
      rw [List.mem_toFinset, List.mem_iff_get]
      exact ⟨⟨n, hn⟩,
        by
          simp [stream,
            GenLimit.Generic.historyThenFallback, hn]⟩
    · simpa [stream,
        GenLimit.Generic.historyThenFallback, hn]
        using hfallbackL
  have hfirstSample :
      GenLimit.Generic.sample stream S.card = S := by
    calc
      GenLimit.Generic.sample stream S.card =
          GenLimit.Generic.sample
            (GenLimit.Generic.historyThenFallback
              S.toList fallback) S.card := by
        apply GenLimit.Generic.sample_eq_of_eq_on_prefix
        intro n hn
        have hnS : n < S.toList.length := by
          simpa using hn
        have hnHistory : n < history.length := by
          simp only [history, List.length_append,
            Finset.length_toList]
          omega
        change
          GenLimit.Generic.historyThenFallback
              history fallback n =
            GenLimit.Generic.historyThenFallback
              S.toList fallback n
        simp only [GenLimit.Generic.historyThenFallback,
          dif_pos hnHistory, dif_pos hnS, history]
        exact List.getElem_append_left hnS
      _ = GenLimit.Generic.sample
          (GenLimit.Generic.historyThenFallback
            S.toList fallback) S.toList.length := by
        rw [Finset.length_toList]
      _ = S.toList.toFinset :=
        GenLimit.Generic.sample_historyThenFallback_length
          S.toList fallback
      _ = S := Finset.toList_toFinset S
  have hfullSample :
      GenLimit.Generic.sample stream history.length =
        S ∪ centers := by
    change
      GenLimit.Generic.sample
          (GenLimit.Generic.historyThenFallback
            history fallback) history.length =
        S ∪ centers
    rw [GenLimit.Generic.sample_historyThenFallback_length,
      hhistoryFinset]
  have htrigger :
      CoveringNumberAtLeast ρ ε
        (GenLimit.Generic.sample stream S.card :
          Set α) k := by
    rw [hfirstSample]
    exact coveringNumberAtLeast_of_eq_of_le
      (Nat.le_of_lt hkd) hEq
  have htime : S.card ≤ history.length := by
    simp [history]
  have hcorrect :=
    hgen L hLVersion.1 stream hstream
      S.card htrigger history.length htime
  have houtput :
      GenLimit.Generic.output gen stream history.length =
        xhat := by
    unfold GenLimit.Generic.output
    simp only [stream, xhat]
    congr 1
    funext i
    simp [GenLimit.Generic.historyThenFallback, i.isLt]
  rcases hbad with hxCore | hxL
  · apply hcorrect.2
    rw [houtput, hfullSample]
    apply inClosedNeighborhood_mono_centers
        (show (centers : Set α) ⊆
          (S ∪ centers : Finset α) from by
            intro x hx
            exact Finset.mem_union_right S hx)
    exact hcoverCore hxCore
  · apply hxL
    simpa only [houtput] using hcorrect.1

/-- Corrected necessity direction for Theorem 3.1, with the missing
same-radius internal-center premise explicit. -/
theorem uniform_implies_finite_scaleClosureDimension_of_internalization
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hInternal :
      ScaleClosureWitnessCoverInternalizationAt
        ρ ε ε' H)
    (hUniform :
      UniformlyGeneratableAt ρ ε ε' H) :
    HasFiniteScaleClosureDimension ρ ε ε' H := by
  obtain ⟨gen, k, hgen⟩ := hUniform
  refine ⟨k, ?_⟩
  intro d hkd
  rintro ⟨S, hS⟩
  exact
    (internal_scaleClosureWitness_defeats_uniform_threshold
      (gen := gen) hkd hS.1 hS.2.1
        (hInternal S d hS)) hgen

/-! ## Genuine metric counterexample to unqualified necessity -/

namespace NecessityCounterexample

/-- Points of the weighted star: one ambient hub, a shared countable core,
and two disjoint countable target tails. -/
inductive StarPoint where
  | hub
  | core (n : ℕ)
  | tail (side : Bool) (n : ℕ)
  deriving DecidableEq

open StarPoint

private def weight : StarPoint → ℝ
  | hub => 0
  | core _ => 1
  | tail _ _ => 3

/-- The weighted-star distance: distinct points have distance equal to the
sum of their edge weights to the hub. -/
def starDistance (x y : StarPoint) : ℝ :=
  if x = y then 0 else weight x + weight y

private theorem weight_nonneg (x : StarPoint) :
    0 ≤ weight x := by
  cases x <;> norm_num [weight]

private theorem weight_pos_of_ne_hub
    {x : StarPoint} (hx : x ≠ hub) :
    0 < weight x := by
  cases x <;> simp_all [weight]

@[simp] private theorem starDistance_self (x : StarPoint) :
    starDistance x x = 0 :=
  WeightedStar.distance_self weight x

private theorem starDistance_comm (x y : StarPoint) :
    starDistance x y = starDistance y x :=
  WeightedStar.distance_comm weight x y

private theorem starDistance_triangle (x y z : StarPoint) :
    starDistance x z ≤
      starDistance x y + starDistance y z :=
  WeightedStar.distance_triangle weight weight_nonneg x y z

private theorem weight_pair_pos
    {x y : StarPoint} (hxy : x ≠ y) :
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

/-- The counterexample kernel is a genuine metric, not merely an arbitrary
distance function accepted by the paper-facing semantic layer. -/
instance instMetricSpaceStarPoint : MetricSpace StarPoint where
  dist := starDistance
  dist_self := starDistance_self
  dist_comm := starDistance_comm
  dist_triangle := starDistance_triangle
  eq_of_dist_eq_zero :=
    WeightedStar.eq_of_distance_eq_zero weight weight_pair_pos

/-- The infinitely many weight-one leaves shared by both targets. -/
def coreSet : Set StarPoint
  | core _ => True
  | _ => False

/-- A target contains the common core and one of the two weight-three
tails, but not the hub. -/
def target (side : Bool) : Set StarPoint
  | core _ => True
  | tail side' _ => side' = side
  | hub => False

/-- The two-target counterexample class. -/
def starClass : GenLimit.Generic.LanguageClass StarPoint :=
  {target false, target true}

private def corePrefix (d : ℕ) : Finset StarPoint :=
  (Finset.range d).image core

@[simp] private theorem mem_coreSet_core (n : ℕ) :
    core n ∈ coreSet := by
  trivial

@[simp] private theorem hub_not_mem_coreSet :
    hub ∉ coreSet := by
  intro h
  exact h

@[simp] private theorem tail_not_mem_coreSet
    (side : Bool) (n : ℕ) :
    tail side n ∉ coreSet := by
  intro h
  exact h

@[simp] private theorem mem_target_core
    (side : Bool) (n : ℕ) :
    core n ∈ target side := by
  trivial

@[simp] private theorem hub_not_mem_target (side : Bool) :
    hub ∉ target side := by
  intro h
  exact h

@[simp] private theorem mem_target_tail_iff
    (side side' : Bool) (n : ℕ) :
    tail side' n ∈ target side ↔ side' = side := by
  rfl

private theorem core_injective :
    Function.Injective core := by
  intro n m h
  cases h
  rfl

@[simp] private theorem corePrefix_card (d : ℕ) :
    (corePrefix d).card = d := by
  calc
    (corePrefix d).card =
        (Finset.range d).card := by
      exact Finset.card_image_of_injective
        (Finset.range d) core_injective
    _ = d := Finset.card_range d

private theorem corePrefix_subset_target
    (side : Bool) (d : ℕ) :
    (corePrefix d : Set StarPoint) ⊆ target side := by
  intro x hx
  obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hx
  simp

private theorem target_mem_versionSpace_corePrefix
    (side : Bool) (d : ℕ) :
    target side ∈ versionSpace starClass (corePrefix d) := by
  constructor
  · cases side <;> simp [starClass]
  · exact corePrefix_subset_target side d

private theorem commonCore_corePrefix (d : ℕ) :
    commonCore starClass (corePrefix d) = coreSet := by
  ext x
  constructor
  · intro hx
    cases x with
    | hub =>
        exact (hub_not_mem_target false
          (hx (target false)
            (target_mem_versionSpace_corePrefix false d))).elim
    | core n =>
        exact mem_coreSet_core n
    | tail side n =>
        cases side with
        | false =>
            have hbad :=
              hx (target true)
                (target_mem_versionSpace_corePrefix true d)
            exact (by
              have : (false : Bool) = true :=
                (mem_target_tail_iff true false n).mp hbad
              contradiction)
        | true =>
            have hbad :=
              hx (target false)
                (target_mem_versionSpace_corePrefix false d)
            exact (by
              have : (true : Bool) = false :=
                (mem_target_tail_iff false true n).mp hbad
              contradiction)
  · intro hx L hL
    cases x with
    | hub => exact (hub_not_mem_coreSet hx).elim
    | core n =>
        rcases hL.1 with hL | hL
        · subst L
          exact mem_target_core false n
        · subst L
          exact mem_target_core true n
    | tail side n =>
        exact (tail_not_mem_coreSet side n hx).elim

private theorem core_mem_closedNeighborhood_half_iff
    (A : Set StarPoint) (n : ℕ) :
    core n ∈ closedNeighborhood starDistance A (1 / 2 : ℝ) ↔
      core n ∈ A := by
  constructor
  · intro hnear
    obtain ⟨x, hxA, hdist⟩ :=
      hnear (3 / 4 : ℝ) (by norm_num)
    have hx : x = core n := by
      cases x with
      | hub =>
          rw [starDistance, if_neg (by simp)] at hdist
          norm_num [weight] at hdist
      | core m =>
          by_cases hmn : m = n
          · subst m
            rfl
          · norm_num [starDistance, weight, hmn] at hdist
      | tail side m =>
          rw [starDistance, if_neg (by simp)] at hdist
          norm_num [weight] at hdist
    rwa [hx] at hxA
  · intro hxA η hη
    exact ⟨core n, hxA,
      by simp only [starDistance_self]; linarith⟩

private theorem corePrefix_coveringNumberEq (d : ℕ) :
    CoveringNumberEq starDistance (1 / 2 : ℝ)
      (corePrefix d : Set StarPoint) d := by
  constructor
  · intro centers hcover
    have hsubset : corePrefix d ⊆ centers := by
      intro x hx
      obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hx
      exact
        (core_mem_closedNeighborhood_half_iff
          (centers : Set StarPoint) n).mp (hcover hx)
    simpa using Finset.card_le_card hsubset
  · refine ⟨corePrefix d, corePrefix_card d, ?_⟩
    intro x hx
    obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hx
    exact
      (core_mem_closedNeighborhood_half_iff
        (corePrefix d : Set StarPoint) n).2
        (by exact hx)

private theorem coreSet_hasFiniteCover_one :
    HasFiniteCover starDistance 1 coreSet := by
  refine ⟨{hub}, ?_⟩
  intro x hx η hη
  cases x with
  | hub => exact (hub_not_mem_coreSet hx).elim
  | core n =>
      refine ⟨hub, by simp, ?_⟩
      simpa [starDistance, weight] using hη
  | tail side n =>
      exact (tail_not_mem_coreSet side n hx).elim

private theorem corePrefix_scaleClosureWitness (d : ℕ) :
    IsScaleClosureWitness starDistance (1 / 2 : ℝ) 1
      starClass (corePrefix d) d := by
  refine ⟨?_, corePrefix_coveringNumberEq d, ?_⟩
  · exact
      ⟨target false,
        target_mem_versionSpace_corePrefix false d⟩
  · rw [commonCore_corePrefix]
    exact coreSet_hasFiniteCover_one

/-- The class has arbitrarily large `(1/2, 1)` scale-closure witnesses. -/
theorem infinite_scaleClosureDimension :
    ¬ HasFiniteScaleClosureDimension
      starDistance (1 / 2 : ℝ) 1 starClass := by
  rintro ⟨D, hD⟩
  exact hD (D + 1) (Nat.lt_succ_self D)
    ⟨corePrefix (D + 1),
      corePrefix_scaleClosureWitness (D + 1)⟩

private theorem coreSet_infinite : coreSet.Infinite := by
  have hrange :
      (Set.range core).Infinite :=
    Set.infinite_range_of_injective core_injective
  apply hrange.mono
  rintro x ⟨n, rfl⟩
  simp

/-- Choose a common-core leaf not present in the finite input history. -/
noncomputable def freshCoreGenerator :
    GenLimit.Generic.Generator StarPoint :=
  fun _ xs =>
    Classical.choose
      (coreSet_infinite.exists_notMem_finset
        (GenLimit.Generic.sequenceSample xs))

/-- The chosen output belongs to the core and is absent from the history. -/
theorem freshCoreGenerator_spec
    {t : ℕ} (xs : Fin t → StarPoint) :
    freshCoreGenerator t xs ∈ coreSet ∧
      freshCoreGenerator t xs ∉
        GenLimit.Generic.sequenceSample xs := by
  exact
    Classical.choose_spec
      (coreSet_infinite.exists_notMem_finset
        (GenLimit.Generic.sequenceSample xs))

private theorem coreSet_subset_of_mem_starClass
    {L : GenLimit.Generic.Language StarPoint}
    (hL : L ∈ starClass) :
    coreSet ⊆ L := by
  intro x hx
  rcases hL with hL | hL
  · subst L
    cases x with
    | hub => exact (hub_not_mem_coreSet hx).elim
    | core n => exact mem_target_core false n
    | tail side n =>
        exact (tail_not_mem_coreSet side n hx).elim
  · subst L
    cases x with
    | hub => exact (hub_not_mem_coreSet hx).elim
    | core n => exact mem_target_core true n
    | tail side n =>
        exact (tail_not_mem_coreSet side n hx).elim

private theorem target_distinct_core_distance_ge_two
    {side : Bool} {x : StarPoint} {n : ℕ}
    (hx : x ∈ target side) (hne : x ≠ core n) :
    2 ≤ starDistance x (core n) := by
  cases x with
  | hub => exact (hub_not_mem_target side hx).elim
  | core m =>
      have hmn : m ≠ n := by
        intro h
        subst m
        exact hne rfl
      norm_num [starDistance, weight, hmn]
  | tail side' m =>
      rw [starDistance, if_neg (by simp)]
      norm_num [weight]

private theorem fresh_core_not_in_target_sample_neighborhood
    {side : Bool} {S : Finset StarPoint}
    (hS : (S : Set StarPoint) ⊆ target side)
    {x : StarPoint} (hxCore : x ∈ coreSet)
    (hxFresh : x ∉ S) :
    x ∉ closedNeighborhood starDistance
      (S : Set StarPoint) 1 := by
  intro hnear
  cases x with
  | hub => exact (hub_not_mem_coreSet hxCore).elim
  | core n =>
      obtain ⟨y, hyS, hydist⟩ :=
        hnear (3 / 2 : ℝ) (by norm_num)
      have hyTarget : y ∈ target side := hS hyS
      have hyNe : y ≠ core n := by
        intro hy
        subst y
        exact hxFresh hyS
      have hge :=
        target_distinct_core_distance_ge_two
          hyTarget hyNe
      linarith
  | tail side n =>
      exact (tail_not_mem_coreSet side n hxCore).elim

/-- The fresh-core generator is uniformly correct at threshold one. -/
theorem freshCoreGenerator_isUniform :
    IsUniformGeneratorAt starDistance (1 / 2 : ℝ) 1
      freshCoreGenerator starClass 1 := by
  intro L hL stream hstream _t _htrigger s _hts
  have hsampleTarget :
      (GenLimit.Generic.sample stream s : Set StarPoint) ⊆ L := by
    intro x hx
    obtain ⟨i, _his, rfl⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hx
    exact hstream ⟨i, rfl⟩
  have hspec :=
    freshCoreGenerator_spec
      (fun i : Fin s => stream i)
  rw [GenLimit.Generic.sequenceSample_prefix] at hspec
  change
    freshCoreGenerator s (fun i : Fin s => stream i) ∈ L ∧
      freshCoreGenerator s (fun i : Fin s => stream i) ∉
        closedNeighborhood starDistance
          (GenLimit.Generic.sample stream s : Set StarPoint) 1
  refine ⟨coreSet_subset_of_mem_starClass hL hspec.1, ?_⟩
  rcases hL with hL | hL
  · subst L
    exact fresh_core_not_in_target_sample_neighborhood
      hsampleTarget hspec.1 hspec.2
  · subst L
    exact fresh_core_not_in_target_sample_neighborhood
      hsampleTarget hspec.1 hspec.2

/-- The counterexample class is `(1/2, 1)`-uniformly generatable. -/
theorem uniformlyGeneratable :
    UniformlyGeneratableAt starDistance (1 / 2 : ℝ) 1
      starClass :=
  ⟨freshCoreGenerator, 1, freshCoreGenerator_isUniform⟩

private theorem tail_injective (side : Bool) :
    Function.Injective (tail side) := by
  intro n m h
  cases h
  rfl

private theorem distinct_tail_distance_ge_three
    {side : Bool} {x : StarPoint} {n : ℕ}
    (hne : x ≠ tail side n) :
    3 ≤ starDistance x (tail side n) := by
  cases x with
  | hub =>
      rw [starDistance, if_neg (by simp)]
      norm_num [weight]
  | core m =>
      rw [starDistance, if_neg (by simp)]
      norm_num [weight]
  | tail side' m =>
      norm_num [starDistance, weight, hne]

private theorem target_not_hasFiniteCover_one (side : Bool) :
    ¬ HasFiniteCover starDistance 1 (target side) := by
  rintro ⟨centers, hcover⟩
  have hrange :
      (Set.range (tail side)).Infinite :=
    Set.infinite_range_of_injective (tail_injective side)
  obtain ⟨x, ⟨n, rfl⟩, hxCenters⟩ :=
    hrange.exists_notMem_finset centers
  have hxTarget : tail side n ∈ target side := by
    simp
  have hnear := hcover hxTarget
  obtain ⟨y, hyCenters, hydist⟩ :=
    hnear 2 (by norm_num)
  have hyNe : y ≠ tail side n := by
    intro hy
    subst y
    exact hxCenters hyCenters
  have hge := distinct_tail_distance_ge_three hyNe
  linarith

/-- Both targets have infinite radius-one covering number because of their
weight-three tails. -/
theorem uniformlyUnboundedSupport :
    UniformlyUnboundedSupportAt starDistance 1 starClass := by
  intro L hL
  rcases hL with hL | hL
  · subst L
    exact target_not_hasFiniteCover_one false
  · subst L
    exact target_not_hasFiniteCover_one true

/-- The unqualified necessity implication in source Theorem 3.1 is false
under its literal ambient-center covering convention, even for a genuine
metric, a finite class, positive scales bounded by the UUS radius, and an
explicit uniformly correct generator. -/
theorem theorem_3_1_necessity_counterexample :
    UniformlyUnboundedSupportAt starDistance 1 starClass ∧
      UniformlyGeneratableAt starDistance (1 / 2 : ℝ) 1
        starClass ∧
      ¬ HasFiniteScaleClosureDimension
        starDistance (1 / 2 : ℝ) 1 starClass :=
  ⟨uniformlyUnboundedSupport, uniformlyGeneratable,
    infinite_scaleClosureDimension⟩

end NecessityCounterexample

end GenLimit.MetricSpaces
