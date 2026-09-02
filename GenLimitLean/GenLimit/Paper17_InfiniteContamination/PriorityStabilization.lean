import GenLimit.Paper17_InfiniteContamination.VanishingNoise
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic

/-!
# Prefix-priority stabilization

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Lemma 4.1 and Corollary 4.2.

Algorithm 1 assigns every language an integer priority which is monotone in
time and is bounded below by its index.  At any fixed finite cutoff `p`,
only the first `p + 1` zero-indexed languages can ever have priority at most
`p`.  Each of those finitely many priority traces either remains bounded by
`p` and eventually stabilizes, or crosses above `p` and stays there.
Taking a maximum of the finitely many thresholds gives the source's uniform
prefix-stabilization time.

The source phrases the stable class using a limit in `ℕ ∪ {∞}`.  At a fixed
finite cutoff, `boundedPriorityIndices` is the equivalent discrete
normalization: a monotone natural-valued trace has limit at most `p` exactly
when all of its values are at most `p`.

The final lemmas check Corollary 4.2's finite-step output argument.  If a
selected prefix contains the stable class and has infinite intersection,
there is a fresh point in that intersection; when the target belongs to the
stable class, the point lies in the target.  The containment is deliberately
the corrected one: the selected intersection is a subset of the target.
-/

namespace GenLimit.InfiniteContamination

open Filter

/-! ## Algorithm 4's threshold priority -/

/-- Algorithm 4's `Nᵢ⁽ⁿ⁾`: the maximum of `1` and one plus the latest
prefix at which the empirical noise rate violates the threshold.

For the source's positive thresholds, the zero-length prefix is never a
violation.  Hence this is exactly its displayed recurrence: the value is
`1` when every nonempty prefix through `n` meets the threshold, and it is
`m + 1` when `m` is the latest violating prefix (in particular, `n + 1`
when the current prefix violates). -/
noncomputable def thresholdPenalty
    (rate : ℕ → ℝ) (threshold : ℝ) (n : ℕ) : ℕ := by
  classical
  exact max 1 (
    ((Finset.range (n + 1)).filter
      fun m => threshold < rate m).sup fun m => m + 1)

theorem thresholdPenalty_le_time_succ
    (rate : ℕ → ℝ) (threshold : ℝ) (n : ℕ) :
    thresholdPenalty rate threshold n ≤ n + 1 := by
  classical
  unfold thresholdPenalty
  apply max_le
  · omega
  · apply Finset.sup_le
    intro m hm
    have hmrange : m < n + 1 :=
      (Finset.mem_filter.mp hm).1 |> Finset.mem_range.mp
    omega

/-- If no prefix through `n` violates the threshold, Algorithm 4's counter
has its source-defined baseline value `1`. -/
theorem thresholdPenalty_eq_one_of_forall_le
    (rate : ℕ → ℝ) (threshold : ℝ) {n : ℕ}
    (hgood : ∀ m, m ≤ n → rate m ≤ threshold) :
    thresholdPenalty rate threshold n = 1 := by
  classical
  unfold thresholdPenalty
  have hempty :
      (Finset.range (n + 1)).filter
          (fun m => threshold < rate m) = ∅ := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
      iff_false, not_and]
    intro hm
    exact not_lt_of_ge (hgood m (Nat.le_of_lt_succ hm))
  rw [hempty]
  simp

/-- A current threshold violation sets the penalty to exactly `n+1`,
matching the second branch of Algorithm 4. -/
theorem thresholdPenalty_eq_time_succ_of_violation
    (rate : ℕ → ℝ) (threshold : ℝ) {n : ℕ}
    (hviolation : threshold < rate n) :
    thresholdPenalty rate threshold n = n + 1 := by
  apply le_antisymm
  · exact thresholdPenalty_le_time_succ rate threshold n
  · classical
    unfold thresholdPenalty
    exact (Finset.le_sup (f := fun m : ℕ => m + 1)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), hviolation⟩)).trans
          (Nat.le_max_right _ _)

/-- The threshold penalty is monotone in time, as required by the priority
template's Lemma 4.1. -/
theorem thresholdPenalty_mono
    (rate : ℕ → ℝ) (threshold : ℝ) :
    Monotone (thresholdPenalty rate threshold) := by
  intro m n hmn
  classical
  unfold thresholdPenalty
  apply max_le_max_left
  apply Finset.sup_mono
  intro k hk
  have hkparts := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hkparts.1)
        (Nat.add_le_add_right hmn 1)),
      hkparts.2⟩

/-- Once every later empirical rate meets the threshold, no new violation
can change Algorithm 4's penalty. -/
theorem thresholdPenalty_eq_of_eventually_le
    (rate : ℕ → ℝ) (threshold : ℝ) {T n : ℕ}
    (hT : ∀ m, T ≤ m → rate m ≤ threshold)
    (hTn : T ≤ n) :
    thresholdPenalty rate threshold n =
      thresholdPenalty rate threshold T := by
  classical
  have hsets :
      (Finset.range (n + 1)).filter
          (fun m => threshold < rate m) =
        (Finset.range (T + 1)).filter
          (fun m => threshold < rate m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hmn, hbad⟩
      have hmT : m < T := by
        by_contra hnot
        exact (not_lt_of_ge (hT m (Nat.le_of_not_gt hnot))) hbad
      exact ⟨hmT.trans (Nat.lt_succ_self T), hbad⟩
    · rintro ⟨hmT, hbad⟩
      exact
        ⟨hmT.trans_le
          (Nat.add_le_add_right hTn 1), hbad⟩
  unfold thresholdPenalty
  rw [hsets]

/-- A rate tending to zero makes every positive-threshold penalty eventually
constant.  This is the exact bounded-priority fact used for the target
language in Theorem 5.1. -/
theorem thresholdPenalty_eventually_constant_of_tendsto_zero
    (rate : ℕ → ℝ) {threshold : ℝ}
    (hthreshold : 0 < threshold)
    (hrate : Tendsto rate atTop (nhds 0)) :
    ∃ T, ∀ n, T ≤ n →
      thresholdPenalty rate threshold n =
        thresholdPenalty rate threshold T := by
  have heventually :
      ∀ᶠ n : ℕ in atTop, rate n ≤ threshold :=
    ((tendsto_order.1 hrate).2 threshold hthreshold).mono
      fun _ hn => hn.le
  obtain ⟨T, hT⟩ := eventually_atTop.mp heventually
  exact
    ⟨T, fun n hn =>
      thresholdPenalty_eq_of_eventually_le rate threshold hT hn⟩

/-- Algorithm 4's natural-valued priority.  With Lean index `i`
corresponding to source index `i + 1`, this is the source priority
`(i + 1) + Nᵢ⁽ⁿ⁾` minus the same constant `1` for every language, and
therefore induces exactly the source ordering. -/
noncomputable def thresholdPriorityTrace
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ)
    (i n : ℕ) : ℕ :=
  i + thresholdPenalty
    (empiricalNoiseRate stream (family i)) (threshold i) n

theorem thresholdPriorityTrace_mono
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (i : ℕ) :
    Monotone (thresholdPriorityTrace stream family threshold i) := by
  intro m n hmn
  exact Nat.add_le_add_left
    (thresholdPenalty_mono
      (empiricalNoiseRate stream (family i))
      (threshold i) hmn) i

theorem thresholdPriorityTrace_index_le
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (i n : ℕ) :
    i ≤ thresholdPriorityTrace stream family threshold i n := by
  unfold thresholdPriorityTrace
  omega

theorem thresholdPriorityTrace_eventually_constant_of_vanishingNoise
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (i : ℕ)
    (hthreshold : 0 < threshold i)
    (hnoise : VanishingNoise stream (family i)) :
    ∃ T, ∀ n, T ≤ n →
      thresholdPriorityTrace stream family threshold i n =
        thresholdPriorityTrace stream family threshold i T := by
  obtain ⟨T, hT⟩ :=
    thresholdPenalty_eventually_constant_of_tendsto_zero
      (empiricalNoiseRate stream (family i))
      hthreshold hnoise
  refine ⟨T, ?_⟩
  intro n hn
  unfold thresholdPriorityTrace
  rw [hT n hn]

/-- The zero-indexed languages whose monotone priority trace stays below a
fixed finite cutoff.  This is the finite-cutoff form of the source's
`𝓛(p) = {Lᵢ : Pᵢ^∞ ≤ p}`. -/
noncomputable def boundedPriorityIndices
    (priorityTrace : ℕ → ℕ → ℕ) (p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (p + 1)).filter fun i =>
    ∀ n, priorityTrace i n ≤ p

@[simp] theorem mem_boundedPriorityIndices
    {priorityTrace : ℕ → ℕ → ℕ} {p i : ℕ} :
    i ∈ boundedPriorityIndices priorityTrace p ↔
      i ≤ p ∧ ∀ n, priorityTrace i n ≤ p := by
  classical
  simp [boundedPriorityIndices, Nat.lt_succ_iff]

theorem boundedPriorityIndices_subset_range
    (priorityTrace : ℕ → ℕ → ℕ) (p : ℕ) :
    boundedPriorityIndices priorityTrace p ⊆ Finset.range (p + 1) := by
  intro i hi
  exact Finset.mem_range.mpr
    (Nat.lt_succ_iff.mpr (mem_boundedPriorityIndices.mp hi).1)

/-- Under vanishing target noise and a positive target threshold, Algorithm
4 places the target in some finite stable priority class `𝓛(p)`. -/
theorem exists_boundedPriorityClass_of_vanishingNoise
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (target : ℕ)
    (hthreshold : 0 < threshold target)
    (hnoise : VanishingNoise stream (family target)) :
    ∃ p,
      target ∈ boundedPriorityIndices
        (thresholdPriorityTrace stream family threshold) p := by
  obtain ⟨T, hT⟩ :=
    thresholdPriorityTrace_eventually_constant_of_vanishingNoise
      stream family threshold target hthreshold hnoise
  let p :=
    thresholdPriorityTrace stream family threshold target T
  refine ⟨p, mem_boundedPriorityIndices.mpr ⟨?_, ?_⟩⟩
  · exact thresholdPriorityTrace_index_le
      stream family threshold target T
  · intro n
    rcases le_total n T with hnT | hTn
    · exact thresholdPriorityTrace_mono
        stream family threshold target hnT
    · exact (hT n hTn).le

/-- Lemma 4.1, Prefix Priority Stabilization.

Beyond one common time:

1. every member of the stable cutoff class has priority at most `p`;
2. every nonmember has priority strictly above `p`; and
3. every member's priority is unchanged by the next round.

The lower bound `i ≤ priority i n` handles all indices above `p`; only the
finite range through `p` must be synchronized. -/
theorem lemma_4_1_prefix_priority_stabilization
    (priorityTrace : ℕ → ℕ → ℕ)
    (hmono : ∀ i, Monotone (priorityTrace i))
    (hlower : ∀ i n, i ≤ priorityTrace i n)
    (p : ℕ) :
    ∃ N, p ≤ N ∧ ∀ n, N ≤ n →
      (∀ i, i ∈ boundedPriorityIndices priorityTrace p →
        priorityTrace i n ≤ p) ∧
      (∀ i, i ∉ boundedPriorityIndices priorityTrace p →
        p < priorityTrace i n) ∧
      (∀ i, i ∈ boundedPriorityIndices priorityTrace p →
        priorityTrace i (n + 1) = priorityTrace i n) := by
  classical
  let stable := boundedPriorityIndices priorityTrace p
  have hperIndex :
      ∀ i ∈ Finset.range (p + 1),
        ∀ᶠ n : ℕ in atTop,
          (i ∈ stable →
              priorityTrace i n ≤ p ∧
                priorityTrace i (n + 1) = priorityTrace i n) ∧
            (i ∉ stable → p < priorityTrace i n) := by
    intro i hi
    have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hbounded : ∀ n, priorityTrace i n ≤ p
    · obtain ⟨value, N, hN⟩ :=
        converges_of_monotone_of_bounded (hmono i) hbounded
      filter_upwards [eventually_ge_atTop N] with n hn
      have histable : i ∈ stable := by
        exact mem_boundedPriorityIndices.mpr ⟨hip, hbounded⟩
      constructor
      · intro _
        refine ⟨hbounded n, ?_⟩
        rw [hN n hn, hN (n + 1) (hn.trans (Nat.le_succ n))]
      · intro hinot
        exact (hinot histable).elim
    · push_neg at hbounded
      obtain ⟨crossing, hcrossing⟩ := hbounded
      have hinot : i ∉ stable := by
        intro histable
        exact (not_lt_of_ge
          ((mem_boundedPriorityIndices.mp histable).2 crossing))
          hcrossing
      filter_upwards [eventually_ge_atTop crossing] with n hn
      have habove : p < priorityTrace i n :=
        hcrossing.trans_le ((hmono i) hn)
      constructor
      · intro histable
        exact (hinot histable).elim
      · intro _
        exact habove
  have hall :
      ∀ᶠ n : ℕ in atTop,
        ∀ i ∈ Finset.range (p + 1),
          (i ∈ stable →
              priorityTrace i n ≤ p ∧
                priorityTrace i (n + 1) = priorityTrace i n) ∧
            (i ∉ stable → p < priorityTrace i n) :=
    (Finset.range (p + 1)).eventually_all.mpr hperIndex
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hall
  refine ⟨max p N₀, Nat.le_max_left _ _, ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := (Nat.le_max_right p N₀).trans hn
  have hnow := hN₀ n hn₀
  change
    (∀ i, i ∈ stable → priorityTrace i n ≤ p) ∧
      (∀ i, i ∉ stable → p < priorityTrace i n) ∧
      (∀ i, i ∈ stable →
        priorityTrace i (n + 1) = priorityTrace i n)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hirange : i ∈ Finset.range (p + 1) :=
      boundedPriorityIndices_subset_range priorityTrace p hi
    exact ((hnow i hirange).1 hi).1
  · intro i hi
    by_cases hip : i ≤ p
    · exact (hnow i
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hip))).2 hi
    · exact (Nat.lt_of_not_ge hip).trans_le (hlower i n)
  · intro i hi
    have hirange : i ∈ Finset.range (p + 1) :=
      boundedPriorityIndices_subset_range priorityTrace p hi
    exact ((hnow i hirange).1 hi).2

/-- The stable finite language class corresponding to
`boundedPriorityIndices`. -/
noncomputable def boundedPriorityLanguages
    (family : ℕ → GenLimit.Generic.Language α)
    (priorityTrace : ℕ → ℕ → ℕ) (p : ℕ) :
    Finset (GenLimit.Generic.Language α) := by
  classical
  exact (boundedPriorityIndices priorityTrace p).image family

/-- The finite language class selected by a finite set of indices. -/
noncomputable def indexedLanguages
    (family : ℕ → GenLimit.Generic.Language α)
    (indices : Finset ℕ) :
    Finset (GenLimit.Generic.Language α) := by
  classical
  exact indices.image family

/-- Corrected containment direction used by Theorem 5.1: when the target is
in the stable priority class, the class intersection is contained in the
target. -/
theorem boundedPriorityCore_subset_target
    (family : ℕ → GenLimit.Generic.Language α)
    (priorityTrace : ℕ → ℕ → ℕ) (p target : ℕ)
    (htarget : target ∈ boundedPriorityIndices priorityTrace p) :
    finiteCommonCore
        (boundedPriorityLanguages family priorityTrace p) ⊆
      family target := by
  apply finiteCommonCore_subset_of_mem
  classical
  exact Finset.mem_image.mpr ⟨target, htarget, rfl⟩

/-- Corollary 4.2's validity endgame.  Any selected finite class containing
the stable class also contains the target, so its intersection is a subset
of the target. -/
theorem corollary_4_2_selected_core_subset_target
    (family : ℕ → GenLimit.Generic.Language α)
    (priorityTrace : ℕ → ℕ → ℕ) (p target : ℕ)
    (selected : Finset ℕ)
    (hcontains :
      boundedPriorityIndices priorityTrace p ⊆ selected)
    (htarget : target ∈ boundedPriorityIndices priorityTrace p) :
    finiteCommonCore (indexedLanguages family selected) ⊆
      family target := by
  apply finiteCommonCore_subset_of_mem
  classical
  unfold indexedLanguages
  exact Finset.mem_image.mpr
    ⟨target, hcontains htarget, rfl⟩

/-- Corollary 4.2's one-round fresh-output core.  An infinite selected
intersection contains a point outside every finite forbidden set; the
corrected containment direction makes that point valid for the target. -/
theorem corollary_4_2_exists_fresh_target_output
    (family : ℕ → GenLimit.Generic.Language α)
    (priorityTrace : ℕ → ℕ → ℕ) (p target : ℕ)
    (selected : Finset ℕ)
    (hcontains :
      boundedPriorityIndices priorityTrace p ⊆ selected)
    (htarget : target ∈ boundedPriorityIndices priorityTrace p)
    (hinfinite :
      (finiteCommonCore
        (indexedLanguages family selected)).Infinite)
    (forbidden : Finset α) :
    ∃ x,
      x ∈ finiteCommonCore
          (indexedLanguages family selected) ∧
        x ∉ forbidden ∧ x ∈ family target := by
  have hnotSubset :
      ¬finiteCommonCore
          (indexedLanguages family selected) ⊆
        (forbidden : Set α) := by
    intro hsubset
    exact hinfinite (forbidden.finite_toSet.subset hsubset)
  obtain ⟨x, hxcore, hxfresh⟩ := Set.not_subset.mp hnotSubset
  exact ⟨x, hxcore, hxfresh,
    corollary_4_2_selected_core_subset_target
      family priorityTrace p target selected hcontains htarget hxcore⟩

end GenLimit.InfiniteContamination
