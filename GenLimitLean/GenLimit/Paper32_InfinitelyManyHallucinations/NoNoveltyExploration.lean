import GenLimit.Paper32_InfinitelyManyHallucinations.Certificates
import Mathlib.Data.Finset.Interval

/-!
# Algorithm 4.3: sparse exploration without novelty

This module gives a history-sensitive implementation of the no-novelty
construction.  Exploration index `k` is scheduled when the adversarial stage
cardinality first crosses the quadratic threshold `M * (k+1)^2`.  On that
round the generator reserves enough of the adversary's batch capacity for the
new exploration values and fills the remaining capacity with target-valid
adversarial values.

Scheduling by crossed cardinality rather than wall-clock time is extensionally
equivalent to the source's output-size clock for the two properties that
matter: every ambient index is explored, and the number of exploratory values
through size `m` is sublinear in `m`.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

/-- Exploration indices whose quadratic thresholds are at most `m`. -/
def explorationIndexPrefix (spacing m : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun k => quadraticTime spacing k ≤ m

/-- Exploration indices whose thresholds are crossed between cardinalities
`lo` and `hi`. -/
def crossedExplorationIndices (spacing lo hi : ℕ) : Finset ℕ :=
  (Finset.range hi).filter fun k =>
    lo < quadraticTime spacing k ∧ quadraticTime spacing k ≤ hi

theorem crossedExplorationIndices_subset_prefix
    (spacing lo hi : ℕ) :
    crossedExplorationIndices spacing lo hi ⊆
      explorationIndexPrefix spacing hi := by
  intro k hk
  simp only [crossedExplorationIndices, explorationIndexPrefix,
    Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨hk.1, hk.2.2⟩

theorem crossedExplorationIndices_eq_sdiff
    {spacing lo hi : ℕ} (hspacing : 0 < spacing) :
    crossedExplorationIndices spacing lo hi =
      explorationIndexPrefix spacing hi \
        explorationIndexPrefix spacing lo := by
  ext k
  simp only [crossedExplorationIndices, explorationIndexPrefix,
    Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
  constructor
  · rintro ⟨hkhi, hlo, hhi⟩
    refine ⟨⟨hkhi, hhi⟩, ?_⟩
    intro hklo
    exact (not_lt_of_ge hklo.2) hlo
  · rintro ⟨⟨hkhi, hhi⟩, hklo⟩
    refine ⟨hkhi, ?_, hhi⟩
    by_contra hnot
    apply hklo
    refine ⟨?_, le_of_not_gt hnot⟩
    have htimePos : 0 < quadraticTime spacing k := by
      unfold quadraticTime
      positivity
    have hkltTime : k < quadraticTime spacing k := by
      unfold quadraticTime
      have : k < (k + 1) ^ 2 := by nlinarith
      exact this.trans_le
        (Nat.le_mul_of_pos_left ((k + 1) ^ 2) hspacing)
    exact hkltTime.trans_le (le_of_not_gt hnot)

theorem explorationIndexPrefix_card_eq_explorationCount
    {spacing m : ℕ} (hspacing : 0 < spacing) :
    (explorationIndexPrefix spacing m).card =
      explorationCount (quadraticCarrier spacing) m := by
  classical
  let q := quadraticTime spacing
  have hinj : Function.Injective q := quadraticTime_injective hspacing
  have hImage :
      (explorationIndexPrefix spacing m).image q =
        (Finset.Icc 1 m).filter
          (fun n => n ∈ quadraticCarrier spacing) := by
    ext n
    simp only [Finset.mem_image, explorationIndexPrefix,
      Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
      quadraticCarrier, Set.mem_range]
    constructor
    · rintro ⟨k, ⟨hklt, hkq⟩, rfl⟩
      have hqpos : 1 ≤ q k := by
        unfold q quadraticTime
        have hpos : 0 < spacing * (k + 1) ^ 2 :=
          Nat.mul_pos hspacing (by positivity)
        omega
      exact ⟨⟨hqpos, hkq⟩, ⟨k, rfl⟩⟩
    · rintro ⟨⟨hnpos, hnle⟩, k, rfl⟩
      refine ⟨k, ⟨?_, hnle⟩, rfl⟩
      exact quadratic_index_lt_sqrt hspacing hnle |>.trans_le
        (Nat.sqrt_le_self m)
  unfold explorationCount
  rw [← hImage, Finset.card_image_iff.mpr hinj.injOn]

theorem crossedExplorationIndices_card_le_sub
    {spacing lo hi : ℕ} (hspacing : 0 < spacing) :
    (crossedExplorationIndices spacing lo hi).card ≤ hi - lo := by
  classical
  let q := quadraticTime spacing
  have hinj : Function.Injective q := quadraticTime_injective hspacing
  have himage :
      (crossedExplorationIndices spacing lo hi).image q ⊆
        Finset.Ioc lo hi := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    exact Finset.mem_Ioc.mpr (Finset.mem_filter.mp hk).2
  calc
    (crossedExplorationIndices spacing lo hi).card =
        ((crossedExplorationIndices spacing lo hi).image q).card :=
      (Finset.card_image_iff.mpr hinj.injOn).symm
    _ ≤ (Finset.Ioc lo hi).card := Finset.card_le_card himage
    _ = hi - lo := by simp

/-- A total finite-subset selector of size `min k |S|`. -/
noncomputable def chooseSubsetUpTo (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  Classical.choose (Finset.exists_subset_card_eq
    (Nat.min_le_right k S.card))

theorem chooseSubsetUpTo_subset (S : Finset ℕ) (k : ℕ) :
    chooseSubsetUpTo S k ⊆ S :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (Nat.min_le_right k S.card))).1

theorem card_chooseSubsetUpTo (S : Finset ℕ) (k : ℕ) :
    (chooseSubsetUpTo S k).card = min k S.card :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (Nat.min_le_right k S.card))).2

/-- Current stage in a finite adversarial history through round `n`. -/
def historyCurrent (n : ℕ) (history : Fin (n + 1) → Finset ℕ) : Finset ℕ :=
  history ⟨n, Nat.lt_succ_self n⟩

/-- Previous stage.  At round zero this is stage zero, which is empty on a
legal exhaustion. -/
def historyPrevious (n : ℕ) (history : Fin (n + 1) → Finset ℕ) : Finset ℕ :=
  history ⟨n - 1, by omega⟩

def historyIncrement (n : ℕ) (history : Fin (n + 1) → Finset ℕ) : Finset ℕ :=
  historyCurrent n history \ historyPrevious n history

@[simp] theorem historyCurrent_stage
    (adversary : Exhaustion) (n : ℕ) :
    historyCurrent n (fun i => adversary.stage i) = adversary.stage n :=
  rfl

@[simp] theorem historyPrevious_stage_succ
    (adversary : Exhaustion) (n : ℕ) :
    historyPrevious (n + 1) (fun i => adversary.stage i) =
      adversary.stage n := by
  simp [historyPrevious]

@[simp] theorem historyIncrement_stage_succ
    (adversary : Exhaustion) (n : ℕ) :
    historyIncrement (n + 1) (fun i => adversary.stage i) =
      adversary.increment (n + 1) := by
  simp [historyIncrement, Exhaustion.increment]

/-- Algorithm 4.3's capacity-respecting batch at one history. -/
noncomputable def noNoveltyExplorationBatch
    (spacing n : ℕ) (history : Fin (n + 1) → Finset ℕ)
    (previousGuess : Finset ℕ) : Finset ℕ := by
  let increment := historyIncrement n history
  let candidates := crossedExplorationIndices spacing
    (historyPrevious n history).card (historyCurrent n history).card
  let exploration := candidates \ previousGuess
  let safePool := (increment \ previousGuess) \ exploration
  let safeCapacity := increment.card - exploration.card
  exact exploration ∪ chooseSubsetUpTo safePool safeCapacity

noncomputable def noNoveltyExplorationGenerator
    (spacing : ℕ) : BatchGenerator :=
  fun n history previousGuess =>
    noNoveltyExplorationBatch spacing n history previousGuess

/-! ## The concrete run -/

def crossedAt
    (spacing : ℕ) (adversary : Exhaustion) (n : ℕ) : Finset ℕ :=
  crossedExplorationIndices spacing
    (adversary.stage n).card (adversary.stage (n + 1)).card

def explorationAt
    (spacing : ℕ) (adversary : Exhaustion)
    (previousGuess : Finset ℕ) (n : ℕ) : Finset ℕ :=
  crossedAt spacing adversary n \ previousGuess

def safePoolAt
    (spacing : ℕ) (adversary : Exhaustion)
    (previousGuess : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (adversary.increment (n + 1) \ previousGuess) \
    explorationAt spacing adversary previousGuess n

noncomputable def concreteBatch
    (spacing : ℕ) (adversary : Exhaustion)
    (previousGuess : Finset ℕ) (n : ℕ) : Finset ℕ :=
  let exploration := explorationAt spacing adversary previousGuess n
  let safePool := safePoolAt spacing adversary previousGuess n
  let safeCapacity :=
    (adversary.increment (n + 1)).card - exploration.card
  exploration ∪ chooseSubsetUpTo safePool safeCapacity

theorem noNoveltyExplorationBatch_stage_succ
    (spacing : ℕ) (adversary : Exhaustion)
    (previousGuess : Finset ℕ) (n : ℕ) :
    noNoveltyExplorationBatch spacing (n + 1)
        (fun i => adversary.stage i) previousGuess =
      concreteBatch spacing adversary previousGuess n := by
  simp [noNoveltyExplorationBatch, concreteBatch, explorationAt,
    crossedAt, safePoolAt]

theorem crossedAt_card_le_increment
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (n : ℕ) :
    (crossedAt spacing adversary n).card ≤
      (adversary.increment (n + 1)).card := by
  have hcross := crossedExplorationIndices_card_le_sub
    (spacing := spacing)
    (lo := (adversary.stage n).card)
    (hi := (adversary.stage (n + 1)).card) hspacing
  rw [Exhaustion.increment,
    Finset.card_sdiff_of_subset
      (adversary.monotone_stage (Nat.le_succ n))]
  exact hcross

theorem explorationAt_card_le_increment
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (previousGuess : Finset ℕ) (n : ℕ) :
    (explorationAt spacing adversary previousGuess n).card ≤
      (adversary.increment (n + 1)).card := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    (crossedAt_card_le_increment hspacing adversary n)

theorem explorationAt_disjoint_previousGuess
    (spacing : ℕ) (adversary : Exhaustion)
    (previousGuess : Finset ℕ) (n : ℕ) :
    Disjoint (explorationAt spacing adversary previousGuess n)
      previousGuess := by
  rw [Finset.disjoint_left]
  intro x hx hprevious
  exact (Finset.mem_sdiff.mp hx).2 hprevious

theorem concreteBatch_disjoint_previousGuess
    (spacing : ℕ) (adversary : Exhaustion)
    (previousGuess : Finset ℕ) (n : ℕ) :
    Disjoint (concreteBatch spacing adversary previousGuess n)
      previousGuess := by
  apply Finset.disjoint_union_left.mpr
  refine ⟨explorationAt_disjoint_previousGuess spacing adversary
    previousGuess n, ?_⟩
  rw [Finset.disjoint_left]
  intro x hx hprevious
  have hxPool := chooseSubsetUpTo_subset
    (safePoolAt spacing adversary previousGuess n)
    ((adversary.increment (n + 1)).card -
      (explorationAt spacing adversary previousGuess n).card) hx
  have hxFresh : x ∈ adversary.increment (n + 1) \ previousGuess :=
    (Finset.mem_sdiff.mp hxPool).1
  exact (Finset.mem_sdiff.mp hxFresh).2 hprevious

theorem concreteBatch_card_le_increment
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (previousGuess : Finset ℕ) (n : ℕ) :
    (concreteBatch spacing adversary previousGuess n).card ≤
      (adversary.increment (n + 1)).card := by
  let exploration := explorationAt spacing adversary previousGuess n
  let safePool := safePoolAt spacing adversary previousGuess n
  let safeCapacity :=
    (adversary.increment (n + 1)).card - exploration.card
  have hexploration : exploration.card ≤
      (adversary.increment (n + 1)).card := by
    exact explorationAt_card_le_increment hspacing adversary previousGuess n
  have hdisjoint :
      Disjoint exploration (chooseSubsetUpTo safePool safeCapacity) := by
    rw [Finset.disjoint_left]
    intro x hxExploration hxSafe
    have hxPool := chooseSubsetUpTo_subset safePool safeCapacity hxSafe
    exact (Finset.mem_sdiff.mp hxPool).2 hxExploration
  rw [concreteBatch, Finset.card_union_of_disjoint hdisjoint,
    card_chooseSubsetUpTo]
  have hmin : min safeCapacity safePool.card ≤ safeCapacity :=
    Nat.min_le_left _ _
  dsimp only [safeCapacity] at hmin
  omega

theorem generated_increment_noNoveltyExplorationGenerator
    (spacing : ℕ) (adversary : Exhaustion) (n : ℕ) :
    (generatedExhaustion (noNoveltyExplorationGenerator spacing) adversary).increment
        (n + 1) =
      concreteBatch spacing adversary
        (generatedStages (noNoveltyExplorationGenerator spacing) adversary n) n := by
  let previous :=
    generatedStages (noNoveltyExplorationGenerator spacing) adversary n
  let batch := concreteBatch spacing adversary previous n
  have hdisjoint : Disjoint previous batch :=
    (concreteBatch_disjoint_previousGuess spacing adversary previous n).symm
  change (previous ∪ batch) \ previous = batch
  exact Finset.union_sdiff_cancel_left hdisjoint

theorem generated_boundedBy_noNoveltyExplorationGenerator
    {spacing : ℕ} (hspacing : 0 < spacing)
    (f : ℕ → ℕ) {adversary : Exhaustion}
    (hbounded : adversary.BoundedBy f) :
    (generatedExhaustion
      (noNoveltyExplorationGenerator spacing) adversary).BoundedBy f := by
  intro n
  rw [generated_increment_noNoveltyExplorationGenerator]
  exact (concreteBatch_card_le_increment hspacing adversary _ n).trans
    (hbounded n)

theorem crossed_index_generated_next
    (spacing : ℕ) (adversary : Exhaustion) (n k : ℕ)
    (hk : k ∈ crossedAt spacing adversary n) :
    k ∈ generatedStages (noNoveltyExplorationGenerator spacing)
      adversary (n + 1) := by
  let previous :=
    generatedStages (noNoveltyExplorationGenerator spacing) adversary n
  by_cases hkPrevious : k ∈ previous
  · exact Finset.mem_union_left _ hkPrevious
  · apply Finset.mem_union_right previous
    rw [noNoveltyExplorationGenerator,
      noNoveltyExplorationBatch_stage_succ]
    apply Finset.mem_union_left
    exact Finset.mem_sdiff.mpr ⟨hk, hkPrevious⟩

theorem exists_crossedAt
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (hinfinite : adversary.limit.Infinite)
    (k : ℕ) :
    ∃ n, k ∈ crossedAt spacing adversary n := by
  let q := quadraticTime spacing k
  have hqpos : 0 < q := by
    unfold q quadraticTime
    exact Nat.mul_pos hspacing (by positivity)
  have hkq : k < q := by
    unfold q quadraticTime
    have hkSquare : k < (k + 1) ^ 2 := by nlinarith
    exact hkSquare.trans_le
      (Nat.le_mul_of_pos_left ((k + 1) ^ 2) hspacing)
  have hreachEventually :
      ∀ᶠ n : ℕ in atTop, q ≤ (adversary.stage n).card :=
    (adversary.card_tendsto_atTop_of_limit_infinite hinfinite).eventually
      (eventually_ge_atTop q)
  let hex : ∃ n, q ≤ (adversary.stage n).card :=
    hreachEventually.exists
  have hfindNe : Nat.find hex ≠ 0 := by
    intro hzero
    have hfirst := Nat.find_spec hex
    rw [hzero, adversary.stage_zero] at hfirst
    simp only [Finset.card_empty] at hfirst
    omega
  obtain ⟨n, hfindEq⟩ := Nat.exists_eq_succ_of_ne_zero hfindNe
  have hfirst : q ≤ (adversary.stage (n + 1)).card := by
    simpa [hfindEq] using Nat.find_spec hex
  have hprevious : (adversary.stage n).card < q := by
    apply lt_of_not_ge
    apply Nat.find_min hex
    rw [hfindEq]
    exact Nat.lt_succ_self n
  refine ⟨n, ?_⟩
  simp only [crossedAt, crossedExplorationIndices,
    Finset.mem_filter, Finset.mem_range]
  exact ⟨hkq.trans_le hfirst, hprevious, hfirst⟩

/-- Every ambient code is eventually generated.  This is the constructive
perfect-recall part of Theorem 4.3. -/
theorem noNoveltyExplorationGenerator_covers_universe
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (hinfinite : adversary.limit.Infinite) :
    (Set.univ : Language) ⊆
      (generatedExhaustion
        (noNoveltyExplorationGenerator spacing) adversary).limit := by
  intro k _hk
  obtain ⟨n, hkCrossed⟩ :=
    exists_crossedAt hspacing adversary hinfinite k
  exact ⟨n + 1,
    crossed_index_generated_next spacing adversary n k hkCrossed⟩

theorem explorationIndexPrefix_mono
    (spacing : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    explorationIndexPrefix spacing m ⊆ explorationIndexPrefix spacing n := by
  intro k hk
  simp only [explorationIndexPrefix, Finset.mem_filter,
    Finset.mem_range] at hk ⊢
  exact ⟨hk.1.trans_le hmn, hk.2.trans hmn⟩

theorem concreteBatch_subset_increment_union_prefix
    (spacing : ℕ) (adversary : Exhaustion)
    (previousGuess : Finset ℕ) (n : ℕ) :
    concreteBatch spacing adversary previousGuess n ⊆
      adversary.increment (n + 1) ∪
        explorationIndexPrefix spacing (adversary.stage (n + 1)).card := by
  intro x hx
  rw [concreteBatch, Finset.mem_union] at hx
  rcases hx with hxExplore | hxSafe
  · apply Finset.mem_union_right
    exact crossedExplorationIndices_subset_prefix _ _ _
      (Finset.mem_of_subset Finset.sdiff_subset hxExplore)
  · apply Finset.mem_union_left
    have hxPool := chooseSubsetUpTo_subset
      (safePoolAt spacing adversary previousGuess n)
      ((adversary.increment (n + 1)).card -
        (explorationAt spacing adversary previousGuess n).card) hxSafe
    exact Finset.mem_of_subset Finset.sdiff_subset
      (Finset.mem_of_subset Finset.sdiff_subset hxPool)

/-- At every finite stage, all generated values are either already revealed
by the adversary or are one of the exploration indices whose threshold has
been crossed. -/
theorem generatedStages_subset_adversary_union_explorationPrefix
    (spacing : ℕ) (adversary : Exhaustion) (n : ℕ) :
    generatedStages (noNoveltyExplorationGenerator spacing) adversary n ⊆
      adversary.stage n ∪
        explorationIndexPrefix spacing (adversary.stage n).card := by
  induction n with
  | zero => simp [generatedStages, adversary.stage_zero,
      explorationIndexPrefix]
  | succ n ih =>
      rw [generatedStages, noNoveltyExplorationGenerator,
        noNoveltyExplorationBatch_stage_succ]
      apply Finset.union_subset
      · intro x hx
        have hx' := ih hx
        rw [Finset.mem_union] at hx' ⊢
        rcases hx' with hxAdversary | hxExplore
        · exact Or.inl (adversary.monotone_stage (Nat.le_succ n) hxAdversary)
        · exact Or.inr (explorationIndexPrefix_mono spacing
            (Finset.card_le_card
              (adversary.monotone_stage (Nat.le_succ n))) hxExplore)
      · exact (concreteBatch_subset_increment_union_prefix
          spacing adversary _ n).trans
          (Finset.union_subset_union
            (adversary.increment_subset_stage (n + 1))
            Finset.Subset.rfl)

theorem invalidCount_generatedStage_le_explorationCount_adversaryCard
    {spacing : ℕ} (hspacing : 0 < spacing)
    {L : Language} (adversary : Exhaustion)
    (hvalid : adversary.limit ⊆ L) (n : ℕ) :
    invalidCount L
        (generatedStages (noNoveltyExplorationGenerator spacing) adversary n) ≤
      explorationCount (quadraticCarrier spacing)
        (adversary.stage n).card := by
  classical
  unfold invalidCount
  rw [← explorationIndexPrefix_card_eq_explorationCount hspacing]
  apply Finset.card_le_card
  intro x hx
  have hxGenerated :
      x ∈ generatedStages (noNoveltyExplorationGenerator spacing)
        adversary n := (Finset.mem_filter.mp hx).1
  have hxInvalid : x ∉ L := (Finset.mem_filter.mp hx).2
  rcases Finset.mem_union.mp
      (generatedStages_subset_adversary_union_explorationPrefix
        spacing adversary n hxGenerated) with hxAdversary | hxExplore
  · exact False.elim (hxInvalid
      (hvalid (adversary.stage_subset_limit n hxAdversary)))
  · exact hxExplore

theorem freshMissing_card_le_exploration
    (increment previousGuess exploration : Finset ℕ)
    (hexploration : exploration.card ≤ increment.card) :
    let safePool := (increment \ previousGuess) \ exploration
    let safeCapacity := increment.card - exploration.card
    let retained := chooseSubsetUpTo safePool safeCapacity
    ((increment \ previousGuess) \ (exploration ∪ retained)).card ≤
      exploration.card := by
  dsimp only
  let safePool := (increment \ previousGuess) \ exploration
  let safeCapacity := increment.card - exploration.card
  let retained := chooseSubsetUpTo safePool safeCapacity
  have hmissingEq :
      (increment \ previousGuess) \ (exploration ∪ retained) =
        safePool \ retained := by
    ext x
    simp [safePool]
    tauto
  have hretained : retained ⊆ safePool :=
    chooseSubsetUpTo_subset safePool safeCapacity
  have hpool : safePool.card ≤ increment.card :=
    Finset.card_le_card
      (Finset.sdiff_subset.trans Finset.sdiff_subset)
  rw [hmissingEq, Finset.card_sdiff_of_subset hretained,
    show retained.card = min safeCapacity safePool.card from
      card_chooseSubsetUpTo safePool safeCapacity]
  dsimp only [safeCapacity]
  omega

theorem missing_succ_card_le_add_crossed
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (previousGuess : Finset ℕ) (n : ℕ) :
    (adversary.stage (n + 1) \
        (previousGuess ∪
          concreteBatch spacing adversary previousGuess n)).card ≤
      (adversary.stage n \ previousGuess).card +
        (crossedAt spacing adversary n).card := by
  let increment := adversary.increment (n + 1)
  let exploration := explorationAt spacing adversary previousGuess n
  let safePool := safePoolAt spacing adversary previousGuess n
  let safeCapacity := increment.card - exploration.card
  let retained := chooseSubsetUpTo safePool safeCapacity
  have hexploration : exploration.card ≤ increment.card :=
    explorationAt_card_le_increment hspacing adversary previousGuess n
  have hfreshMissing :
      ((increment \ previousGuess) \
        (exploration ∪ retained)).card ≤ exploration.card := by
    simpa [increment, exploration, safePool, safeCapacity, retained,
      safePoolAt] using
      freshMissing_card_le_exploration increment previousGuess exploration
        hexploration
  have hsubset :
      adversary.stage (n + 1) \
          (previousGuess ∪ concreteBatch spacing adversary previousGuess n) ⊆
        (adversary.stage n \ previousGuess) ∪
          ((increment \ previousGuess) \ (exploration ∪ retained)) := by
    intro x hx
    have hxStage : x ∈ adversary.stage (n + 1) :=
      (Finset.mem_sdiff.mp hx).1
    have hxNotUnion := (Finset.mem_sdiff.mp hx).2
    have hxNotPrevious : x ∉ previousGuess := by
      intro hxPrevious
      exact hxNotUnion (Finset.mem_union_left _ hxPrevious)
    by_cases hxOld : x ∈ adversary.stage n
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hxOld, hxNotPrevious⟩)
    · apply Finset.mem_union_right
      have hxIncrement : x ∈ increment := by
        dsimp only [increment]
        simp [Exhaustion.increment, hxStage, hxOld]
      have hxFresh : x ∈ increment \ previousGuess :=
        Finset.mem_sdiff.mpr ⟨hxIncrement, hxNotPrevious⟩
      have hxNotBatch :
          x ∉ exploration ∪ retained := by
        intro hxBatch
        apply hxNotUnion
        apply Finset.mem_union_right previousGuess
        simpa [concreteBatch, increment, exploration, safePool,
          safeCapacity, retained] using hxBatch
      exact Finset.mem_sdiff.mpr ⟨hxFresh, hxNotBatch⟩
  calc
    (adversary.stage (n + 1) \
        (previousGuess ∪
          concreteBatch spacing adversary previousGuess n)).card ≤
        ((adversary.stage n \ previousGuess) ∪
          ((increment \ previousGuess) \
            (exploration ∪ retained))).card :=
      Finset.card_le_card hsubset
    _ ≤ (adversary.stage n \ previousGuess).card +
          ((increment \ previousGuess) \
            (exploration ∪ retained)).card :=
      Finset.card_union_le _ _
    _ ≤ (adversary.stage n \ previousGuess).card +
          exploration.card := Nat.add_le_add_left hfreshMissing _
    _ ≤ (adversary.stage n \ previousGuess).card +
          (crossedAt spacing adversary n).card :=
      Nat.add_le_add_left (Finset.card_le_card Finset.sdiff_subset) _

theorem prefix_card_add_crossedAt_card
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (n : ℕ) :
    (explorationIndexPrefix spacing (adversary.stage n).card).card +
        (crossedAt spacing adversary n).card =
      (explorationIndexPrefix spacing
        (adversary.stage (n + 1)).card).card := by
  have hstageCard : (adversary.stage n).card ≤
      (adversary.stage (n + 1)).card :=
    Finset.card_le_card
      (adversary.monotone_stage (Nat.le_succ n))
  have hprefix :
      explorationIndexPrefix spacing (adversary.stage n).card ⊆
        explorationIndexPrefix spacing (adversary.stage (n + 1)).card :=
    explorationIndexPrefix_mono spacing hstageCard
  have hprefixCard := Finset.card_le_card hprefix
  rw [crossedAt, crossedExplorationIndices_eq_sdiff hspacing,
    Finset.card_sdiff_of_subset hprefix]
  omega

/-- At each stage, the adversarial values omitted by the capacity-respecting
exploration construction are no more numerous than the exploration indices
whose thresholds have already been crossed. -/
theorem adversary_missing_generated_card_le_explorationPrefix
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (n : ℕ) :
    (adversary.stage n \
        generatedStages (noNoveltyExplorationGenerator spacing)
          adversary n).card ≤
      (explorationIndexPrefix spacing (adversary.stage n).card).card := by
  induction n with
  | zero => simp [generatedStages, adversary.stage_zero,
      explorationIndexPrefix]
  | succ n ih =>
      have hstep := missing_succ_card_le_add_crossed hspacing
        adversary
        (generatedStages (noNoveltyExplorationGenerator spacing)
          adversary n) n
      have hgenerated :
          generatedStages (noNoveltyExplorationGenerator spacing)
              adversary (n + 1) =
            generatedStages (noNoveltyExplorationGenerator spacing)
                adversary n ∪
              concreteBatch spacing adversary
                (generatedStages (noNoveltyExplorationGenerator spacing)
                  adversary n) n := by
        change
          generatedStages (noNoveltyExplorationGenerator spacing)
                adversary n ∪
              noNoveltyExplorationBatch spacing (n + 1)
                (fun i => adversary.stage i)
                (generatedStages (noNoveltyExplorationGenerator spacing)
                  adversary n) = _
        rw [noNoveltyExplorationBatch_stage_succ]
      calc
        (adversary.stage (n + 1) \
            generatedStages (noNoveltyExplorationGenerator spacing)
              adversary (n + 1)).card ≤
            (adversary.stage n \
              generatedStages (noNoveltyExplorationGenerator spacing)
                adversary n).card +
              (crossedAt spacing adversary n).card := by
          rw [hgenerated]
          exact hstep
        _ ≤ (explorationIndexPrefix spacing
              (adversary.stage n).card).card +
              (crossedAt spacing adversary n).card :=
          Nat.add_le_add_right ih _
        _ = (explorationIndexPrefix spacing
              (adversary.stage (n + 1)).card).card :=
          prefix_card_add_crossedAt_card hspacing adversary n

theorem control_le_generated_card_add_explorationCount
    {spacing : ℕ} (hspacing : 0 < spacing)
    (adversary : Exhaustion) (n : ℕ) :
    (adversary.stage n).card ≤
      (generatedStages (noNoveltyExplorationGenerator spacing)
          adversary n).card +
        explorationCount (quadraticCarrier spacing)
          (adversary.stage n).card := by
  let guessStage :=
    generatedStages (noNoveltyExplorationGenerator spacing) adversary n
  have hcover : adversary.stage n ⊆
      guessStage ∪ (adversary.stage n \ guessStage) := by
    intro x hx
    by_cases hxGuess : x ∈ guessStage
    · exact Finset.mem_union_left _ hxGuess
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hx, hxGuess⟩)
  have hcardCover := (Finset.card_le_card hcover).trans
    (Finset.card_union_le _ _)
  have hmissing :=
    adversary_missing_generated_card_le_explorationPrefix
      hspacing adversary n
  rw [explorationIndexPrefix_card_eq_explorationCount hspacing]
    at hmissing
  dsimp only [guessStage] at hcardCover ⊢
  omega

def noNovelty_controlledSparseCertificate
    {spacing : ℕ} (hspacing : 2 ≤ spacing)
    {L : Language} (adversary : Exhaustion)
    (hinfinite : adversary.limit.Infinite)
    (hvalid : adversary.limit ⊆ L) :
    ControlledSparseExplorationCertificate
      (quadraticExplorationSet spacing hspacing) L
      (generatedExhaustion
        (noNoveltyExplorationGenerator spacing) adversary) where
  control := fun n => (adversary.stage n).card
  control_tendsto_atTop :=
    adversary.card_tendsto_atTop_of_limit_infinite hinfinite
  invalid_le_exploration := by
    intro n
    change invalidCount L
        (generatedStages (noNoveltyExplorationGenerator spacing)
          adversary n) ≤ _
    exact invalidCount_generatedStage_le_explorationCount_adversaryCard
      (lt_of_lt_of_le (by decide) hspacing) adversary hvalid n
  control_le_guess_add_exploration := by
    intro n
    change (adversary.stage n).card ≤
      (generatedStages (noNoveltyExplorationGenerator spacing)
          adversary n).card + _
    exact control_le_generated_card_add_explorationCount
      (lt_of_lt_of_le (by decide) hspacing) adversary n

theorem lowerMembershipPrecision_noNoveltyExplorationGenerator
    {spacing : ℕ} (hspacing : 2 ≤ spacing)
    {L : Language} (adversary : Exhaustion)
    (hinfinite : adversary.limit.Infinite)
    (hvalid : adversary.limit ⊆ L) :
    lowerMembershipPrecision L
        (generatedExhaustion
          (noNoveltyExplorationGenerator spacing) adversary) = 1 :=
  (noNovelty_controlledSparseCertificate hspacing adversary
    hinfinite hvalid).precision_one

/-- Theorem 4.3, with an explicit universal generator.  The construction is
independent of the language family: for every infinite partial adversarial
exhaustion it preserves the same batch bound, explores the whole countable
universe, and attains perfect recall and membership precision. -/
theorem theorem_4_3
    (target : GenLimit.KleinbergWei.OrderedLanguage)
    (L : Language) (f : ℕ → ℕ) :
    ∃ G : BatchGenerator, ∀ adversary : Exhaustion,
      adversary.limit.Infinite →
      adversary.limit ⊆ L →
      adversary.BoundedBy f →
      let guess := generatedExhaustion G adversary
      guess.BoundedBy f ∧
        lowerRecall target guess.limit = 1 ∧
        lowerMembershipPrecision L guess = 1 := by
  refine ⟨noNoveltyExplorationGenerator 2, ?_⟩
  intro adversary hinfinite hvalid hbounded
  dsimp only
  refine ⟨generated_boundedBy_noNoveltyExplorationGenerator
      (by decide) f hbounded, ?_, ?_⟩
  · apply lowerRecall_eq_one_of_target_subset
    intro x _hx
    exact noNoveltyExplorationGenerator_covers_universe
      (by decide) adversary hinfinite (Set.mem_univ x)
  · exact lowerMembershipPrecision_noNoveltyExplorationGenerator
      (by decide) adversary hinfinite hvalid

end GenLimit.InfinitelyManyHallucinations
