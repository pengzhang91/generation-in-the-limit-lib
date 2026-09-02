import GenLimit.Paper17_InfiniteContamination.AlgorithmSixSeven
import GenLimit.Paper17_InfiniteContamination.ElementDensity
import GenLimit.Support.KleinbergWei.OrderedPositions
import Mathlib.Data.Nat.Find

/-!
# Algorithm 8: extracting element density from set density

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Algorithm 8, Theorem 6.15, Corollary 6.16,
and Claim 6.17.

The implementation below keeps the source's essential adaptive mechanism.
For each past set output it computes a finite prefix after which every
currently selected language sees the output at approximately its lower
density.  At round `t`, it uses the latest past stage whose cutoff fits the
current linear budget and returns the least globally ordered point outside
the input sample and all previous outputs.

The source additionally replaces each cutoff by a strictly increasing
envelope.  That normalization is not needed: every fixed past cutoff fits
the growing budget eventually, which already makes the selected stage tend
to infinity and proves the same rank and density bounds.
-/

namespace GenLimit.InfiniteContamination

open Filter
open scoped Topology
open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback

/-! ## Eventual lower-density cutoffs -/

/-- The multiplicative slack `1 + 2⁻ⁿ` used at zero-based stage `n`.
The exponent is shifted by one to match the paper's one-based rounds. -/
noncomputable def densitySlack (n : ℕ) : ℝ :=
  1 + (1 / 2 : ℝ) ^ (n + 1)

theorem densitySlack_pos (n : ℕ) : 0 < densitySlack n := by
  unfold densitySlack
  positivity

theorem one_lt_densitySlack (n : ℕ) : 1 < densitySlack n := by
  unfold densitySlack
  have hpow : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  linarith

theorem tendsto_densitySlack_atTop :
    Tendsto densitySlack atTop (nhds 1) := by
  unfold densitySlack
  have hpow :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hshift := hpow.comp (tendsto_add_atTop_nat 1)
  simpa using tendsto_const_nhds.add hshift

theorem exists_eventual_density_cutoff
    (K : OrderedLanguage) (A : Set ℕ) (stage : ℕ) :
    ∃ N, ∀ m, N ≤ m →
      K.lowerDensity A / densitySlack stage ≤
        K.prefixRatio A m := by
  have hdnonneg := K.lowerDensity_nonneg A
  by_cases hd : K.lowerDensity A = 0
  · refine ⟨0, fun m _hm => ?_⟩
    rw [hd, zero_div]
    exact K.prefixRatio_nonneg A m
  · have hdpos : 0 < K.lowerDensity A :=
      lt_of_le_of_ne hdnonneg (Ne.symm hd)
    have hlt :
        K.lowerDensity A / densitySlack stage <
          K.lowerDensity A := by
      rw [div_lt_iff₀ (densitySlack_pos stage)]
      nlinarith [one_lt_densitySlack stage]
    have heventually :
        ∀ᶠ m : ℕ in atTop,
          K.lowerDensity A / densitySlack stage <
            K.prefixRatio A m :=
      eventually_lt_of_lt_liminf hlt
        (isBoundedUnder_of
          ⟨0, fun m => K.prefixRatio_nonneg A m⟩)
    obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
    exact ⟨N, fun m hm => (hN m hm).le⟩

/-- A chosen cutoff witnessing the eventual lower-density estimate. -/
noncomputable def densityCutoff
    (K : OrderedLanguage) (A : Set ℕ) (stage : ℕ) : ℕ :=
  Classical.choose (exists_eventual_density_cutoff K A stage)

theorem densityCutoff_spec
    (K : OrderedLanguage) (A : Set ℕ) (stage : ℕ)
    {m : ℕ} (hm : densityCutoff K A stage ≤ m) :
    K.lowerDensity A / densitySlack stage ≤
      K.prefixRatio A m :=
  Classical.choose_spec
    (exists_eventual_density_cutoff K A stage) m hm

/-- One cutoff which works for every language in a finite selected class. -/
noncomputable def finiteDensityCutoff
    (orders : ℕ → OrderedLanguage)
    (selected : Finset ℕ) (A : Set ℕ) (stage : ℕ) : ℕ :=
  selected.sup fun i => densityCutoff (orders i) A stage

theorem finiteDensityCutoff_spec
    (orders : ℕ → OrderedLanguage)
    (selected : Finset ℕ) (A : Set ℕ) (stage : ℕ)
    {i m : ℕ} (hi : i ∈ selected)
    (hm : finiteDensityCutoff orders selected A stage ≤ m) :
    (orders i).lowerDensity A / densitySlack stage ≤
      (orders i).prefixRatio A m := by
  apply densityCutoff_spec
  exact (Finset.le_sup (f := fun j =>
    densityCutoff (orders j) A stage) hi).trans hm

/-! ## Adaptive past-stage selection -/

/-- The source's cutoff at one stage of a fixed run. -/
noncomputable def algorithmEightStageCutoff
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ) (stage : ℕ) : ℕ :=
  finiteDensityCutoff orders
    (selection stage (fun i => stream i))
    (setOutput setGen stream stage) stage

/-- A past stage fits round `t` when its density cutoff is small enough to
leave twice the round number many low-rank candidates. -/
def AlgorithmEightBudget
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (stream : GenLimit.Generic.Stream ℕ)
    (stage t : ℕ) : Prop :=
  (algorithmEightStageCutoff setGen selection orders stream stage : ℝ) /
      densitySlack stage ≤
    2 * (t + 1 : ℕ) / ρ

/-- Stage zero is the source's total fallback when no positive stage yet
fits the budget. -/
def AlgorithmEightAdmissible
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (stream : GenLimit.Generic.Stream ℕ)
    (stage t : ℕ) : Prop :=
  stage = 0 ∨
    AlgorithmEightBudget
      setGen selection orders ρ stream stage t

/-- Latest fitting past stage. -/
noncomputable def algorithmEightIndexOn
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun stage =>
      AlgorithmEightAdmissible
        setGen selection orders ρ stream stage t) t

theorem algorithmEightIndexOn_le
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) :
    algorithmEightIndexOn setGen selection orders ρ stream t ≤ t := by
  classical
  exact Nat.findGreatest_le t

theorem algorithmEightIndexOn_admissible
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) :
    AlgorithmEightAdmissible setGen selection orders ρ stream
      (algorithmEightIndexOn setGen selection orders ρ stream t) t := by
  classical
  let P : ℕ → Prop := fun stage =>
    AlgorithmEightAdmissible
      setGen selection orders ρ stream stage t
  change P (Nat.findGreatest P t)
  exact @Nat.findGreatest_spec 0 P (Classical.decPred P) t
    (Nat.zero_le t) (Or.inl rfl)

/-- Every fixed past stage eventually fits, so the chosen stages tend to
infinity. -/
theorem tendsto_algorithmEightIndexOn_atTop
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (hρ : 0 < ρ)
    (stream : GenLimit.Generic.Stream ℕ) :
    Tendsto
      (algorithmEightIndexOn setGen selection orders ρ stream)
      atTop atTop := by
  classical
  rw [tendsto_atTop]
  intro stage
  let a : ℝ :=
    (algorithmEightStageCutoff
        setGen selection orders stream stage : ℝ) /
      densitySlack stage
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (a * ρ / 2)
  filter_upwards [eventually_ge_atTop (max stage T)] with t ht
  have hstage : stage ≤ t := (Nat.le_max_left _ _).trans ht
  apply Nat.le_findGreatest hstage
  right
  change a ≤ 2 * (t + 1 : ℕ) / ρ
  have hTR : a * ρ / 2 < (t + 1 : ℕ) := by
    have hTt : T ≤ t := (Nat.le_max_right _ _).trans ht
    have hcast : (T : ℝ) ≤ t := by exact_mod_cast hTt
    exact hT.trans_le (hcast.trans (by norm_num))
  rw [le_div_iff₀ hρ]
  nlinarith

/-! ## Finite-history form and recursive output -/

/-- Algorithm 8's stage index computed solely from the supplied history. -/
noncomputable def algorithmEightHistoryIndex
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) {t : ℕ} (xs : Fin t → ℕ) : ℕ :=
  algorithmEightIndexOn setGen selection orders ρ
    (prefixCompletion 0 xs) t

theorem algorithmEightStageCutoff_eq_of_eq_on_prefix
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    {stream₁ stream₂ : GenLimit.Generic.Stream ℕ} {stage : ℕ}
    (h : ∀ i, i < stage → stream₁ i = stream₂ i) :
    algorithmEightStageCutoff
        setGen selection orders stream₁ stage =
      algorithmEightStageCutoff
        setGen selection orders stream₂ stage := by
  have hhistory :
      (fun i : Fin stage => stream₁ i) =
        fun i : Fin stage => stream₂ i := by
    funext i
    exact h i i.isLt
  unfold algorithmEightStageCutoff setOutput
  rw [hhistory]

theorem algorithmEightHistoryIndex_eq_stream
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    algorithmEightHistoryIndex setGen selection orders ρ
        (fun i : Fin t => stream i) =
      algorithmEightIndexOn setGen selection orders ρ stream t := by
  classical
  unfold algorithmEightHistoryIndex algorithmEightIndexOn
  let completed :=
    prefixCompletion 0 (fun i : Fin t => stream i)
  let P : ℕ → Prop := fun stage =>
    AlgorithmEightAdmissible
      setGen selection orders ρ completed stage t
  let Q : ℕ → Prop := fun stage =>
    AlgorithmEightAdmissible
      setGen selection orders ρ stream stage t
  have hiff : ∀ stage, stage ≤ t → (P stage ↔ Q stage) := by
    intro stage hstage
    have hcutoff :
        algorithmEightStageCutoff
            setGen selection orders completed stage =
          algorithmEightStageCutoff
            setGen selection orders stream stage := by
      apply algorithmEightStageCutoff_eq_of_eq_on_prefix
      intro i hi
      simp [completed, hi.trans_le hstage]
    simp only [P, Q, AlgorithmEightAdmissible,
      AlgorithmEightBudget]
    rw [hcutoff]
  change Nat.findGreatest P t = Nat.findGreatest Q t
  have hPzero : P 0 := by
    exact Or.inl rfl
  have hQzero : Q 0 := by
    exact Or.inl rfl
  apply le_antisymm
  · apply Nat.le_findGreatest (Nat.findGreatest_le t)
    exact (hiff _ (Nat.findGreatest_le t)).mp
      (Nat.findGreatest_spec (Nat.zero_le t) hPzero)
  · apply Nat.le_findGreatest (Nat.findGreatest_le t)
    exact (hiff _ (Nat.findGreatest_le t)).mpr
      (Nat.findGreatest_spec (Nat.zero_le t) hQzero)

/-- Stage set chosen at a finite history. -/
noncomputable def algorithmEightChosenSet
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) {t : ℕ} (xs : Fin t → ℕ) : Set ℕ :=
  let k := algorithmEightHistoryIndex setGen selection orders ρ xs
  setOutput setGen (prefixCompletion 0 xs) k

/-- Literal recursive Algorithm 8 output: the least available natural in
the selected past set. -/
noncomputable def algorithmEightOutput
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (t : ℕ) (xs : Fin t → ℕ) : ℕ := by
  classical
  let previous : Finset ℕ :=
    Finset.univ.image fun s : Fin t =>
      algorithmEightOutput setGen hinfinite selection orders ρ s
        (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)
  let forbidden := GenLimit.Generic.sequenceSample xs ∪ previous
  let A := algorithmEightChosenSet setGen selection orders ρ xs
  have hA : A.Infinite := by
    unfold A algorithmEightChosenSet
    exact hinfinite _ _
  have hexists : ∃ x, x ∈ A ∧ x ∉ forbidden := by
    by_contra hnot
    push_neg at hnot
    exact hA (forbidden.finite_toSet.subset hnot)
  exact Nat.find hexists
termination_by t
decreasing_by exact s.isLt

/-- Paper-level element generator obtained from Algorithm 8. -/
noncomputable def algorithmEightGenerator
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ) :
    GenLimit.Generic.Generator ℕ :=
  algorithmEightOutput setGen hinfinite selection orders ρ

theorem algorithmEightOutput_spec
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) {t : ℕ} (xs : Fin t → ℕ) :
    let output :=
      algorithmEightOutput setGen hinfinite selection orders ρ t xs
    output ∈ algorithmEightChosenSet
        setGen selection orders ρ xs ∧
      output ∉ GenLimit.Generic.sequenceSample xs ∧
      ∀ s : Fin t,
        output ≠ algorithmEightOutput
          setGen hinfinite selection orders ρ s
            (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩) := by
  classical
  let previous : Finset ℕ :=
    Finset.univ.image fun s : Fin t =>
      algorithmEightOutput setGen hinfinite selection orders ρ s
        (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)
  let forbidden := GenLimit.Generic.sequenceSample xs ∪ previous
  let A := algorithmEightChosenSet setGen selection orders ρ xs
  have hA : A.Infinite := by
    unfold A algorithmEightChosenSet
    exact hinfinite _ _
  have hexists : ∃ x, x ∈ A ∧ x ∉ forbidden := by
    by_contra hnot
    push_neg at hnot
    exact hA (forbidden.finite_toSet.subset hnot)
  have hspec := Nat.find_spec hexists
  have hout :
      algorithmEightOutput
          setGen hinfinite selection orders ρ t xs =
        Nat.find hexists := by
    rw [algorithmEightOutput]
  rw [hout]
  refine ⟨hspec.1, ?_, ?_⟩
  · intro hsample
    exact hspec.2 (Finset.mem_union_left _ hsample)
  · intro s heq
    exact hspec.2 (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, heq.symm⟩))

/-- The least-choice part of Algorithm 8. -/
theorem algorithmEightOutput_le_of_available
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) {t : ℕ} (xs : Fin t → ℕ) {y : ℕ}
    (hyA : y ∈ algorithmEightChosenSet
      setGen selection orders ρ xs)
    (hySample : y ∉ GenLimit.Generic.sequenceSample xs)
    (hyPrevious : ∀ s : Fin t,
      y ≠ algorithmEightOutput
        setGen hinfinite selection orders ρ s
          (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)) :
    algorithmEightOutput
        setGen hinfinite selection orders ρ t xs ≤ y := by
  classical
  let previous : Finset ℕ :=
    Finset.univ.image fun s : Fin t =>
      algorithmEightOutput setGen hinfinite selection orders ρ s
        (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)
  let forbidden := GenLimit.Generic.sequenceSample xs ∪ previous
  let A := algorithmEightChosenSet setGen selection orders ρ xs
  have hA : A.Infinite := by
    unfold A algorithmEightChosenSet
    exact hinfinite _ _
  have hexists : ∃ x, x ∈ A ∧ x ∉ forbidden := by
    by_contra hnot
    push_neg at hnot
    exact hA (forbidden.finite_toSet.subset hnot)
  have hy : y ∈ A ∧ y ∉ forbidden := by
    refine ⟨hyA, ?_⟩
    intro hyForbidden
    rcases Finset.mem_union.mp hyForbidden with hsample | hprevious
    · exact hySample hsample
    · obtain ⟨s, _hs, heq⟩ := Finset.mem_image.mp hprevious
      exact hyPrevious s heq.symm
  have hout :
      algorithmEightOutput
          setGen hinfinite selection orders ρ t xs =
        Nat.find hexists := by
    rw [algorithmEightOutput]
  rw [hout]
  exact Nat.find_min' hexists hy

/-! ## The finite counting core of Claim 6.17 -/

theorem canonicalRank_carrier_le_of_le_enumeration
    (K : OrderedLanguage) (horder : InheritsAmbientOrder K)
    {x i : ℕ} (hx : x ∈ K.carrier)
    (hxi : x ≤ K.enumeration i) :
    canonicalRank K K.carrier x ≤ i + 1 := by
  rw [canonicalRank_carrier K hx]
  apply Nat.add_le_add_right
  rw [← horder.le_iff_le]
  simpa [enumeration_canonicalIndex K hx] using hxi

theorem exists_available_in_ordered_prefix
    (K : OrderedLanguage) (A : Set ℕ)
    (forbidden : Finset ℕ) (m : ℕ)
    (hcount : forbidden.card < K.prefixCount A m) :
    ∃ i, i < m ∧ K.enumeration i ∈ A ∧
      K.enumeration i ∉ forbidden := by
  classical
  let indices :=
    (Finset.range m).filter fun i => K.enumeration i ∈ A
  let values := indices.image K.enumeration
  have hcard : values.card = K.prefixCount A m := by
    rw [Finset.card_image_of_injective _ K.enumeration_injective]
    rfl
  obtain ⟨y, hyValues, hyForbidden⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (show forbidden.card < values.card by simpa [hcard] using hcount)
  obtain ⟨i, hiIndices, hiy⟩ := Finset.mem_image.mp hyValues
  refine ⟨i, ?_, ?_, ?_⟩
  · exact Finset.mem_range.mp (Finset.mem_filter.mp hiIndices).1
  · exact (Finset.mem_filter.mp hiIndices).2
  · simpa [hiy] using hyForbidden

/-- If the chosen set has more low-rank candidates than the input sample
and all previous outputs combined, the least available output lies in that
ordered prefix. -/
theorem algorithmEightOutput_rank_le_of_prefixCount
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (K : OrderedLanguage)
    (horder : InheritsAmbientOrder K)
    {t m : ℕ} (xs : Fin t → ℕ)
    (hsubset : algorithmEightChosenSet
        setGen selection orders ρ xs ⊆ K.carrier)
    (hcount : 2 * t < K.prefixCount
      (algorithmEightChosenSet setGen selection orders ρ xs) m) :
    canonicalRank K K.carrier
        (algorithmEightOutput
          setGen hinfinite selection orders ρ t xs) ≤ m := by
  classical
  letI : DecidableEq ℕ := Classical.decEq ℕ
  let previous : Finset ℕ :=
    Finset.univ.image fun s : Fin t =>
      algorithmEightOutput setGen hinfinite selection orders ρ s
        (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)
  let forbidden := GenLimit.Generic.sequenceSample xs ∪ previous
  have hsampleCard :
      (GenLimit.Generic.sequenceSample xs).card ≤ t := by
    rw [GenLimit.Generic.sequenceSample]
    exact (Finset.card_image_le.trans_eq (by simp))
  have hpreviousCard : previous.card ≤ t := by
    dsimp [previous]
    calc
      (Finset.univ.image fun s : Fin t =>
          algorithmEightOutput setGen hinfinite selection orders ρ s
            (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)).card ≤
          Finset.univ.card := Finset.card_image_le
      _ = t := by simp
  have hforbiddenCard : forbidden.card ≤ 2 * t := by
    calc
      forbidden.card ≤
          (GenLimit.Generic.sequenceSample xs).card + previous.card :=
        Finset.card_union_le _ _
      _ ≤ t + t := Nat.add_le_add hsampleCard hpreviousCard
      _ = 2 * t := by omega
  obtain ⟨i, him, hiA, hiForbidden⟩ :=
    exists_available_in_ordered_prefix K
      (algorithmEightChosenSet setGen selection orders ρ xs)
      forbidden m (hforbiddenCard.trans_lt hcount)
  have hiSample :
      K.enumeration i ∉ GenLimit.Generic.sequenceSample xs := by
    intro hi
    exact hiForbidden (Finset.mem_union_left _ hi)
  have hiPrevious : ∀ s : Fin t,
      K.enumeration i ≠
        algorithmEightOutput setGen hinfinite selection orders ρ s
          (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩) := by
    intro s heq
    exact hiForbidden (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, heq.symm⟩))
  have houtLe := algorithmEightOutput_le_of_available
    setGen hinfinite selection orders ρ xs hiA hiSample hiPrevious
  have houtMem := hsubset
    (algorithmEightOutput_spec
      setGen hinfinite selection orders ρ xs).1
  exact (canonicalRank_carrier_le_of_le_enumeration
    K horder houtMem houtLe).trans (by omega)

/-- The target prefix length appearing in Claim 6.17, with Lean's
zero-based round `t` corresponding to the paper's round `t + 1`. -/
noncomputable def algorithmEightRankCutoff
    (ρ : ℝ) (stage t : ℕ) : ℕ :=
  ⌈(2 : ℝ) * (t + 1 : ℕ) * densitySlack stage / ρ⌉₊

/-- Admissibility plus the selected target's density guarantee supplies
twice as many low-rank candidates as the current round needs. -/
theorem algorithmEight_prefixCount_rankCutoff
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (hρ : 0 < ρ)
    (stream : GenLimit.Generic.Stream ℕ)
    {target stage t : ℕ}
    (hselected : target ∈ selection stage (fun i => stream i))
    (hdensity : ρ ≤
      (orders target).lowerDensity (setOutput setGen stream stage))
    (hbudget : AlgorithmEightBudget
      setGen selection orders ρ stream stage t) :
    2 * (t + 1) ≤
      (orders target).prefixCount (setOutput setGen stream stage)
        (algorithmEightRankCutoff ρ stage t) := by
  let slack := densitySlack stage
  let m := algorithmEightRankCutoff ρ stage t
  have hslack : 0 < slack := densitySlack_pos stage
  have hscale : 0 < ρ / slack := div_pos hρ hslack
  have hmReal :
      (2 : ℝ) * (t + 1 : ℕ) * slack / ρ ≤ (m : ℝ) := by
    exact Nat.le_ceil _
  have hmpos : 0 < m := by
    dsimp [m, algorithmEightRankCutoff]
    rw [Nat.ceil_pos]
    positivity
  have hcutoffReal :
      (algorithmEightStageCutoff
          setGen selection orders stream stage : ℝ) ≤ m := by
    have hmul := (div_le_iff₀ hslack).mp hbudget
    calc
      (algorithmEightStageCutoff
          setGen selection orders stream stage : ℝ)
          ≤ (2 * (t + 1 : ℕ) / ρ) * slack := hmul
      _ = (2 : ℝ) * (t + 1 : ℕ) * slack / ρ := by ring
      _ ≤ m := hmReal
  have hcutoff :
      algorithmEightStageCutoff
          setGen selection orders stream stage ≤ m := by
    exact_mod_cast hcutoffReal
  have hratio := finiteDensityCutoff_spec orders
    (selection stage (fun i => stream i))
    (setOutput setGen stream stage) stage hselected hcutoff
  have hρratio :
      ρ / slack ≤
        (orders target).prefixRatio
          (setOutput setGen stream stage) m :=
    (div_le_div_iff_of_pos_right hslack).mpr hdensity |>.trans hratio
  have hscaledCount :
      (ρ / slack) * (m : ℝ) ≤
        (orders target).prefixCount (setOutput setGen stream stage) m := by
    simp only [OrderedLanguage.prefixRatio, if_neg hmpos.ne'] at hρratio
    exact (le_div_iff₀ (by exact_mod_cast hmpos)).mp hρratio
  have hneeded :
      (2 * (t + 1) : ℕ) ≤
        (orders target).prefixCount (setOutput setGen stream stage) m := by
    have hscaled := mul_le_mul_of_nonneg_left hmReal hscale.le
    have hleft :
        (ρ / slack) *
            ((2 : ℝ) * (t + 1 : ℕ) * slack / ρ) =
          (2 : ℝ) * (t + 1 : ℕ) := by
      field_simp [hρ.ne', hslack.ne']
    have hreal :
        (2 : ℝ) * (t + 1 : ℕ) ≤
          (orders target).prefixCount
            (setOutput setGen stream stage) m := by
      rw [hleft] at hscaled
      exact hscaled.trans hscaledCount
    exact_mod_cast hreal
  simpa [m] using hneeded

/-- On an actual run, the finite-history chosen set is exactly the set
generator's output at the selected past stage. -/
theorem algorithmEightChosenSet_eq_stream
    (setGen : SetGenerator ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    algorithmEightChosenSet setGen selection orders ρ
        (fun i : Fin t => stream i) =
      setOutput setGen stream
        (algorithmEightIndexOn
          setGen selection orders ρ stream t) := by
  unfold algorithmEightChosenSet
  rw [algorithmEightHistoryIndex_eq_stream]
  unfold setOutput
  apply congrArg (setGen _)
  funext i
  exact prefixCompletion_eq 0 _
    (i.isLt.trans_le
      (algorithmEightIndexOn_le
        setGen selection orders ρ stream t))

/-- Algorithm 8 always avoids the current sample and all previous outputs. -/
theorem algorithmEightGenerator_fresh_every_round
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    GenLimit.Generic.output
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ) stream t ∉
      GenLimit.Generic.sample stream t ∧
    GenLimit.Generic.output
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ) stream t ∉
      generatedBefore
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ) stream t := by
  let xs : Fin t → ℕ := fun i => stream i
  have hspec := algorithmEightOutput_spec
    setGen hinfinite selection orders ρ xs
  change
    algorithmEightOutput
        setGen hinfinite selection orders ρ t xs ∉
        GenLimit.Generic.sample stream t ∧
      algorithmEightOutput
        setGen hinfinite selection orders ρ t xs ∉
        generatedBefore
          (algorithmEightGenerator
            setGen hinfinite selection orders ρ) stream t
  constructor
  · rw [← GenLimit.Generic.sequenceSample_prefix stream t]
    exact hspec.2.1
  · rw [mem_generatedBefore_iff]
    rintro ⟨s, hst, heq⟩
    let sf : Fin t := ⟨s, hst⟩
    apply hspec.2.2 sf
    simpa [xs, sf, algorithmEightGenerator] using heq.symm

theorem algorithmEightOutputStream_injective
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (stream : GenLimit.Generic.Stream ℕ) :
    Function.Injective
      (elementOutputStream
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ) stream) := by
  apply elementOutputStream_injective_of_fresh
  intro t
  exact (algorithmEightGenerator_fresh_every_round
    setGen hinfinite selection orders ρ stream t).2

/-! ## Eventual validity -/

/-- Structural hypothesis on the set algorithm used by Theorem 6.15: its
output lies in the selected common core and avoids its own input prefix. -/
def SetCoreSelectionInvariant
    (setGen : SetGenerator ℕ)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ) : Prop :=
  ∀ t xs,
    setGen t xs ⊆
      finiteCommonCore
          (indexedLanguages family (selection t xs)) \
        (↑(GenLimit.Generic.sequenceSample xs) : Set ℕ)

/-- The chosen past stage eventually contains the target, so Algorithm 8 is
eventually target-valid and fresh. -/
theorem algorithmEight_generates_of_eventually_selected
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (target : ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i)) :
    GeneratesElementInLimitOn
      (algorithmEightGenerator
        setGen hinfinite selection orders ρ)
      (family target) stream := by
  classical
  obtain ⟨N, hN⟩ := hselected
  have hindex := tendsto_algorithmEightIndexOn_atTop
    setGen selection orders ρ hρ stream
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hindex.eventually (eventually_ge_atTop N))
  refine ⟨T, ?_⟩
  intro t ht
  let k := algorithmEightIndexOn
    setGen selection orders ρ stream t
  have hkN : N ≤ k := hT t ht
  have hkt : k ≤ t := algorithmEightIndexOn_le
    setGen selection orders ρ stream t
  have htarget : target ∈ selection k (fun i => stream i) :=
    hN k hkN
  let xs : Fin t → ℕ := fun i => stream i
  have hspec := algorithmEightOutput_spec
    setGen hinfinite selection orders ρ xs
  have hchosen :
      algorithmEightChosenSet setGen selection orders ρ xs =
        setOutput setGen stream k := by
    simpa [xs, k] using algorithmEightChosenSet_eq_stream
      setGen selection orders ρ stream t
  have houtSet :
      algorithmEightOutput
          setGen hinfinite selection orders ρ t xs ∈
        setOutput setGen stream k := by
    rw [← hchosen]
    exact hspec.1
  have hcore := hinvariant k (fun i : Fin k => stream i) houtSet
  have hvalid :
      algorithmEightOutput
          setGen hinfinite selection orders ρ t xs ∈
        family target := by
    exact finiteCommonCore_subset_of_mem
      (Finset.mem_image.mpr ⟨target, htarget, rfl⟩) hcore.1
  have hfresh := algorithmEightGenerator_fresh_every_round
    setGen hinfinite selection orders ρ stream t
  exact ⟨hvalid, hfresh.1, hfresh.2⟩

/-! ## Claim 6.17 and Theorem 6.15 -/

/-- Claim 6.17 for the literal Algorithm 8 implementation. -/
theorem claim_6_17_algorithmEight_rank
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (target : ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i))
    (hdensity : ∃ N, ∀ t, N ≤ t →
      ρ ≤ (orders target).lowerDensity (setOutput setGen stream t)) :
    ∃ N, ∀ t, N ≤ t →
      canonicalRank (orders target) (orders target).carrier
          (elementOutputStream
            (algorithmEightGenerator
              setGen hinfinite selection orders ρ) stream t) ≤
        algorithmEightRankCutoff ρ
          (algorithmEightIndexOn
            setGen selection orders ρ stream t) t := by
  classical
  obtain ⟨Nselected, hNselected⟩ := hselected
  obtain ⟨Ndensity, hNdensity⟩ := hdensity
  let N := max (max Nselected Ndensity) 1
  have hindex := tendsto_algorithmEightIndexOn_atTop
    setGen selection orders ρ hρ stream
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hindex.eventually (eventually_ge_atTop N))
  refine ⟨T, ?_⟩
  intro t ht
  let k := algorithmEightIndexOn
    setGen selection orders ρ stream t
  have hkN : N ≤ k := hT t ht
  have hkSelected : Nselected ≤ k :=
    (Nat.le_max_left Nselected Ndensity).trans
      (Nat.le_max_left (max Nselected Ndensity) 1) |>.trans hkN
  have hkDensity : Ndensity ≤ k :=
    (Nat.le_max_right Nselected Ndensity).trans
      (Nat.le_max_left (max Nselected Ndensity) 1) |>.trans hkN
  have hkPositive : 0 < k := by
    have : 1 ≤ k :=
      (Nat.le_max_right (max Nselected Ndensity) 1).trans hkN
    omega
  have htarget : target ∈ selection k (fun i => stream i) :=
    hNselected k hkSelected
  have hdense :
      ρ ≤ (orders target).lowerDensity (setOutput setGen stream k) :=
    hNdensity k hkDensity
  have hbudget : AlgorithmEightBudget
      setGen selection orders ρ stream k t := by
    rcases algorithmEightIndexOn_admissible
      setGen selection orders ρ stream t with hkzero | hbudget
    · exact False.elim (hkPositive.ne' hkzero)
    · exact hbudget
  let xs : Fin t → ℕ := fun i => stream i
  have hchosen :
      algorithmEightChosenSet setGen selection orders ρ xs =
        setOutput setGen stream k := by
    simpa [xs, k] using algorithmEightChosenSet_eq_stream
      setGen selection orders ρ stream t
  have hsubset :
      algorithmEightChosenSet setGen selection orders ρ xs ⊆
        (orders target).carrier := by
    rw [hchosen]
    intro x hx
    have hcore := hinvariant k (fun i : Fin k => stream i) hx
    rw [hcarrier target]
    exact finiteCommonCore_subset_of_mem
      (Finset.mem_image.mpr ⟨target, htarget, rfl⟩) hcore.1
  have hcount :
      2 * (t + 1) ≤
        (orders target).prefixCount (setOutput setGen stream k)
          (algorithmEightRankCutoff ρ k t) :=
    algorithmEight_prefixCount_rankCutoff
      setGen selection orders ρ hρ stream htarget hdense hbudget
  change
    canonicalRank (orders target) (orders target).carrier
        (algorithmEightOutput
          setGen hinfinite selection orders ρ t xs) ≤
      algorithmEightRankCutoff ρ k t
  apply algorithmEightOutput_rank_le_of_prefixCount
    setGen hinfinite selection orders ρ (orders target)
      (horder target) xs hsubset
  rw [hchosen]
  omega

/-- The analytic consequence of Claim 6.17: since the selected stages tend
to infinity, its rank cutoffs have asymptotic slope at most `2 / ρ`. -/
theorem claim_6_17_implies_asymptoticDisplacement
    (K : OrderedLanguage)
    (output : GenLimit.Generic.Stream ℕ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (stage : ℕ → ℕ)
    (hstage : Tendsto stage atTop atTop)
    (hclaim : ∃ N, ∀ t, N ≤ t →
      canonicalRank K K.carrier (output t) ≤
        algorithmEightRankCutoff ρ (stage t) t) :
    AsymptoticDisplacementAtMost K output (2 / ρ) := by
  have hslack :
      Tendsto (fun t => densitySlack (stage t)) atTop (nhds 1) :=
    tendsto_densitySlack_atTop.comp hstage
  have hmain :
      Tendsto
        (fun t : ℕ =>
          (2 : ℝ) * densitySlack (stage t) / ρ +
            1 / (t + 1 : ℕ))
        atTop (nhds (2 / ρ)) := by
    have hfirst :
        Tendsto
          (fun t : ℕ => (2 : ℝ) * densitySlack (stage t) / ρ)
          atTop (nhds (2 / ρ)) := by
      simpa using (tendsto_const_nhds.mul hslack).div_const ρ
    simpa using hfirst.add tendsto_one_div_add_atTop_nhds_zero_nat
  intro M hM
  obtain ⟨Nclaim, hNclaim⟩ := hclaim
  have heventually :
      ∀ᶠ t : ℕ in atTop,
        (2 : ℝ) * densitySlack (stage t) / ρ +
            1 / (t + 1 : ℕ) < M :=
    (tendsto_order.1 hmain).2 M hM
  obtain ⟨Nbound, hNbound⟩ := eventually_atTop.mp heventually
  refine ⟨max Nclaim Nbound, ?_⟩
  intro t ht
  have htClaim : Nclaim ≤ t :=
    (Nat.le_max_left Nclaim Nbound).trans ht
  have htBound : Nbound ≤ t :=
    (Nat.le_max_right Nclaim Nbound).trans ht
  have hrank := hNclaim t htClaim
  have hceil :
      (algorithmEightRankCutoff ρ (stage t) t : ℝ) <
        (2 : ℝ) * (t + 1 : ℕ) * densitySlack (stage t) / ρ + 1 := by
    unfold algorithmEightRankCutoff
    apply Nat.ceil_lt_add_one
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (by positivity))
        (densitySlack_pos _).le)
      hρ.le
  have hfactor :
      (2 : ℝ) * (t + 1 : ℕ) * densitySlack (stage t) / ρ + 1 =
        ((2 : ℝ) * densitySlack (stage t) / ρ +
          1 / (t + 1 : ℕ)) * (t + 1 : ℕ) := by
    have htpos : (0 : ℝ) < (t + 1 : ℕ) := by positivity
    field_simp [hρ.ne', htpos.ne']
  calc
    (canonicalRank K K.carrier (output t) : ℝ)
        ≤ algorithmEightRankCutoff ρ (stage t) t := by
          exact_mod_cast hrank
    _ ≤ (2 : ℝ) * (t + 1 : ℕ) *
          densitySlack (stage t) / ρ + 1 := hceil.le
    _ = ((2 : ℝ) * densitySlack (stage t) / ρ +
          1 / (t + 1 : ℕ)) * (t + 1 : ℕ) := hfactor
    _ ≤ M * (t + 1) := by
      have htNonneg : (0 : ℝ) ≤ (t + 1 : ℕ) := by positivity
      simpa only [Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonneg_right (hNbound t htBound).le htNonneg

/-- Theorem 6.15: the literal Algorithm 8 converts an eventually
`ρ`-dense set generator satisfying the selected-core interface into a fresh
element generator of lower density at least `ρ / 2`. -/
theorem theorem_6_15_algorithmEight
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (target : ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i))
    (hdensity : ∃ N, ∀ t, N ≤ t →
      ρ ≤ (orders target).lowerDensity (setOutput setGen stream t)) :
    GeneratesElementInLimitOn
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ)
        (family target) stream ∧
      ρ / 2 ≤ elementBasedLowerDensity
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ)
        (orders target) stream := by
  let gen := algorithmEightGenerator
    setGen hinfinite selection orders ρ
  have hgenerates : GeneratesElementInLimitOn gen (family target) stream :=
    algorithmEight_generates_of_eventually_selected
      setGen hinfinite family selection orders ρ hρ hinvariant
      target stream hselected
  refine ⟨hgenerates, ?_⟩
  have hinjective :
      Function.Injective (elementOutputStream gen stream) :=
    algorithmEightOutputStream_injective
      setGen hinfinite selection orders ρ stream
  have heventually :
      ∃ N, ∀ n, N ≤ n →
        elementOutputStream gen stream n ∈ (orders target).carrier := by
    obtain ⟨N, hN⟩ := hgenerates
    refine ⟨N, ?_⟩
    intro n hn
    rw [hcarrier target]
    exact (hN n hn).1
  have hclaim := claim_6_17_algorithmEight_rank
    setGen hinfinite family selection orders ρ hρ hinvariant
    hcarrier horder target stream hselected hdensity
  have hdisplacement :
      AsymptoticDisplacementAtMost
        (orders target) (elementOutputStream gen stream) (2 / ρ) :=
    claim_6_17_implies_asymptoticDisplacement
      (orders target) (elementOutputStream gen stream) ρ hρ
      (algorithmEightIndexOn setGen selection orders ρ stream)
      (tendsto_algorithmEightIndexOn_atTop
        setGen selection orders ρ hρ stream)
      hclaim
  change ρ / 2 ≤
    (orders target).lowerDensity
      (Set.range (elementOutputStream gen stream))
  exact theorem_6_15_density_endgame
    (orders target) (elementOutputStream gen stream) ρ hρ
    hinjective heventually hdisplacement

/-- Corollary 6.16 in its nontrivial range `0 < ρ - ε`: a set-based
`liminf` guarantee supplies the eventual pointwise premise of Theorem 6.15. -/
theorem corollary_6_16_algorithmEight
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ ε : ℝ) (hε : 0 < ε) (hρε : 0 < ρ - ε)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (target : ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i))
    (hsetDensity : ρ ≤
      setBasedLowerDensity setGen (orders target) stream) :
    GeneratesElementInLimitOn
        (algorithmEightGenerator
          setGen hinfinite selection orders (ρ - ε))
        (family target) stream ∧
      (ρ - ε) / 2 ≤ elementBasedLowerDensity
        (algorithmEightGenerator
          setGen hinfinite selection orders (ρ - ε))
        (orders target) stream := by
  have hlt :
      ρ - ε <
        liminf
          (fun t => (orders target).lowerDensity
            (setOutput setGen stream t)) atTop := by
    exact (sub_lt_self ρ hε).trans_le hsetDensity
  have heventually :
      ∀ᶠ t : ℕ in atTop,
        ρ - ε < (orders target).lowerDensity
          (setOutput setGen stream t) :=
    eventually_lt_of_lt_liminf hlt
      (isBoundedUnder_of
        ⟨0, fun t =>
          (orders target).lowerDensity_nonneg
            (setOutput setGen stream t)⟩)
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
  exact theorem_6_15_algorithmEight
    setGen hinfinite family selection orders (ρ - ε) hρε
    hinvariant hcarrier horder target stream hselected
    ⟨N, fun t ht => (hN t ht).le⟩

/-- Corollary 6.16 for every `ε > 0`.  When `ρ - ε` is positive this is
the quantitative Algorithm 8 construction above.  Otherwise the requested
density lower bound is nonpositive, so any positive Algorithm 8 budget gives
generation and ordered-density nonnegativity closes the bound. -/
theorem corollary_6_16
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ ε : ℝ) (hε : 0 < ε)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (target : ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i))
    (hsetDensity : ρ ≤
      setBasedLowerDensity setGen (orders target) stream) :
    ∃ gen : GenLimit.Generic.Generator ℕ,
      GeneratesElementInLimitOn gen (family target) stream ∧
        (ρ - ε) / 2 ≤
          elementBasedLowerDensity gen (orders target) stream := by
  by_cases hρε : 0 < ρ - ε
  · let gen := algorithmEightGenerator
      setGen hinfinite selection orders (ρ - ε)
    exact ⟨gen, corollary_6_16_algorithmEight
      setGen hinfinite family selection orders ρ ε hε hρε
      hinvariant hcarrier horder target stream hselected hsetDensity⟩
  · let gen := algorithmEightGenerator
      setGen hinfinite selection orders 1
    refine ⟨gen, ?_, ?_⟩
    · exact algorithmEight_generates_of_eventually_selected
        setGen hinfinite family selection orders 1 (by norm_num)
        hinvariant target stream hselected
    · have hnonneg : 0 ≤
          elementBasedLowerDensity gen (orders target) stream :=
        (orders target).lowerDensity_nonneg _
      have hleft : (ρ - ε) / 2 ≤ 0 := by
        have : ρ - ε ≤ 0 := le_of_not_gt hρε
        linarith
      exact hleft.trans hnonneg

end GenLimit.InfiniteContamination
