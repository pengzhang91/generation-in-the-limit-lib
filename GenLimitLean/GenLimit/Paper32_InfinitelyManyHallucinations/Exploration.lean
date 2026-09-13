import GenLimit.Paper32_InfinitelyManyHallucinations.Definitions
import GenLimit.Support.Asymptotics.SparseSquares
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Sparse exploration schedules

This module supplies the construction asserted after Definition 4.2.  We use
the quadratic schedule

`spacing * (k + 1)^2`, `k = 0, 1, ...`,

instead of the paper's exponentially sparse example.  Quadratic sparsity is
enough for every argument in the paper, while its prefix count has the simple
checked bound `Nat.sqrt m`.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

/-- A concrete family of increasingly sparse exploration times. -/
def quadraticTime (spacing k : ℕ) : ℕ :=
  spacing * (k + 1) ^ 2

/-- The corresponding set of exploration rounds. -/
def quadraticCarrier (spacing : ℕ) : Set ℕ :=
  Set.range (quadraticTime spacing)

theorem quadraticTime_injective {spacing : ℕ} (hspacing : 0 < spacing) :
    Function.Injective (quadraticTime spacing) := by
  intro a b hab
  have hsquares : (a + 1) ^ 2 = (b + 1) ^ 2 := by
    exact Nat.eq_of_mul_eq_mul_left hspacing hab
  nlinarith

theorem quadraticCarrier_infinite {spacing : ℕ} (hspacing : 0 < spacing) :
    (quadraticCarrier spacing).Infinite := by
  exact Set.infinite_range_of_injective
    (quadraticTime_injective hspacing)

theorem spacing_dvd_of_mem_quadraticCarrier
    {spacing n : ℕ} (hn : n ∈ quadraticCarrier spacing) :
    spacing ∣ n := by
  rcases hn with ⟨k, rfl⟩
  exact dvd_mul_right spacing ((k + 1) ^ 2)

theorem quadraticCarrier_one_not_mem
    {spacing : ℕ} (hspacing : 2 ≤ spacing) :
    1 ∉ quadraticCarrier spacing := by
  intro hone
  have hdvd : spacing ∣ 1 :=
    spacing_dvd_of_mem_quadraticCarrier hone
  have : spacing = 1 := Nat.dvd_one.mp hdvd
  omega

theorem quadraticCarrier_nonconsecutive
    {spacing : ℕ} (hspacing : 2 ≤ spacing) :
    ∀ n, n ∈ quadraticCarrier spacing → n + 1 ∉ quadraticCarrier spacing := by
  intro n hn hn1
  have hnDvd : spacing ∣ n :=
    spacing_dvd_of_mem_quadraticCarrier hn
  have hn1Dvd : spacing ∣ n + 1 :=
    spacing_dvd_of_mem_quadraticCarrier hn1
  have hnMod : n % spacing = 0 := Nat.mod_eq_zero_of_dvd hnDvd
  have hn1Mod : (n + 1) % spacing = 0 :=
    Nat.mod_eq_zero_of_dvd hn1Dvd
  have honeMod : (n + 1) % spacing = 1 := by
    rw [Nat.add_mod, hnMod]
    simp [Nat.mod_eq_of_lt (show 1 < spacing by omega)]
  omega

/-- Every quadratic exploration time at most `m` has an index below
`Nat.sqrt m`. -/
theorem quadratic_index_lt_sqrt
    {spacing k m : ℕ} (hspacing : 0 < spacing)
    (hkm : quadraticTime spacing k ≤ m) :
    k < Nat.sqrt m := by
  have hsquare : (k + 1) ^ 2 ≤ m := by
    exact le_trans
      (Nat.le_mul_of_pos_left ((k + 1) ^ 2) hspacing)
      hkm
  have := (Nat.le_sqrt' (m := k + 1) (n := m)).2 hsquare
  omega

/-- The number of quadratic exploration times through `m` is at most
`Nat.sqrt m`. -/
theorem explorationCount_quadraticCarrier_le_sqrt
    {spacing : ℕ} (hspacing : 0 < spacing) (m : ℕ) :
    explorationCount (quadraticCarrier spacing) m ≤ Nat.sqrt m := by
  classical
  unfold explorationCount
  let present :=
    (Finset.Icc 1 m).filter
      (fun n => n ∈ quadraticCarrier spacing)
  have hpresent :
      present ⊆
        (Finset.range (Nat.sqrt m)).image (quadraticTime spacing) := by
    intro n hn
    have hnle : n ≤ m := by
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have hncarrier : n ∈ quadraticCarrier spacing :=
      (Finset.mem_filter.mp hn).2
    rcases hncarrier with ⟨k, rfl⟩
    exact Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr
        (quadratic_index_lt_sqrt hspacing hnle), rfl⟩
  calc
    present.card ≤
        ((Finset.range (Nat.sqrt m)).image
          (quadraticTime spacing)).card :=
      Finset.card_le_card hpresent
    _ ≤ (Finset.range (Nat.sqrt m)).card := Finset.card_image_le
    _ = Nat.sqrt m := Finset.card_range _

theorem tendsto_natSqrt_atTop :
    Tendsto Nat.sqrt atTop atTop :=
  SparseSquares.natSqrt_tendsto_atTop

theorem tendsto_natSqrt_div_self_zero :
    Tendsto (fun m : ℕ => (Nat.sqrt m : ℝ) / (m : ℝ))
      atTop (nhds 0) :=
  SparseSquares.natSqrt_div_self_tendsto_zero

theorem quadratic_prefixRatio_tendsto_zero
    {spacing : ℕ} (hspacing : 0 < spacing) :
    Tendsto
      (fun m =>
        ((explorationCount (quadraticCarrier spacing) m : ℝ) /
          (m : ℝ)))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun m => by positivity
  · exact Eventually.of_forall fun m => by
      have hcast :
          (explorationCount (quadraticCarrier spacing) m : ℝ) ≤
            (Nat.sqrt m : ℝ) := by
        exact_mod_cast
          explorationCount_quadraticCarrier_le_sqrt hspacing m
      exact div_le_div_of_nonneg_right
        hcast
        (by positivity)
  · exact tendsto_natSqrt_div_self_zero

/-- A concrete exploration set, proving Definition 4.1 is inhabited. -/
def quadraticExplorationSet (spacing : ℕ) (hspacing : 2 ≤ spacing) :
    ExplorationSet where
  carrier := quadraticCarrier spacing
  infinite' := quadraticCarrier_infinite (lt_of_lt_of_le (by decide) hspacing)
  one_not_mem := quadraticCarrier_one_not_mem hspacing
  nonconsecutive := quadraticCarrier_nonconsecutive hspacing
  prefixRatio_tendsto_zero :=
    quadratic_prefixRatio_tendsto_zero (lt_of_lt_of_le (by decide) hspacing)

theorem explorationCount_quadraticCarrier_eq_zero_of_lt_spacing
    {spacing m : ℕ} (hm : m < spacing) :
    explorationCount (quadraticCarrier spacing) m = 0 := by
  classical
  unfold explorationCount
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro n hnrange hncarrier
  rcases hncarrier with ⟨k, rfl⟩
  have htimeLe : quadraticTime spacing k ≤ m := by
    exact (Finset.mem_Icc.mp hnrange).2
  have hspacingLe : spacing ≤ quadraticTime spacing k := by
    unfold quadraticTime
    exact Nat.le_mul_of_pos_right spacing (by positivity)
  omega

/-- Appendix Lemma (existence of `γ`-admissible exploration sets), in a
slightly stronger form that needs only `γ < 1`; the main paper later also
assumes `0 ≤ γ`. -/
theorem exists_gammaAdmissible_explorationSet
    {γ : ℝ} (hγ : γ < 1) :
    ∃ E : ExplorationSet, E.GammaAdmissible γ := by
  have hdelta : 0 < 1 - γ := sub_pos.mpr hγ
  have heventually :
      ∀ᶠ m : ℕ in atTop,
        (Nat.sqrt m : ℝ) / (m : ℝ) < 1 - γ :=
    (tendsto_order.1 tendsto_natSqrt_div_self_zero).2
      (1 - γ) hdelta
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  let spacing := N + 2
  have hspacing : 2 ≤ spacing := by
    simp [spacing]
  refine ⟨quadraticExplorationSet spacing hspacing, ?_⟩
  intro m
  change
    (explorationCount (quadraticCarrier spacing) m : ℝ) ≤
      (1 - γ) * (m : ℝ)
  by_cases hmzero : m = 0
  · subst m
    simp [explorationCount]
  by_cases hm : N ≤ m
  · have hcountCast :
        (explorationCount (quadraticCarrier spacing) m : ℝ) ≤
          (Nat.sqrt m : ℝ) := by
      exact_mod_cast explorationCount_quadraticCarrier_le_sqrt
        (show 0 < spacing by omega) m
    have hdenom : (0 : ℝ) < m := by
      exact_mod_cast Nat.pos_of_ne_zero hmzero
    have hratio :
        (explorationCount (quadraticCarrier spacing) m : ℝ) /
            (m : ℝ) < 1 - γ :=
      lt_of_le_of_lt
        (div_le_div_of_nonneg_right hcountCast hdenom.le)
        (hN m hm)
    have hmul :
        (explorationCount (quadraticCarrier spacing) m : ℝ) <
          (1 - γ) * (m : ℝ) :=
      (div_lt_iff₀ hdenom).mp hratio
    exact hmul.le
  · have hmLt : m < spacing := by
      simp only [spacing]
      omega
    rw [explorationCount_quadraticCarrier_eq_zero_of_lt_spacing hmLt]
    norm_num only [Nat.cast_zero]
    exact mul_nonneg hdelta.le (Nat.cast_nonneg m)

end GenLimit.InfinitelyManyHallucinations
