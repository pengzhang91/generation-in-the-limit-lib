import GenLimit.NoRegretLanguageGeneration.AnytimeRealizable
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

namespace PredictionToGeneration

/-- The arithmetic criterion is exactly Mathlib's real-valued little-o relation. -/
theorem natSublinear_iff_isLittleO (f : Nat → Nat) :
    NatSublinear f ↔ (fun t : Nat => (f t : ℝ)) =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro hf c hc
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
    obtain ⟨N, hN⟩ := hf (n + 1)
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro t ht
    have hb : (n + 1 : ℝ) * (f t : ℝ) ≤ (t : ℝ) := by exact_mod_cast hN t ht
    have hp : (0 : ℝ) < n + 1 := by positivity
    have hd : (f t : ℝ) ≤ (t : ℝ) / (n + 1) := (le_div_iff₀ hp).mpr (by nlinarith [hb])
    simp only [Real.norm_natCast]
    calc
      (f t : ℝ) ≤ (t : ℝ) / (n + 1) := hd
      _ = (1 / (n + 1)) * (t : ℝ) := by ring
      _ ≤ c * (t : ℝ) := mul_le_mul_of_nonneg_right (le_of_lt hn) (by positivity)
  · intro hf k
    by_cases hk : k = 0
    · subst k; exact ⟨0, by simp⟩
    have hp : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hf (one_div_pos.mpr hp))
    refine ⟨N, ?_⟩
    intro t ht
    have hb := hN t ht
    simp only [Real.norm_natCast] at hb
    have hd : (f t : ℝ) ≤ (t : ℝ) / k := by simpa [div_eq_mul_inv, mul_comm] using hb
    have hm := (le_div_iff₀ hp).mp hd
    exact_mod_cast (show (k : ℝ) * (f t : ℝ) ≤ (t : ℝ) by nlinarith [hm])

theorem realizable_no_regret_iff_isLittleO (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) :
    RealizableNoRegret H ↔
      (fun t : Nat => (MF H t : ℝ)) =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  rw [realizable_no_regret_iff_sublinear H hu hne, natSublinear_iff_isLittleO]

/-- Flooring a real envelope preserves the integer bounds, so the exact factor
four is unchanged for the manuscript's real-valued envelopes. -/
theorem horizon_to_anytime_real (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (b : Nat → ℝ) (hmono : Monotone b)
    (hunbounded : ∀ c : ℝ, ∃ t, c < b t)
    (hpositive : ∀ t, 1 ≤ t → 1 ≤ b t)
    (hbound : ∀ t, 1 ≤ t → (MF H t : ℝ) ≤ b t) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → 1 ≤ xs.length →
      ∀ h, H h → Realizes h (G.play xs) →
        (mistakes h (G.play xs) : ℝ) ≤ 4 * b xs.length := by
  have hm : ∀ i j, i ≤ j → Nat.floor (b i) ≤ Nat.floor (b j) :=
    fun i j hij => Nat.floor_mono (hmono hij)
  have hu' : ∀ c : Nat, ∃ t, c < Nat.floor (b t) := by
    intro c
    obtain ⟨t, ht⟩ := hunbounded (c + 1)
    refine ⟨t, ?_⟩
    have hb : c + 1 ≤ Nat.floor (b t) := Nat.le_floor (by exact_mod_cast le_of_lt ht)
    omega
  obtain ⟨G, hg⟩ := horizon_to_anytime_nat H hu hne (fun t => Nat.floor (b t)) hm hu'
    (fun t ht => Nat.le_floor (by simpa using hpositive t ht))
    (fun t => by
      by_cases ht : 1 ≤ t
      · exact Nat.le_floor (hbound t ht)
      · have he : t = 0 := by omega
        subst t
        exact Nat.le_trans (mf_le_horizon H 0) (Nat.zero_le _))
  refine ⟨G, ?_⟩
  intro xs hn hl h hh hr
  have hb : (mistakes h (G.play xs) : ℝ) ≤ 4 * (Nat.floor (b xs.length) : ℝ) := by
    exact_mod_cast hg xs hn hl h hh hr
  have hf := Nat.floor_le (show 0 ≤ b xs.length by linarith [hpositive xs.length hl])
  linarith

end PredictionToGeneration

