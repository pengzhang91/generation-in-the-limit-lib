import GenLimit.NoRegretLanguageGeneration.AnytimeAgnostic
import GenLimit.NoRegretLanguageGeneration.AsymptoticBridge
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

namespace PredictionToGeneration

/-- The manuscript's factor-four theorem for arbitrary real-valued envelopes. -/
theorem agnostic_horizon_to_anytime_real (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (b : ℕ → ℝ)
    (hmono : Monotone b) (hunbounded : ∀ c : ℝ, ∃ t, c < b t)
    (hpositive : ∀ t, 1 ≤ t → 1 ≤ b t)
    (hbound : ∀ t, (SMF H t : ℝ) ≤ b t) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → 1 ≤ xs.length →
      ∀ h, H h → (regret h (G.play xs) : ℝ) ≤ 4 * b xs.length := by
  let r : ℕ → ℕ := fun t => ⌊b t⌋₊
  have hm : ∀ i j, i ≤ j → r i ≤ r j := fun _ _ hij => Nat.floor_mono (hmono hij)
  have hu' : ∀ c, ∃ t, c < r t := by
    intro c
    obtain ⟨t, ht⟩ := hunbounded ((c : ℝ)+1)
    refine ⟨t, ?_⟩
    have hf : c+1 ≤ r t := Nat.le_floor (by exact_mod_cast le_of_lt ht)
    omega
  have hp : ∀ t, 1 ≤ t → 1 ≤ r t := fun t ht => Nat.le_floor (by simpa using hpositive t ht)
  have hb : ∀ t, SMF H t ≤ r t := fun t => Nat.le_floor (hbound t)
  obtain ⟨G, hg⟩ := agnostic_horizon_to_anytime_nat H hu hne r hm hu' hp hb
  refine ⟨G, fun xs hn hl h hh => ?_⟩
  have hi := hg xs hn hl h hh
  have hi' : (regret h (G.play xs) : ℝ) ≤ 4 * (r xs.length : ℝ) := by exact_mod_cast hi
  have hf : (r xs.length : ℝ) ≤ b xs.length := Nat.floor_le (by linarith [hpositive xs.length hl])
  linarith

/-- Agnostic generation is possible exactly when the signed minimax profile is little-o of time. -/
theorem agnostic_no_regret_iff_isLittleO (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) :
    AgnosticNoRegret H ↔
      Asymptotics.IsLittleO Filter.atTop (fun t => (SMF H t : ℝ)) (fun t => (t : ℝ)) := by
  rw [agnostic_no_regret_iff H hu hne, natSublinear_iff_isLittleO]

end PredictionToGeneration
