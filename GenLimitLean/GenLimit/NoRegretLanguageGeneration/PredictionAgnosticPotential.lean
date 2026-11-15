import GenLimit.NoRegretLanguageGeneration.CapacityAgnostic
import GenLimit.NoRegretLanguageGeneration.FiniteMinimax
import Mathlib.Tactic

namespace PredictionToGeneration
open scoped ENNReal

noncomputable def agnosticWeight (η : ℝ≥0∞) (h : Hypothesis X) : Trajectory X → ℝ≥0∞
  | [] => 1
  | (z,x)::τ => signedFactor η (h z) (h x) * agnosticWeight η h τ

theorem signed_updated_weights_finite (w : Hypothesis X → ℝ≥0∞)
    (hw : (Set.range w).Finite) (η : ℝ≥0∞) (z x : X) :
    (Set.range (fun h => signedFactor η (h z) (h x) * w h)).Finite := by
  let p := Set.range (fun b : Bool × Bool => signedFactor η b.1 b.2)
  have hp : p.Finite := Set.finite_range _
  apply ((hp.prod hw).image (fun t : ℝ≥0∞ × ℝ≥0∞ => t.1*t.2)).subset
  rintro _ ⟨h, rfl⟩
  exact ⟨(_, _), ⟨⟨(h z,h x),rfl⟩, ⟨h,rfl⟩⟩,rfl⟩

/-- A deterministic finite strategy controls every comparator's multiplicative weight. -/
theorem capacity_agnostic_strategy (fallback : Generator X) (η : ℝ≥0∞) (hη : η ≤ 1)
    (n : Nat) (τ : Trajectory X) (H : HypothesisClass X)
    (w : Hypothesis X → ℝ≥0∞) (hw : (Set.range w).Finite)
    (hinv : ∀ h, H h → w h = agnosticWeight η h τ) :
    ∃ s : Strategy X n τ, Guarantees
      (fun leaf => ∀ h, H h → agnosticWeight η h leaf ≤ capacity H w (2*n)) s := by
  classical
  induction n generalizing τ w with
  | zero =>
    refine ⟨.done τ, ?_⟩
    intro h hh
    rw [← hinv h hh]
    exact capacity_zero_le H w h hh
  | succ n ih =>
    obtain ⟨z, hz, hmax⟩ := capacity_maximizer H w hw (2*n+1) {x | Fresh τ x}
      ⟨fallback.output (demonstrations τ), fallback.fresh _⟩
    let v := fun x h => signedFactor η (h z) (h x) * w h
    have hv (x : X) : (Set.range (v x)).Finite := signed_updated_weights_finite w hw η z x
    have hi (x : X) : ∀ h, H h → v x h = agnosticWeight η h ((z,x)::τ) := by
      intro h hh
      simp only [v, agnosticWeight, hinv h hh]
    have child (x : X) := ih ((z,x)::τ) (v x) (hv x) (hi x)
    let next := fun x (_ : Fresh τ x) => Classical.choose (child x)
    refine ⟨.step z hz next, ?_⟩
    intro x hx
    apply guarantees_mono (next x hx) (hs := Classical.choose_spec (child x))
    intro leaf hb h hh
    have hu := capacity_agnostic_update H w (2*n) z x η hη (hmax x hx)
    have ht := (hb h hh).trans hu
    simpa [Nat.mul_add] using ht

theorem finite_ldim_agnostic_potential (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h)
    (d T : Nat) (hd : LdimLE H d) (η : ℝ≥0∞) (hη : η ≤ 1) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → xs.length = T →
      ∀ h, H h → agnosticWeight η h (G.play xs) ≤ (sauer (2*T) d : ℝ≥0∞) := by
  obtain ⟨s, hs⟩ := capacity_agnostic_strategy (generatorOfUUS H hu hne) η hη T [] H (fun _ => 1)
    Set.finite_range_const (by intro h _; rfl)
  have ht : Guarantees (fun leaf => ∀ h, H h → agnosticWeight η h leaf ≤ (sauer (2*T) d : ℝ≥0∞)) s := by
    apply guarantees_mono s (hs := hs)
    intro leaf hb h hh
    exact (hb h hh).trans (capacity_sauer H d hd (2*T))
  obtain ⟨G, hg⟩ := (strategy_iff_generator (generatorOfUUS H hu hne) _ T).mp ⟨s, ht⟩
  exact ⟨G, (G.guarantees_iff_histories _ T).mp hg⟩

end PredictionToGeneration
