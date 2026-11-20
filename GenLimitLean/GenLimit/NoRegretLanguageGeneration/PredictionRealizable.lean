import GenLimit.NoRegretLanguageGeneration.CapacityBounds
import GenLimit.NoRegretLanguageGeneration.FiniteMinimax
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace PredictionToGeneration
open scoped ENNReal

theorem outcome_realizes_prefix {n : Nat} {τ : Trajectory X} (s : Strategy X n τ)
    (leaf : Trajectory X) (ho : Outcome s leaf) (h : Hypothesis X)
    (hr : Realizes h leaf) : Realizes h τ := by
  induction s with
  | done τ => change leaf = τ at ho; subst leaf; exact hr
  | step z hz next ih =>
    obtain ⟨x, hx, ht⟩ := ho
    exact (ih x hx ht).2

theorem updated_weights_finite (w : Hypothesis X → ℝ≥0∞) (hw : (Set.range w).Finite) (z : X) :
    (Set.range (fun h => if h z then w h else 2*w h)).Finite := by
  have hmul : (Set.range (fun h => (2 : ℝ≥0∞)*w h)).Finite :=
    (hw.image (fun t => 2*t)).subset (by rintro _ ⟨h, rfl⟩; exact ⟨w h, ⟨h, rfl⟩, rfl⟩)
  exact Set.finite_range_ite hw hmul

/-- The potential construction includes an actual finite strategy. -/
theorem capacity_realizable_strategy (fallback : Generator X) (n : Nat) (τ : Trajectory X)
    (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞) (hw : (Set.range w).Finite)
    (hinv : ∀ h, H h → w h = (2 : ℝ≥0∞)^mistakes h τ) :
    ∃ s : Strategy X n τ, Guarantees
      (fun leaf => ∀ h, H h → Realizes h leaf → (2 : ℝ≥0∞)^mistakes h leaf ≤ capacity H w (2*n)) s := by
  classical
  induction n generalizing τ H w with
  | zero =>
    refine ⟨.done τ, ?_⟩
    intro h hh _
    rw [← hinv h hh]
    exact capacity_zero_le H w h hh
  | succ n ih =>
    obtain ⟨z, hz, hmax⟩ := capacity_maximizer H w hw (2*n+1) {x | Fresh τ x}
      ⟨fallback.output (demonstrations τ), fallback.fresh _⟩
    let v := fun h => if h z then w h else 2*w h
    have hv : (Set.range v).Finite := updated_weights_finite w hw z
    have hi (x : X) : ∀ h, restrict H x true h → v h = (2 : ℝ≥0∞)^mistakes h ((z,x)::τ) := by
      intro h hh
      dsimp [v]
      rw [hinv h hh.1]
      cases he : h z <;> simp [mistakes, loss, he, pow_add]
    have child (x : X) := ih ((z,x)::τ) (restrict H x true) v hv (hi x)
    let next := fun x (_ : Fresh τ x) => Classical.choose (child x)
    refine ⟨.step z hz next, ?_⟩
    intro x hx
    apply (guarantees_iff_outcomes _ (next x hx)).mpr
    intro leaf ho h hh hr
    have hp := outcome_realizes_prefix (next x hx) leaf ho h hr
    have hb := (guarantees_iff_outcomes _ (next x hx)).mp (Classical.choose_spec (child x))
      leaf ho h ⟨hh, hp.1⟩ hr
    have hu := capacity_realizable_update H w (2*n) z x (hmax x hx)
    have ht := hb.trans hu
    simpa [Nat.mul_add] using ht

theorem finite_ldim_exponential (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h)
    (d T : Nat) (hd : LdimLE H d) : 2 ^ MF H T ≤ sauer (2*T) d := by
  obtain ⟨s, hs⟩ := capacity_realizable_strategy (generatorOfUUS H hu hne) T [] H (fun _ => 1)
    Set.finite_range_const (by intro h _; simp [mistakes])
  obtain ⟨leaf, h, ho, _, _, hh, hr, hm⟩ := realizable_lower_bound H T (MF H T)
    (mf_spec H hu hne T).1 s
  have hb := (guarantees_iff_outcomes _ s).mp hs leaf ho h hh hr
  have hsauer := capacity_sauer H d hd (2*T)
  have hp : (2 : ℝ≥0∞) ^ MF H T ≤ (2 : ℝ≥0∞)^mistakes h leaf :=
    pow_le_pow_right₀ (by norm_num) hm
  exact_mod_cast hp.trans (hb.trans hsauer)

/-- Exact finite-horizon bound from `thm:finite-ldim-realizable`.
Nat.log 2 is the floor of the base-two logarithm on positive integers. -/
theorem finite_ldim_realizable_log (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h)
    (d T : Nat) (hd : LdimLE H d) :
    MF H T ≤ Nat.log 2 (∑ i ∈ Finset.range (min d (2*T)+1), (2*T).choose i) := by
  rw [← sauer_eq_truncated_choose]
  exact Nat.le_log_of_pow_le (by decide) (finite_ldim_exponential H hu hne d T hd)

end PredictionToGeneration

