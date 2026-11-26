import GenLimit.Paper24_PriceOfPrivacy.ExponentialSelection
import GenLimit.Paper24_PriceOfPrivacy.GaussianSelection
import GenLimit.Paper24_PriceOfPrivacy.Resampling

/-! Algorithm 1 for a finite window. Both mechanisms map the selected
candidate back into the public enumeration of the collection. -/

namespace GenLimit.PriceOfPrivacy.Selection

open DiscreteIID Set
open scoped NNReal Classical
noncomputable section

variable {w : ℕ} [NeZero w]

def pureLaw (score : List X → Fin w → ℝ) (Δ ε : ℝ) (xs : List X) : PMF ℕ :=
  (Exponential.law (score xs) (ε/(2*Δ))).map Fin.val

def variance (w : ℕ) (Δ ε δ : ℝ) : ℝ≥0 :=
  Real.toNNReal (2*Real.log ((5/4)/δ)*w*Δ^2/ε^2)

def gaussianLaw (score : List X → Fin w → ℝ) (Δ ε δ : ℝ) (xs : List X) : PMF ℕ :=
  (Gaussian.law (score xs) (variance w Δ ε δ)).map Fin.val

omit [NeZero w] in
private theorem log_pos {δ : ℝ} (hδ : δ ∈ Ioo 0 1) : 0 < Real.log ((5/4)/δ) :=
  Real.log_pos ((lt_div_iff₀ hδ.1).mpr (by linarith [hδ.2]))

omit [NeZero w] in
theorem variance_value {Δ ε δ : ℝ} (hd : 0 < Δ) (he : 0 < ε) (hδ : δ ∈ Ioo 0 1) :
    (variance w Δ ε δ : ℝ) = 2*Real.log ((5/4)/δ)*w*Δ^2/ε^2 := by
  have := log_pos hδ
  exact Real.coe_toNNReal _ (by positivity)

omit [NeZero w] in
private theorem map_event (q : PMF (Fin w)) (E : Set ℕ) :
    probability (q.map Fin.val) E = probability q (Fin.val ⁻¹' E) := by
  simp only [probability,PMF.toOuterMeasure_map_apply]

def SensitiveAt (score : List X → Fin w → ℝ) (Δ : ℝ) (n : ℕ) : Prop :=
  ∀ pre x y post, pre.length+post.length+1 = n → ∀ i,
    |score (pre ++ x::post) i-score (pre ++ y::post) i| ≤ Δ

theorem pure_private {score : List X → Fin w → ℝ} {Δ ε : ℝ} {n : ℕ} (hd : 0 < Δ)
    (he : 0 < ε) (h : SensitiveAt score Δ n) : PrivateAt ε 0 n (pureLaw score Δ ε) := by
  intro pre x y post len E
  simp only [pureLaw,map_event,add_zero]
  have h' := Exponential.event_private _ _ (ε/(2*Δ)) Δ (by positivity) (h pre x y post len) (Fin.val ⁻¹' E)
  rwa [show 2*(ε/(2*Δ))*Δ = ε by field_simp] at h'

theorem gaussian_private {score : List X → Fin w → ℝ} {Δ ε δ : ℝ} {n : ℕ} (hd : 0 < Δ)
    (he : ε ∈ Ioo 0 1) (hδ : δ ∈ Ioo 0 1) (h : SensitiveAt score Δ n) :
    PrivateAt ε δ n (gaussianLaw score Δ ε δ) := by
  intro pre x y post len E
  simp only [gaussianLaw,map_event]
  have hl := log_pos hδ
  have hw : (0:ℝ) < w := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne w)
  have hv := variance_value (w := w) hd he.1 hδ
  have vp : (0:ℝ) < variance w Δ ε δ := by rw [hv]; have := he.1; positivity
  apply Gaussian.selection_private _ _ (fun heq => by simp [heq] at vp) ε δ he hδ _ _
  have energy : Gaussian.energy (score (pre ++ x::post)) (score (pre ++ y::post)) ≤ w*Δ^2 := by
    unfold Gaussian.energy
    calc
      _ ≤ ∑ _ : Fin w, Δ^2 := Finset.sum_le_sum fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hd.le).mpr (h pre x y post len i)
      _ = _ := by simp
  rw [hv]
  calc
    _ ≤ 2*Real.log ((5/4)/δ)*(w*Δ^2) := mul_le_mul_of_nonneg_left energy (by positivity)
    _ = _ := by field_simp [he.1.ne']

theorem pure_gap {score : List X → Fin w → ℝ} {Δ ε Γ : ℝ} (hd : 0 < Δ) (he : 0 < ε)
    (xs : List X) (F : Set ℕ) (target : Fin w) (gap : ∀ i : Fin w, i.val ∈ F → Γ ≤ score xs target-score xs i) :
    probability (pureLaw score Δ ε xs) F ≤ w*Real.exp (-(ε/(2*Δ))*Γ) := by
  rw [pureLaw,map_event]
  simpa using Exponential.event_margin (score xs) (ε/(2*Δ)) (by positivity) (Fin.val ⁻¹' F) target Γ gap

theorem gaussian_gap {score : List X → Fin w → ℝ} {Δ ε δ Γ : ℝ}
    (hΓ : 0 < Γ) (xs : List X) (F : Set ℕ) (target : Fin w)
    (gap : ∀ i : Fin w, i.val ∈ F → Γ ≤ score xs target-score xs i) :
    probability (gaussianLaw score Δ ε δ xs) F ≤ 2*w*Real.exp (-Γ^2/(8*variance w Δ ε δ)) := by
  rw [gaussianLaw,map_event]
  exact Gaussian.event_margin _ _ _ target Γ hΓ gap

end
end GenLimit.PriceOfPrivacy.Selection
