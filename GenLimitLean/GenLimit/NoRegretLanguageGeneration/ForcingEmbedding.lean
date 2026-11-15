import GenLimit.NoRegretLanguageGeneration.FiniteMinimax
import Mathlib.Tactic

namespace PredictionToGeneration

/-- Demonstrations in an embedded component correspond exactly to internal history. -/
def DemonstrationLink (embed : X → Y) (τ : Trajectory X) (σ : Trajectory Y) : Prop :=
  ∀ x, embed x ∈ demonstrations σ ↔ x ∈ demonstrations τ

/-- Outside outputs can be replaced by fresh internal outputs: their lifted loss
is one, so the replacement never increases the internal lower-bound claim. -/
theorem forces_embedding (H : HypothesisClass X) (C : HypothesisClass Y)
    (hu : UUS H) (hne : ∃ h,H h) (embed : X → Y) (hinj : Function.Injective embed)
    (lift : Hypothesis X → Hypothesis Y) (hmem : ∀ h,H h → C (lift h))
    (hlabel : ∀ h,H h → ∀ x,lift h (embed x)=h x)
    (n m : Nat) (τ : Trajectory X) (σ : Trajectory Y)
    (hlink : DemonstrationLink embed τ σ)
    (hreal : ∀ h,H h → Realizes h τ → Realizes (lift h) σ)
    (hcost : ∀ h,H h → mistakes h τ ≤ mistakes (lift h) σ)
    (hout : ∀ h,H h → ∀ y,Fresh σ y → (∀ x,embed x ≠ y) → lift h y=false)
    (hf : Forces (RealizableBad H m) n τ) : Forces (RealizableBad C m) n σ := by
  classical
  induction n generalizing τ σ with
  | zero =>
    obtain ⟨h,hh,hr,hm⟩ := hf
    exact ⟨lift h,hmem h hh,hreal h hh hr,Nat.le_trans hm (hcost h hh)⟩
  | succ n ih =>
    intro y hy
    have hsim : ∃ z,Fresh τ z ∧ ∀ h,H h → loss h z ≤ loss (lift h) y := by
      by_cases hex : ∃ z,embed z=y
      · obtain ⟨z,hz⟩ := hex
        refine ⟨z,?_,?_⟩
        · intro hm
          exact hy (hz ▸ (hlink z).mpr hm)
        · intro h hh
          rw [← hz]
          simp [loss,hlabel h hh]
      · obtain ⟨h0,hh0⟩ := hne
        obtain ⟨z,hz,_⟩ := hu h0 hh0 (demonstrations τ)
        refine ⟨z,hz,?_⟩
        intro h hh
        have hl := hout h hh y hy (fun z hz => hex ⟨z,hz⟩)
        simpa [loss,hl] using loss_le_one h z
    obtain ⟨z,hz,hcompare⟩ := hsim
    obtain ⟨x,hx,hnext⟩ := hf z hz
    refine ⟨embed x,(fun hm => hx ((hlink x).mp hm)),?_⟩
    apply ih ((z,x)::τ) ((y,embed x)::σ) ?_ ?_ ?_ ?_ hnext
    · intro w
      simp only [demonstrations,List.map_cons,List.mem_cons]
      rw [hinj.eq_iff]
      exact or_congr Iff.rfl (hlink w)
    · intro h hh hr
      exact ⟨by rw [hlabel h hh]; exact hr.1,hreal h hh hr.2⟩
    · intro h hh
      have hc := hcost h hh
      have hl := hcompare h hh
      simp only [mistakes]
      omega
    · intro h hh w hw hn
      apply hout h hh w ?_ hn
      intro hm
      exact hw (by simp [demonstrations] at hm ⊢; exact Or.inr hm)

end PredictionToGeneration
