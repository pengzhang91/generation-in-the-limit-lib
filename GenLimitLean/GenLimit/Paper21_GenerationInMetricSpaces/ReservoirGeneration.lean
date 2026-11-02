import GenLimit.Paper21_GenerationInMetricSpaces.UniformSufficiency
import GenLimit.Paper21_GenerationInMetricSpaces.HilbertGeometry

/-!
# Finite-sample reservoirs

The examples use the same semantic choice generator as Theorem 3.1. An
observed structured point certifies an infinite reservoir in every target
consistent with the sample. The chosen fresh point is therefore causal.
-/

namespace GenLimit.MetricSpaces

open GenLimit.Generic

theorem scaleClosureGenerator_correct_of_fresh [Nonempty α]
    {ρ : Distance α} {ε' : ℝ} {H : LanguageClass α}
    {L : Language α} (hL : L ∈ H) {stream : Stream α}
    (hstream : StreamIn stream L) (t : ℕ)
    (hfresh : ∃ y, y ∈ commonCore H (sample stream t) ∧
      y ∉ closedNeighborhood ρ (sample stream t : Set α) ε') :
    MetricCorrectAt ρ ε' (scaleClosureGenerator ρ ε' H) L stream t := by
  have hs := scaleClosureGenerator_spec (ρ := ρ) (ε' := ε') (H := H)
    (xs := fun i : Fin t => stream i)
    (by simpa only [sequenceSample_prefix] using hfresh)
  rw [sequenceSample_prefix] at hs
  exact ⟨hs.1 L (target_mem_versionSpace hL hstream t), hs.2⟩

namespace HilbertAxisReservoir

/-- An injective axis sequence escapes any finite axis-supported sample. -/
theorem axisInjection_avoids_finset (S : Finset Hilbert2)
    (haxis : AxisSupported (S : Set Hilbert2))
    (f : ℕ → ℕ) (hf : Function.Injective f)
    {c γ : ℝ} (hc : 0 < c) (hγc : γ < c) :
    ∃ n, axisPoint c (f n) ∉ closedNeighborhood dist (S : Set Hilbert2) γ := by
  classical
  have hrep : ∀ x : S, ∃ a q, (x : Hilbert2) = axisPoint a q :=
    fun x => haxis x x.property
  choose a q hq using hrep
  obtain ⟨v, ⟨n, rfl⟩, hn⟩ :=
    (Set.infinite_range_of_injective hf).exists_notMem_finset (Finset.univ.image q)
  refine ⟨n, ?_⟩
  intro hnear
  obtain ⟨x, hx, hclose⟩ := hnear c hγc
  have hne : q ⟨x, hx⟩ ≠ f n := by
    intro heq
    exact hn (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, heq⟩)
  have hfar := abs_amplitude_le_dist_axisPoint_of_ne (a ⟨x, hx⟩) c hne
  rw [← hq ⟨x, hx⟩, abs_of_pos hc] at hfar
  exact (not_lt_of_ge hfar) hclose

end HilbertAxisReservoir
end GenLimit.MetricSpaces
