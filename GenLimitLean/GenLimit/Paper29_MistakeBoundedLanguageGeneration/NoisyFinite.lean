import GenLimit.Paper29_MistakeBoundedLanguageGeneration.NoisyGeneration

/-! # Lemma 7.1: noisy finite classes -/
namespace GenLimit.MistakeBounded
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def membershipErrors (K : Set α) (s : ℕ → α) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, if s t ∈ K then 0 else 1

theorem noisy_finite_generation [Infinite α] {N : ℕ} (L : Fin N → Set α)
    (g : ℝ) (hg : 0 < g) (hu : g ≤ 3/4) :
    ∃ G : Generic.Generator α, (∀ t h (i : Fin t), G t h ≠ h i) ∧
      ∀ s, Function.Injective s → ∀ i T,
        (membershipErrors (L i) (Generic.output G s) T : ℝ) ≤
          (1+2*g)*membershipErrors (L i) s T + Real.logb 2 N / g := by
  classical
  let R : NoisyRule (Fin N) α := ⟨L, fun _ => Finset.univ, fun _ => 1, g⟩
  refine ⟨R.generator,R.fresh,?_⟩
  intro s hs i T
  have h := R.active_mistake_bound s hs (fun _ => zero_le_one) hg hu T Finset.univ
    (fun _ _ => Finset.Subset.rfl) i (Finset.mem_univ _) zero_lt_one
  simpa [NoisyRule.activeMistakes,membershipErrors,R,ite_not] using h

end
end GenLimit.MistakeBounded
