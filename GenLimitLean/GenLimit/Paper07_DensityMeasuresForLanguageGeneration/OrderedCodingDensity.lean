import GenLimit.Core.NaturalDensity

namespace GenLimit.KleinbergWei.DensityMeasures.CommonOrder
open Filter

/-- Coding into the natural numbers preserves lower density when each
sufficiently late target element bounds exactly its preceding target
prefix. Its finite initial scramble has no effect on the density. -/
theorem lowerDensity_code (O : OrderedLanguage) (code : ℕ → ℕ)
    (hinj : Function.Injective code)
    (horder : ∃ N, ∀ j ≥ N, ∀ i < j, code (O.enumeration i) < code (O.enumeration j))
    (A : Language) :
    (OrderedLanguage.increasing (Set.range (code ∘ O.enumeration))
      (Set.infinite_range_of_injective (hinj.comp O.enumeration_injective))).lowerDensity A =
      O.lowerDensity (code ⁻¹' A) := by
  classical
  let g := code ∘ O.enumeration
  let K := Set.range g
  have hg : Function.Injective g := hinj.comp O.enumeration_injective
  let hi := Set.infinite_range_of_injective hg
  obtain ⟨N,hN⟩ := horder
  apply liminf_congr
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcut (i : ℕ) : g i < g n ↔ i < n := by
    constructor
    · intro h
      by_contra! hle
      rcases hle.eq_or_lt with he | hl
      · exact h.ne (congrArg g he.symm)
      · exact h.asymm (hN i (hn.trans hl.le) n hl)
    · exact hN n hn i
  have counted (B : Language) :
      Nat.count (· ∈ B ∩ K) (g n) = O.prefixCount (code ⁻¹' B) n := by
    rw [Nat.count_eq_card_filter_range, OrderedLanguage.prefixCount]
    symm
    apply Finset.card_bij (fun i _ ↦ g i)
    · intro i h
      obtain ⟨hi,hB⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((hcut i).2 (Finset.mem_range.mp hi)),hB,⟨i,rfl⟩⟩
    · exact fun _ _ _ _ h ↦ hg h
    · intro x hx
      obtain ⟨hx,hB,⟨i,rfl⟩⟩ := Finset.mem_filter.mp hx
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((hcut i).1 (Finset.mem_range.mp hx)),hB⟩,rfl⟩
  have hc : Nat.count (· ∈ K) (g n) = n := by
    simpa [OrderedLanguage.prefixCount] using counted Set.univ
  have he := OrderedLanguage.increasing_prefixCount K hi A (g n)
  rw [hc,counted] at he
  change (OrderedLanguage.increasing K hi).prefixRatio A n = O.prefixRatio (code ⁻¹' A) n
  simp only [OrderedLanguage.prefixRatio,he]

end GenLimit.KleinbergWei.DensityMeasures.CommonOrder
