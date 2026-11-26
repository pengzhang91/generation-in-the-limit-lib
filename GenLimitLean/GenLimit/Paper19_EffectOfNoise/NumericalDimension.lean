import GenLimit.Paper06_NoisyExamples.Quantitative
import GenLimit.Paper19_EffectOfNoise.SquareRoot
import Mathlib.Data.Nat.Sqrt

/-! # Numerical noisy closure dimension (Definition 2.12, Lemmas 2.13 and 3.2) -/

namespace GenLimit.QuantifyingNoise

/-- Definition 2.12. The finite witness sizes have the same supremum under
the two papers' closure conventions, since a witness requires a consistent language. -/
noncomputable def noisyClosureDimension (C : Generic.LanguageClass α) (i : ℕ) : WithTop ℕ :=
  NoisyExamples.noisyClosureDimension C i

theorem noisyClosureDimension_le_iff {C : Generic.LanguageClass α} {i d : ℕ} :
    noisyClosureDimension C i ≤ (d : WithTop ℕ) ↔
      ∀ k, NoisyClosureWitnessAt C i k → k ≤ d := by
  simp only [noisyClosureDimension, NoisyExamples.noisyClosureDimension_le_iff,
    noisyClosureWitnessAt_iff_rr]

theorem noisyClosureDimension_lt_top_iff {C : Generic.LanguageClass α} {i : ℕ} :
    noisyClosureDimension C i < ⊤ ↔ FiniteNoisyClosureDimensionAt C i :=
  NoisyExamples.noisyClosureDimension_lt_top_iff.trans
    (finiteNoisyClosureDimensionAt_iff_rr C i).symm

private theorem positive_le_dimension_iff {C : Generic.LanguageClass α} {i k : ℕ}
    (hk : 0 < k) : (k : WithTop ℕ) ≤ noisyClosureDimension C i ↔ NoisyClosureWitnessAt C i k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hsucc (d : WithTop ℕ) : ((k+1 : ℕ) : WithTop ℕ) ≤ d ↔ ¬d ≤ (k : WithTop ℕ) := by
    cases d using WithTop.recTopCoe with
    | top => simp
    | coe m =>
      constructor
      · intro hle hm
        exact (Nat.not_succ_le_self k) (WithTop.coe_le_coe.mp (hle.trans hm))
      · intro h
        exact WithTop.coe_le_coe.mpr (Nat.lt_of_not_ge fun hm ↦ h (WithTop.coe_le_coe.mpr hm))
  rw [hsucc, noisyClosureDimension_le_iff]
  constructor
  · intro h
    push_neg at h
    obtain ⟨l, hl, hkl⟩ := h
    exact noisyClosureWitnessAt_restrict hkl hl
  · intro h hall
    exact (Nat.not_succ_le_self k) (hall _ h)

/-- Lemma 2.13. The numerical dimension is monotone in the noise level. -/
theorem lemma_2_13 (C : Generic.LanguageClass α) : Monotone (noisyClosureDimension C) := by
  intro i j hij
  generalize he : noisyClosureDimension C j = value
  cases value using WithTop.recTopCoe with
  | top => exact le_top
  | coe d =>
    exact noisyClosureDimension_le_iff.mpr fun k hw ↦
      noisyClosureDimension_le_iff.mp he.le k (noisyClosureWitnessAt_mono hij hw)

/-- Lemma 3.2, with the integer square root extended by sqrt(∞) = ∞. -/
theorem lemma_3_2 (C : Generic.LanguageClass α) {i : ℕ} (hi : 2 ≤ i) :
    (noisyClosureDimension C i).map Nat.sqrt ≤ noisyClosureDimension C (i-1) := by
  generalize he : noisyClosureDimension C i = value
  cases value using WithTop.recTopCoe with
  | top =>
    have h : ¬FiniteNoisyClosureDimensionAt C i := by
      rw [← noisyClosureDimension_lt_top_iff, he]
      exact lt_irrefl _
    have hp := lemma_3_2_infinite_dimension_descends hi h
    rw [← noisyClosureDimension_lt_top_iff, not_lt_top_iff] at hp
    simp [hp]
  | coe d =>
    change ((d.sqrt : ℕ) : WithTop ℕ) ≤ _
    by_cases hz : d.sqrt = 0
    · simp [hz]
    have hpos := Nat.pos_of_ne_zero hz
    apply (positive_le_dimension_iff hpos).2
    apply lemma_3_2_squareRootWitnessTransfer hi _ hpos
    apply (positive_le_dimension_iff (Nat.mul_pos hpos hpos)).1
    rw [he]
    exact WithTop.coe_le_coe.mpr (Nat.sqrt_le d)

end GenLimit.QuantifyingNoise
