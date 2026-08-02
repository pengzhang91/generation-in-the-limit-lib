import GenLimit.LiRamanTewari.Closure
import Mathlib.Data.ENat.Basic

/-!
# Uniform generation sample complexity

This module formalizes Definition 2.3 and the quantitative conclusion
following Theorem 3.3 in Li--Raman--
Tewari, *Generation through the Lens of Learning Theory*,
arXiv:2410.13714v5 / COLT 2025.

For a fixed generator, the paper defines the uniform generation sample
complexity as its least valid threshold, or `∞` when no threshold is valid.
We represent `ℕ ∪ {∞}` literally by `WithTop ℕ`.  The quantitative closure
dimension argument gives the sharp bounds

`C(H) ≤ d_G` for every uniform generator `G`, and
`d_G ≤ C(H) + 1` for the closure generator.

Thus the optimal sample complexity lies in the one-step interval
`[C(H), C(H) + 1]`.  This is the precise quantitative statement behind the
paper's asymptotic sentence (with the zero-dimension edge case kept
explicit).  No exact equality is asserted.
-/

namespace GenLimit.LiRamanTewari

/-- A valid uniform threshold remains valid after increasing it. -/
theorem uniform_threshold_mono
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} {d n : ℕ}
    (hdn : d ≤ n) (hgen : IsUniformGeneratorAt gen H d) :
    IsUniformGeneratorAt gen H n := by
  intro L hLH stream hstream
  exact GenLimit.Generic.eventualAtExactSize_mono
    (size := fun t ↦ (GenLimit.Generic.sample stream t).card)
    (fun hk ↦ GenLimit.Generic.exists_sample_card_eq_of_le hk)
    hdn (hgen L hLH stream hstream)

/-- Definition 2.3's uniform generation sample complexity for a fixed
generator: the least valid natural threshold, or `⊤` when none exists. -/
noncomputable def uniformGenerationSampleComplexity
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : WithTop ℕ := by
  classical
  exact
    if h : ∃ d : ℕ, IsUniformGeneratorAt gen H d then
      (Nat.find h : WithTop ℕ)
    else
      ⊤

theorem uniformGenerationSampleComplexity_eq_top_iff
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} :
    uniformGenerationSampleComplexity gen H = ⊤ ↔
      ¬ ∃ d : ℕ, IsUniformGeneratorAt gen H d := by
  classical
  by_cases h : ∃ d : ℕ, IsUniformGeneratorAt gen H d
  · simp [uniformGenerationSampleComplexity, h]
  · simp [uniformGenerationSampleComplexity, h]

theorem uniformGenerationSampleComplexity_lt_top_iff
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} :
    uniformGenerationSampleComplexity gen H < ⊤ ↔
      ∃ d : ℕ, IsUniformGeneratorAt gen H d := by
  rw [lt_top_iff_ne_top, ne_eq, uniformGenerationSampleComplexity_eq_top_iff]
  simp

/-- The least-threshold specification: the extended sample complexity is at
most `d` exactly when `d` itself is a valid uniform threshold. -/
theorem uniformGenerationSampleComplexity_le_coe_iff
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ} :
    uniformGenerationSampleComplexity gen H ≤ (d : WithTop ℕ) ↔
      IsUniformGeneratorAt gen H d := by
  classical
  constructor
  · intro hle
    by_cases h : ∃ e : ℕ, IsUniformGeneratorAt gen H e
    · have hfind : Nat.find h ≤ d := by
        apply WithTop.coe_le_coe.mp
        simpa [uniformGenerationSampleComplexity, h] using hle
      exact uniform_threshold_mono hfind (Nat.find_spec h)
    · simp [uniformGenerationSampleComplexity, h] at hle
  · intro hd
    let h : ∃ e : ℕ, IsUniformGeneratorAt gen H e := ⟨d, hd⟩
    have hfind : Nat.find h ≤ d := Nat.find_min' h hd
    simpa [uniformGenerationSampleComplexity, h] using
      (WithTop.coe_le_coe.mpr hfind)

/-- The value is exactly `d` precisely when `d` is valid and no smaller
threshold is valid. -/
theorem uniformGenerationSampleComplexity_eq_coe_iff
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ} :
    uniformGenerationSampleComplexity gen H = (d : WithTop ℕ) ↔
      IsUniformGeneratorAt gen H d ∧
        ∀ e : ℕ, e < d → ¬ IsUniformGeneratorAt gen H e := by
  classical
  constructor
  · intro heq
    have hd : IsUniformGeneratorAt gen H d :=
      uniformGenerationSampleComplexity_le_coe_iff.mp (le_of_eq heq)
    refine ⟨hd, ?_⟩
    intro e hed he
    have hle :
        uniformGenerationSampleComplexity gen H ≤ (e : WithTop ℕ) :=
      uniformGenerationSampleComplexity_le_coe_iff.mpr he
    rw [heq] at hle
    exact (Nat.not_le_of_lt hed) (WithTop.coe_le_coe.mp hle)
  · rintro ⟨hd, hminimal⟩
    let h : ∃ e : ℕ, IsUniformGeneratorAt gen H e := ⟨d, hd⟩
    have hfind_le : Nat.find h ≤ d := Nat.find_min' h hd
    have hd_le_find : d ≤ Nat.find h := by
      by_contra hnot
      have hlt : Nat.find h < d := Nat.lt_of_not_ge hnot
      exact hminimal (Nat.find h) hlt (Nat.find_spec h)
    have hfind : Nat.find h = d := Nat.le_antisymm hfind_le hd_le_find
    simp [uniformGenerationSampleComplexity, h, hfind]

theorem uniformlyGeneratable_iff_exists_sampleComplexity_lt_top
    {H : GenLimit.Generic.LanguageClass α} :
    UniformlyGeneratable H ↔
      ∃ gen : GenLimit.Generic.Generator α,
        uniformGenerationSampleComplexity gen H < ⊤ := by
  constructor
  · rintro ⟨gen, d, hgen⟩
    exact ⟨gen,
      uniformGenerationSampleComplexity_lt_top_iff.mpr ⟨d, hgen⟩⟩
  · rintro ⟨gen, hgen⟩
    obtain ⟨d, hd⟩ :=
      uniformGenerationSampleComplexity_lt_top_iff.mp hgen
    exact ⟨gen, d, hd⟩

/-- The optimal uniform generation sample complexity of a class: the least
threshold attained by any generator, or `⊤` when the class is not uniformly
generatable. -/
noncomputable def optimalUniformGenerationSampleComplexity
    (H : GenLimit.Generic.LanguageClass α) : WithTop ℕ := by
  classical
  exact
    if h :
        ∃ d : ℕ, ∃ gen : GenLimit.Generic.Generator α,
          IsUniformGeneratorAt gen H d then
      (Nat.find h : WithTop ℕ)
    else
      ⊤

theorem optimalUniformGenerationSampleComplexity_eq_top_iff
    {H : GenLimit.Generic.LanguageClass α} :
    optimalUniformGenerationSampleComplexity H = ⊤ ↔
      ¬ UniformlyGeneratable H := by
  classical
  have hex :
      (∃ d : ℕ, ∃ gen : GenLimit.Generic.Generator α,
          IsUniformGeneratorAt gen H d) ↔
        UniformlyGeneratable H := by
    constructor
    · rintro ⟨d, gen, hgen⟩
      exact ⟨gen, d, hgen⟩
    · rintro ⟨gen, d, hgen⟩
      exact ⟨d, gen, hgen⟩
  by_cases h :
      ∃ d : ℕ, ∃ gen : GenLimit.Generic.Generator α,
        IsUniformGeneratorAt gen H d
  · simp [optimalUniformGenerationSampleComplexity, h, hex.mp h]
  · have hnotUniform : ¬ UniformlyGeneratable H :=
      fun hUniform ↦ h (hex.mpr hUniform)
    simp [optimalUniformGenerationSampleComplexity, h, hnotUniform]

/-- The optimal value is at most `d` exactly when some generator works at
threshold `d`. -/
theorem optimalUniformGenerationSampleComplexity_le_coe_iff
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ} :
    optimalUniformGenerationSampleComplexity H ≤ (d : WithTop ℕ) ↔
      ∃ gen : GenLimit.Generic.Generator α,
        IsUniformGeneratorAt gen H d := by
  classical
  constructor
  · intro hle
    by_cases h :
        ∃ e : ℕ, ∃ gen : GenLimit.Generic.Generator α,
          IsUniformGeneratorAt gen H e
    · have hfind : Nat.find h ≤ d := by
        apply WithTop.coe_le_coe.mp
        simpa [optimalUniformGenerationSampleComplexity, h] using hle
      obtain ⟨gen, hgen⟩ := Nat.find_spec h
      exact ⟨gen, uniform_threshold_mono hfind hgen⟩
    · simp [optimalUniformGenerationSampleComplexity, h] at hle
  · rintro ⟨gen, hgen⟩
    let h :
        ∃ e : ℕ, ∃ gen : GenLimit.Generic.Generator α,
          IsUniformGeneratorAt gen H e :=
      ⟨d, gen, hgen⟩
    have hfind : Nat.find h ≤ d :=
      Nat.find_min' h ⟨gen, hgen⟩
    simpa [optimalUniformGenerationSampleComplexity, h] using
      (WithTop.coe_le_coe.mpr hfind)

/-- Quantitative necessity: if `C(H) = d`, every valid threshold for every
generator is at least `d`. -/
theorem closure_dimension_le_uniform_threshold [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d)
    {gen : GenLimit.Generic.Generator α} {e : ℕ}
    (hgen : IsUniformGeneratorAt gen H e) :
    d ≤ e := by
  by_contra hnot
  have hed : e < d := Nat.lt_of_not_ge hnot
  rcases hC.2 with hzero | ⟨S, hSd, hS⟩
  · omega
  · have heS : e ≤ S.card := by omega
    obtain ⟨T, hTS, hTe⟩ := Finset.exists_subset_card_eq heS
    have hT : IsClosureWitness H T := closure_witness_mono hTS hS
    exact (closure_witness_defeats_uniform_threshold hUUS hTe hT gen) hgen

/-- Generator-wise extended-natural lower bound `C(H) ≤ d_G`. -/
theorem closure_dimension_le_uniformGenerationSampleComplexity
    [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d)
    (gen : GenLimit.Generic.Generator α) :
    (d : WithTop ℕ) ≤ uniformGenerationSampleComplexity gen H := by
  classical
  by_cases h : ∃ e : ℕ, IsUniformGeneratorAt gen H e
  · have hde : d ≤ Nat.find h :=
      closure_dimension_le_uniform_threshold hUUS hC (Nat.find_spec h)
    simpa [uniformGenerationSampleComplexity, h] using
      (WithTop.coe_le_coe.mpr hde)
  · simp [uniformGenerationSampleComplexity, h]

/-- The closure generator from Lemma 3.2 has sample complexity at most
`C(H) + 1`. -/
theorem closureGenerator_uniformGenerationSampleComplexity_le
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d) :
    uniformGenerationSampleComplexity
        (closureGenerator H d hC.1) H ≤
      ((d + 1 : ℕ) : WithTop ℕ) := by
  apply uniformGenerationSampleComplexity_le_coe_iff.mpr
  exact closureGenerator_isUniformGeneratorAt hUUS hC

/-- The optimal value inherits the generator-wise lower bound. -/
theorem closure_dimension_le_optimalUniformGenerationSampleComplexity
    [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d) :
    (d : WithTop ℕ) ≤ optimalUniformGenerationSampleComplexity H := by
  classical
  by_cases h :
      ∃ e : ℕ, ∃ gen : GenLimit.Generic.Generator α,
        IsUniformGeneratorAt gen H e
  · obtain ⟨gen, hgen⟩ := Nat.find_spec h
    have hde : d ≤ Nat.find h :=
      closure_dimension_le_uniform_threshold hUUS hC hgen
    simpa [optimalUniformGenerationSampleComplexity, h] using
      (WithTop.coe_le_coe.mpr hde)
  · simp [optimalUniformGenerationSampleComplexity, h]

/-- The closure generator supplies the one-step upper bound for the optimal
value. -/
theorem optimalUniformGenerationSampleComplexity_le_closureDimension_succ
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d) :
    optimalUniformGenerationSampleComplexity H ≤
      ((d + 1 : ℕ) : WithTop ℕ) := by
  apply optimalUniformGenerationSampleComplexity_le_coe_iff.mpr
  exact ⟨closureGenerator H d hC.1,
    closureGenerator_isUniformGeneratorAt hUUS hC⟩

/-- Quantitative conclusion following Theorem 3.3: the optimal value lies in
the exact one-step interval from `C(H)` to `C(H) + 1`.

For positive `C(H)` this immediately gives the usual constant-factor
`Θ(C(H))` reading.  The statement intentionally retains the separate
zero-dimension edge case instead of claiming the false equality
`d_G = C(H)`. -/
theorem optimal_uniform_generation_sample_complexity_bounds
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d) :
    (d : WithTop ℕ) ≤ optimalUniformGenerationSampleComplexity H ∧
      optimalUniformGenerationSampleComplexity H ≤
        ((d + 1 : ℕ) : WithTop ℕ) := by
  exact ⟨closure_dimension_le_optimalUniformGenerationSampleComplexity hUUS hC,
    optimalUniformGenerationSampleComplexity_le_closureDimension_succ hUUS hC⟩

end GenLimit.LiRamanTewari
