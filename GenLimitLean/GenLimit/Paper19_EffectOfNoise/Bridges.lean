import GenLimit.Paper19_EffectOfNoise.Closure
import GenLimit.Paper06_NoisyExamples.NonuniformDefinitions

/-!
# Quantifying Noise: bridges to Raman--Raman

The source paper recalls several Raman--Raman definitions and results.  This
module proves that its finite-set noisy closure is extensionally the existing
one, while retaining the paper's stricter injective-enumeration and inclusive
time conventions at the public boundary.
-/

namespace GenLimit.QuantifyingNoise

theorem missingAtMost_finset_iff
    (S : Finset α) (L : GenLimit.Generic.Language α) (i : ℕ) :
    MissingAtMost (↑S : Set α) L i ↔
      (GenLimit.NoisyExamples.negativePart S L).card ≤ i := by
  classical
  constructor
  · rintro ⟨F, hF, hcard⟩
    have heq : GenLimit.NoisyExamples.negativePart S L = F := by
      ext x
      have hx :
          x ∈ (↑S : Set α) \ L ↔ x ∈ (↑F : Set α) := by
        rw [hF]
      simpa [GenLimit.NoisyExamples.negativePart] using hx
    simpa [heq] using hcard
  · intro hcard
    refine ⟨GenLimit.NoisyExamples.negativePart S L, ?_, hcard⟩
    ext x
    simp [GenLimit.NoisyExamples.negativePart]

theorem negativePart_card_le_iff_version_inequality
    (S : Finset α) (L : GenLimit.Generic.Language α) (i : ℕ) :
    (GenLimit.NoisyExamples.negativePart S L).card ≤ i ↔
      S.card ≤
        (GenLimit.NoisyExamples.positivePart S L).card + i := by
  classical
  have hsplit :
      (GenLimit.NoisyExamples.positivePart S L).card +
          (GenLimit.NoisyExamples.negativePart S L).card =
        S.card := by
    simpa [GenLimit.NoisyExamples.positivePart,
      GenLimit.NoisyExamples.negativePart] using
      S.filter_card_add_filter_neg_card_eq_card (fun x => x ∈ L)
  omega

/-- Definition 2.8 agrees with the existing finite noisy version space. -/
theorem consistentLanguages_finset_eq_rr
    (C : GenLimit.Generic.LanguageClass α) (S : Finset α) (i : ℕ) :
    consistentLanguages C (↑S : Set α) i =
      GenLimit.NoisyExamples.noisyVersionSpace C S i := by
  ext L
  simp only [consistentLanguages, Set.mem_setOf_eq,
    GenLimit.NoisyExamples.noisyVersionSpace]
  rw [missingAtMost_finset_iff,
    negativePart_card_le_iff_version_inequality]

theorem noisyCommonCore_finset_eq_rr
    (C : GenLimit.Generic.LanguageClass α) (S : Finset α) (i : ℕ) :
    noisyCommonCore C (↑S : Set α) i =
      GenLimit.NoisyExamples.noisyCommonCore C S i := by
  rw [noisyCommonCore, GenLimit.NoisyExamples.noisyCommonCore,
    consistentLanguages_finset_eq_rr]

theorem noisyClosure_finset_eq_rr_commonCore
    (C : GenLimit.Generic.LanguageClass α) (S : Finset α) (i : ℕ)
    (h : (GenLimit.NoisyExamples.noisyVersionSpace C S i).Nonempty) :
    noisyClosure C (↑S : Set α) i =
      GenLimit.NoisyExamples.noisyCommonCore C S i := by
  have h' : (consistentLanguages C (↑S : Set α) i).Nonempty := by
    simpa [consistentLanguages_finset_eq_rr] using h
  rw [noisyClosure_eq_commonCore h',
    noisyCommonCore_finset_eq_rr]

theorem noisyClosureWitnessAt_iff_rr
    (C : GenLimit.Generic.LanguageClass α) (i d : ℕ) :
    NoisyClosureWitnessAt C i d ↔
      GenLimit.NoisyExamples.NoisyClosureWitnessAt C i d := by
  constructor
  · rintro ⟨S, hcard, hnonempty, hfinite⟩
    have hrr :
        (GenLimit.NoisyExamples.noisyVersionSpace C S i).Nonempty := by
      simpa [consistentLanguages_finset_eq_rr] using hnonempty
    refine ⟨S, hcard, hrr, ?_⟩
    simpa [noisyClosure_finset_eq_rr_commonCore C S i hrr] using hfinite
  · rintro ⟨S, hcard, hnonempty, hfinite⟩
    have hpaper : (consistentLanguages C (↑S : Set α) i).Nonempty := by
      simpa [consistentLanguages_finset_eq_rr] using hnonempty
    refine ⟨S, hcard, hpaper, ?_⟩
    simpa [noisyClosure_finset_eq_rr_commonCore C S i hnonempty] using hfinite

/-- Definition 2.12's finiteness assertion is exactly the one already
formalized for Raman--Raman. -/
theorem finiteNoisyClosureDimensionAt_iff_rr
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) :
    FiniteNoisyClosureDimensionAt C i ↔
      GenLimit.NoisyExamples.FiniteNoisyClosureDimensionAt C i := by
  constructor <;>
    rintro ⟨D, hD⟩ <;>
    refine ⟨D, ?_⟩ <;>
    intro d hDd hd
  · exact hD d hDd ((noisyClosureWitnessAt_iff_rr C i d).mpr hd)
  · exact hD d hDd ((noisyClosureWitnessAt_iff_rr C i d).mp hd)

/-- Any Raman--Raman uniform noise-dependent generator works for the paper's
stricter injective enumerations.  The shift from `t` to `t+1` exactly matches
the paper's inclusive history `S_t`. -/
theorem rr_uniform_implies_uniformNoiseDependent
    {C : GenLimit.Generic.LanguageClass α}
    (h : GenLimit.NoisyExamples.UniformNoiseDependentGeneratable C) :
    UniformNoiseDependentGeneratable C := by
  obtain ⟨gen, hgen⟩ := h
  refine ⟨gen, ?_⟩
  intro i
  obtain ⟨d, hd⟩ := hgen i
  refine ⟨d, ?_⟩
  intro L hLC stream henum t hdt
  rw [correctAt_iff_generic]
  apply hd L hLC stream
    (hasNoiseAtMost_of_enumerationWithNoiseAtMost henum)
    d
  · have hsample :
        GenLimit.Generic.sample stream d =
          GenLimit.Generic.sequenceSample
            (fun k : Fin d => stream k) :=
      GenLimit.Generic.sequenceSample_prefix stream d |>.symm
    rw [hsample]
    apply GenLimit.NoisyExamples.sequenceSample_card_of_injective
    intro a b hab
    exact Fin.ext (henum.1 hab)
  · omega

/-- The analogous bridge for non-uniform noise-dependent generation. -/
theorem rr_nonuniform_implies_nonuniformNoiseDependent
    {C : GenLimit.Generic.LanguageClass α}
    (h : GenLimit.NoisyExamples.NonuniformNoiseDependentGeneratable C) :
    NonuniformNoiseDependentGeneratable C := by
  obtain ⟨gen, hgen⟩ := h
  refine ⟨gen, ?_⟩
  intro i L hLC
  obtain ⟨d, hd⟩ := hgen i L hLC
  refine ⟨d, ?_⟩
  intro stream henum t hdt
  rw [correctAt_iff_generic]
  apply hd stream
    (hasNoiseAtMost_of_enumerationWithNoiseAtMost henum)
    d
  · have hsample :
        GenLimit.Generic.sample stream d =
          GenLimit.Generic.sequenceSample
            (fun k : Fin d => stream k) :=
      GenLimit.Generic.sequenceSample_prefix stream d |>.symm
    rw [hsample]
    apply GenLimit.NoisyExamples.sequenceSample_card_of_injective
    intro a b hab
    exact Fin.ext (henum.1 hab)
  · omega

/-- Reuse of Raman--Raman Theorem 3.3: finite noisy closure dimensions at all
levels suffice for the exact injective-enumeration Definition 2.6. -/
theorem finite_dimensions_imply_uniformNoiseDependent
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt C i) :
    UniformNoiseDependentGeneratable C := by
  apply rr_uniform_implies_uniformNoiseDependent
  apply GenLimit.NoisyExamples.finite_noisyClosureDimensions_imply_uniform_noiseDependent
  intro i
  exact (finiteNoisyClosureDimensionAt_iff_rr C i).mp (hdim i)

end GenLimit.QuantifyingNoise
