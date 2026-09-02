import GenLimit.Paper19_EffectOfNoise.Definitions

/-!
# Quantifying Noise: noisy closure

Source: *Characterizing the Effect of Noise on Language Generation*,
arXiv:2601.21237v2, Definitions 2.8--2.12 and Lemmas 2.10--2.13.

The paper defines the closure itself to be the empty set when there is no
consistent language.  This differs intentionally from the `Option`-valued
Raman--Raman implementation and is bridged in `Bridges.lean`.
-/

namespace GenLimit.QuantifyingNoise

/-- Definition 2.8: languages missing at most `i` elements of `S`. -/
def consistentLanguages
    (C : GenLimit.Generic.LanguageClass α) (S : Set α) (i : ℕ) :
    Set (GenLimit.Generic.Language α) :=
  {L | L ∈ C ∧ MissingAtMost S L i}

/-- The intersection of every language consistent at level `i`. -/
def noisyCommonCore
    (C : GenLimit.Generic.LanguageClass α) (S : Set α) (i : ℕ) :
    GenLimit.Generic.Language α :=
  {x | ∀ L, L ∈ consistentLanguages C S i → x ∈ L}

/-- Definition 2.9, including its literal empty-version-space convention. -/
noncomputable def noisyClosure
    (C : GenLimit.Generic.LanguageClass α) (S : Set α) (i : ℕ) :
    GenLimit.Generic.Language α := by
  classical
  exact if (consistentLanguages C S i).Nonempty then
    noisyCommonCore C S i
  else ∅

theorem consistentLanguages_mono_noise
    {C : GenLimit.Generic.LanguageClass α} {S : Set α} {i j : ℕ}
    (hij : i ≤ j) :
    consistentLanguages C S i ⊆ consistentLanguages C S j := by
  rintro L ⟨hLC, hmissing⟩
  exact ⟨hLC, missingAtMost_mono hij hmissing⟩

theorem noisyClosure_eq_empty_of_not_nonempty
    {C : GenLimit.Generic.LanguageClass α} {S : Set α} {i : ℕ}
    (h : ¬(consistentLanguages C S i).Nonempty) :
    noisyClosure C S i = ∅ := by
  classical
  simp [noisyClosure, h]

theorem noisyClosure_eq_commonCore
    {C : GenLimit.Generic.LanguageClass α} {S : Set α} {i : ℕ}
    (h : (consistentLanguages C S i).Nonempty) :
    noisyClosure C S i = noisyCommonCore C S i := by
  classical
  simp [noisyClosure, h]

/-- The useful nonempty-version-space form of Lemma 2.10. -/
theorem noisyClosure_mono_of_consistent_nonempty
    {C : GenLimit.Generic.LanguageClass α} {S : Set α} {i j : ℕ}
    (hij : i ≤ j) (hi : (consistentLanguages C S i).Nonempty) :
    noisyClosure C S j ⊆ noisyClosure C S i := by
  have hj : (consistentLanguages C S j).Nonempty :=
    hi.mono (consistentLanguages_mono_noise hij)
  rw [noisyClosure_eq_commonCore hj, noisyClosure_eq_commonCore hi]
  intro x hx L hLi
  exact hx L (consistentLanguages_mono_noise hij hLi)

/-- Lemma 2.10: increasing the allowed noise can only shrink the closure,
unless the lower-level version space was empty (and hence its closure is
empty by convention). -/
theorem lemma_2_10
    (C : GenLimit.Generic.LanguageClass α)
    (S : Set α) {i j : ℕ} (hij : i ≤ j) :
    noisyClosure C S i = ∅ ∨
      noisyClosure C S j ⊆ noisyClosure C S i := by
  by_cases hi : (consistentLanguages C S i).Nonempty
  · exact Or.inr (noisyClosure_mono_of_consistent_nonempty hij hi)
  · exact Or.inl (noisyClosure_eq_empty_of_not_nonempty hi)

/-- Lemma 2.11: the noisy closure is safe for every consistent target. -/
theorem lemma_2_11
    {C : GenLimit.Generic.LanguageClass α} {S : Set α} {i : ℕ}
    {L : GenLimit.Generic.Language α}
    (hL : L ∈ consistentLanguages C S i) :
    noisyClosure C S i ⊆ L := by
  have hnonempty : (consistentLanguages C S i).Nonempty := ⟨L, hL⟩
  rw [noisyClosure_eq_commonCore hnonempty]
  intro x hx
  exact hx L hL

/-- A size-`d` witness in Definition 2.12. -/
def NoisyClosureWitnessAt
    (C : GenLimit.Generic.LanguageClass α) (i d : ℕ) : Prop :=
  ∃ S : Finset α, S.card = d ∧
    (consistentLanguages C (↑S : Set α) i).Nonempty ∧
    (noisyClosure C (↑S : Set α) i).Finite

/-- The assertion `NC_i(C) < ∞` without assigning an artificial value when
witness sizes have gaps. -/
def FiniteNoisyClosureDimensionAt
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) : Prop :=
  ∃ D : ℕ, ∀ d : ℕ, D < d → ¬NoisyClosureWitnessAt C i d

/-- Witness form of Lemma 2.13. -/
theorem noisyClosureWitnessAt_mono
    {C : GenLimit.Generic.LanguageClass α} {i j d : ℕ} (hij : i ≤ j)
    (h : NoisyClosureWitnessAt C i d) :
    NoisyClosureWitnessAt C j d := by
  obtain ⟨S, hcard, hi, hfinite⟩ := h
  have hj : (consistentLanguages C (↑S : Set α) j).Nonempty :=
    hi.mono (consistentLanguages_mono_noise hij)
  refine ⟨S, hcard, hj, ?_⟩
  exact hfinite.subset (noisyClosure_mono_of_consistent_nonempty hij hi)

/-- Finiteness form of Lemma 2.13 (`NC_i(C) ≤ NC_j(C)`). -/
theorem finiteNoisyClosureDimensionAt_anti
    {C : GenLimit.Generic.LanguageClass α} {i j : ℕ} (hij : i ≤ j)
    (hj : FiniteNoisyClosureDimensionAt C j) :
    FiniteNoisyClosureDimensionAt C i := by
  obtain ⟨D, hD⟩ := hj
  refine ⟨D, ?_⟩
  intro d hDd hi
  exact hD d hDd (noisyClosureWitnessAt_mono hij hi)

end GenLimit.QuantifyingNoise
