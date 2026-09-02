import GenLimit.Paper19_EffectOfNoise.Bridges
import GenLimit.Paper06_NoisyExamples.FiniteUnionLimit
import GenLimit.Support.PrefixCompletion

/-!
# Quantifying Noise: the fixed-level characterization

This file formalizes Lemma 3.1 of Li--Zhang,
*Characterizing the Effect of Noise in Language Generation in the Limit*,
arXiv:2601.21237v2.

The source assumes throughout that every language is infinite.  That
assumption is needed in the necessity direction: a finite adversarial prefix
must be extendible to an injective infinite enumeration of the selected
target.  The construction below supplies that continuation explicitly.

The paper numbers the observations `x₀, ..., x_t` inclusively.  Consequently
a prefix containing `m` values is tested at paper time `m - 1`, while the
generic Lean generator receives a history of length `m`.
-/

namespace GenLimit.QuantifyingNoise

/-- The standing assumption from the paper's preliminaries: every member of
the collection is an infinite language. -/
def AllLanguagesInfinite
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ C → L.Infinite

/-! ## The closure generator -/

/-- At a finite history, choose a fresh point of the fixed-level noisy
closure when one exists, and use an arbitrary fallback otherwise. -/
noncomputable def fixedLevelClosureGenerator [Nonempty α]
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) :
    GenLimit.Generic.Generator α :=
  fun _ xs => by
    classical
    let S := GenLimit.Generic.sequenceSample xs
    let fresh := noisyClosure C (↑S : Set α) i \ (S : Set α)
    exact if h : fresh.Nonempty then Classical.choose h
      else Classical.choice inferInstance

theorem fixedLevelClosureGenerator_spec [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α} {i t : ℕ}
    {xs : Fin t → α}
    (h : (noisyClosure C
        (↑(GenLimit.Generic.sequenceSample xs) : Set α) i \
          (GenLimit.Generic.sequenceSample xs : Set α)).Nonempty) :
    fixedLevelClosureGenerator C i t xs ∈
        noisyClosure C
          (↑(GenLimit.Generic.sequenceSample xs) : Set α) i \
            (GenLimit.Generic.sequenceSample xs : Set α) := by
  classical
  simp only [fixedLevelClosureGenerator]
  exact dif_pos h ▸ Classical.choose_spec h

theorem observed_missingAtMost_of_enumeration
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i t : ℕ}
    (henum : EnumerationWithNoiseAtMost stream L i) :
    MissingAtMost (↑(observed stream t) : Set α) L i := by
  classical
  rw [missingAtMost_finset_iff]
  obtain ⟨F, hF, hFcard⟩ := henum.2.2
  have hsub :
      GenLimit.NoisyExamples.negativePart (observed stream t) L ⊆ F := by
    intro x hx
    simp only [GenLimit.NoisyExamples.negativePart,
      Finset.mem_filter] at hx
    have hxrange : x ∈ Set.range stream := by
      obtain ⟨n, _hnt, hn⟩ :=
        GenLimit.Generic.mem_sample_iff.mp
          (show x ∈ GenLimit.Generic.sample stream (t + 1) from hx.1)
      exact ⟨n, hn⟩
    have hxdiff : x ∈ Set.range stream \ L := ⟨hxrange, hx.2⟩
    have hxF : x ∈ (↑F : Set α) := by
      rw [hF]
      exact hxdiff
    exact hxF
  exact (Finset.card_le_card hsub).trans hFcard

theorem target_mem_consistentLanguages_observed
    {C : GenLimit.Generic.LanguageClass α}
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i t : ℕ}
    (hLC : L ∈ C) (henum : EnumerationWithNoiseAtMost stream L i) :
    L ∈ consistentLanguages C (↑(observed stream t) : Set α) i :=
  ⟨hLC, observed_missingAtMost_of_enumeration henum⟩

/-- Sufficiency in Lemma 3.1, with the paper's inclusive time convention.
If `D` bounds all finite-closure witnesses, then paper time `D` already
contains `D + 1` distinct examples. -/
theorem finite_dimension_implies_uniform_fixed_level [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hdim : FiniteNoisyClosureDimensionAt C i) :
    UniformGeneratableAtNoiseLevel C i := by
  classical
  obtain ⟨D, hD⟩ := hdim
  refine ⟨fixedLevelClosureGenerator C i, D, ?_⟩
  intro L hLC stream henum t hDt
  have htarget :
      L ∈ consistentLanguages C (↑(observed stream t) : Set α) i :=
    target_mem_consistentLanguages_observed hLC henum
  have hversion :
      (consistentLanguages C (↑(observed stream t) : Set α) i).Nonempty :=
    ⟨L, htarget⟩
  have hcard : (observed stream t).card = t + 1 :=
    observed_card_of_injective henum.1 t
  have hclosureInfinite :
      (noisyClosure C (↑(observed stream t) : Set α) i).Infinite := by
    by_contra hnot
    have hfinite :
        (noisyClosure C (↑(observed stream t) : Set α) i).Finite :=
      Set.not_infinite.mp hnot
    apply hD (t + 1)
    · omega
    · exact ⟨observed stream t, hcard, hversion, hfinite⟩
  have hfresh :
      (noisyClosure C (↑(observed stream t) : Set α) i \
        (observed stream t : Set α)).Nonempty :=
    (hclosureInfinite.diff (observed stream t).finite_toSet).nonempty
  have hprefix :
      GenLimit.Generic.sequenceSample
          (fun k : Fin (t + 1) => stream k) =
        observed stream t := by
    exact (observed_eq_sequenceSample stream t).symm
  have hchoice :=
    fixedLevelClosureGenerator_spec
      (C := C) (i := i)
      (xs := fun k : Fin (t + 1) => stream k)
      (by simpa [hprefix] using hfresh)
  rw [CorrectAt, outputAt, observed, fixedLevelClosureGenerator]
  change
    fixedLevelClosureGenerator C i (t + 1)
        (fun k : Fin (t + 1) => stream k) ∈ L ∧
      fixedLevelClosureGenerator C i (t + 1)
        (fun k : Fin (t + 1) => stream k) ∉
          GenLimit.Generic.sample stream (t + 1)
  rw [hprefix] at hchoice
  exact ⟨lemma_2_11 htarget hchoice.1, hchoice.2⟩

/-! ## Extending a finite adversarial prefix injectively -/

/-- Prepend every element of `P`, without repetition, and then enumerate the
remaining target `L \ P`, also without repetition. -/
private theorem finsetPrefix_rest_infinite
    (P : Finset α) (L : Set α)
    (hrest : (L \ (P : Set α)).Infinite) :
    (L \ (GenLimit.Generic.sequenceSample
      (fun k : Fin P.card => (P.equivFin.symm k).1) : Set α)).Infinite := by
  rw [GenLimit.NoisyExamples.sequenceSample_equivFin_symm P]
  exact hrest

noncomputable def prefixThenInjectiveTarget [Countable α]
    (P : Finset α) (L : Set α)
    (hrest : (L \ (P : Set α)).Infinite) :
    GenLimit.Generic.Stream α :=
  GenLimit.Support.prefixThenTarget
    (fun k : Fin P.card => (P.equivFin.symm k).1) L
    (finsetPrefix_rest_infinite P L hrest)

theorem prefixThenInjectiveTarget_prefix [Countable α]
    (P : Finset α) (L : Set α)
    (hrest : (L \ (P : Set α)).Infinite)
    {n : ℕ} (hn : n < P.card) :
    prefixThenInjectiveTarget P L hrest n =
      (P.equivFin.symm ⟨n, hn⟩).1 := by
  simpa [prefixThenInjectiveTarget] using
    (GenLimit.Support.prefixThenTarget_prefix
      (fun k : Fin P.card => (P.equivFin.symm k).1) L
      (finsetPrefix_rest_infinite P L hrest) ⟨n, hn⟩)

theorem prefixThenInjectiveTarget_injective [Countable α]
    (P : Finset α) (L : Set α)
    (hrest : (L \ (P : Set α)).Infinite) :
    Function.Injective (prefixThenInjectiveTarget P L hrest) := by
  apply GenLimit.Support.prefixThenTarget_injective
  exact GenLimit.NoisyExamples.equivFin_symm_value_injective P

theorem range_prefixThenInjectiveTarget [Countable α]
    (P : Finset α) (L : Set α)
    (hrest : (L \ (P : Set α)).Infinite) :
    Set.range (prefixThenInjectiveTarget P L hrest) =
      (P : Set α) ∪ L := by
  simpa [prefixThenInjectiveTarget,
    GenLimit.NoisyExamples.sequenceSample_equivFin_symm P] using
    (GenLimit.Support.range_prefixThenTarget_eq_prefix_union
      (fun k : Fin P.card => (P.equivFin.symm k).1) L
      (finsetPrefix_rest_infinite P L hrest))

theorem sample_prefixThenInjectiveTarget [Countable α]
    (P : Finset α) (L : Set α)
    (hrest : (L \ (P : Set α)).Infinite) :
    GenLimit.Generic.sample
        (prefixThenInjectiveTarget P L hrest) P.card = P := by
  simpa [prefixThenInjectiveTarget,
    GenLimit.NoisyExamples.sequenceSample_equivFin_symm P] using
    (GenLimit.Support.prefixThenTarget_sample
      (fun k : Fin P.card => (P.equivFin.symm k).1) L
      (finsetPrefix_rest_infinite P L hrest))

theorem prefixThenInjectiveTarget_enumerates [Countable α]
    (P : Finset α) (L : Set α)
    (hL : L.Infinite)
    {i : ℕ}
    (hnoise : MissingAtMost (P : Set α) L i) :
    EnumerationWithNoiseAtMost
      (prefixThenInjectiveTarget P L (hL.diff P.finite_toSet)) L i := by
  let hrest : (L \ (P : Set α)).Infinite := hL.diff P.finite_toSet
  refine ⟨prefixThenInjectiveTarget_injective P L hrest, ?_, ?_⟩
  · rw [range_prefixThenInjectiveTarget P L hrest]
    exact Set.subset_union_right
  · change MissingAtMost
      (Set.range (prefixThenInjectiveTarget P L hrest)) L i
    rw [range_prefixThenInjectiveTarget P L hrest]
    obtain ⟨F, hF, hcard⟩ := hnoise
    refine ⟨F, ?_, hcard⟩
    calc
      (↑F : Set α) = (P : Set α) \ L := hF
      _ = ((P : Set α) ∪ L) \ L := by
        ext x
        simp only [Set.mem_diff, Set.mem_union]
        aesop

/-! ## Necessity -/

theorem arbitrarily_large_witness_of_not_finite_dimension
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hnot : ¬FiniteNoisyClosureDimensionAt C i) :
    ∀ D, ∃ d, D < d ∧ NoisyClosureWitnessAt C i d := by
  intro D
  by_contra hnone
  apply hnot
  refine ⟨D, ?_⟩
  intro d hDd hwit
  exact hnone ⟨d, hDd, hwit⟩

theorem consistentLanguages_eq_of_between_closure
    {C : GenLimit.Generic.LanguageClass α}
    {S P : Finset α} {i : ℕ}
    (hSP : S ⊆ P)
    (hPSclosure :
      (P : Set α) ⊆
        (S : Set α) ∪ noisyClosure C (↑S : Set α) i) :
    consistentLanguages C (↑P : Set α) i =
      consistentLanguages C (↑S : Set α) i := by
  classical
  apply Set.Subset.antisymm
  · rintro L ⟨hLC, hmissing⟩
    refine ⟨hLC, (missingAtMost_finset_iff S L i).mpr ?_⟩
    have hsub :
        GenLimit.NoisyExamples.negativePart S L ⊆
          GenLimit.NoisyExamples.negativePart P L := by
      intro x hx
      simp only [GenLimit.NoisyExamples.negativePart,
        Finset.mem_filter] at hx ⊢
      exact ⟨hSP hx.1, hx.2⟩
    exact (Finset.card_le_card hsub).trans
      ((missingAtMost_finset_iff P L i).mp hmissing)
  · rintro L hL
    refine ⟨hL.1, (missingAtMost_finset_iff P L i).mpr ?_⟩
    have heq :
        GenLimit.NoisyExamples.negativePart P L =
          GenLimit.NoisyExamples.negativePart S L := by
      ext x
      simp only [GenLimit.NoisyExamples.negativePart,
        Finset.mem_filter]
      constructor
      · rintro ⟨hxP, hxnotL⟩
        rcases hPSclosure hxP with hxS | hxclosure
        · exact ⟨hxS, hxnotL⟩
        · exact (hxnotL (lemma_2_11 hL hxclosure)).elim
      · rintro ⟨hxS, hxnotL⟩
        exact ⟨hSP hxS, hxnotL⟩
    rw [heq]
    exact (missingAtMost_finset_iff S L i).mp hL.2

/-- Necessity in Lemma 3.1.  The proof is the paper's finite-core
adversary, with its claimed finite prefix extended here to a genuine
injective infinite noisy enumeration. -/
theorem uniform_fixed_level_implies_finite_dimension [Countable α]
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hInfinite : AllLanguagesInfinite C)
    (hgen : UniformGeneratableAtNoiseLevel C i) :
    FiniteNoisyClosureDimensionAt C i := by
  classical
  obtain ⟨gen, T, hT⟩ := hgen
  by_contra hnot
  obtain ⟨d, hTd, S, hScard, hversion, hclosureFinite⟩ :=
    arbitrarily_large_witness_of_not_finite_dimension hnot T
  let closureFinset := hclosureFinite.toFinset
  let P := S ∪ closureFinset
  have hSP : S ⊆ P := Finset.subset_union_left
  have hP_between :
      (P : Set α) ⊆
        (S : Set α) ∪ noisyClosure C (↑S : Set α) i := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxclosure
    · exact Or.inl hxS
    · exact Or.inr (by
        simpa [closureFinset] using hxclosure)
  have hPcard : T < P.card := by
    exact hTd.trans_le
      (by simpa [hScard] using Finset.card_le_card hSP)
  have hPpos : 0 < P.card := lt_of_le_of_lt (Nat.zero_le T) hPcard
  let xs : Fin P.card → α := fun k =>
    (P.equivFin.symm k).1
  have hxsInjective : Function.Injective xs := by
    intro a b hab
    have hsub :
        P.equivFin.symm a = P.equivFin.symm b :=
      Subtype.ext hab
    exact P.equivFin.symm.injective hsub
  have hsample : GenLimit.Generic.sequenceSample xs = P := by
    simpa [xs] using
      GenLimit.NoisyExamples.sequenceSample_equivFin_symm P
  let y := gen P.card xs
  have hclosureSubP :
      noisyClosure C (↑S : Set α) i ⊆ (P : Set α) := by
    intro x hx
    have hxC : x ∈ closureFinset := by
      simpa [closureFinset] using hx
    exact Finset.mem_union_right S hxC
  obtain ⟨L, hLS, hybad⟩ :
      ∃ L, L ∈ consistentLanguages C (↑S : Set α) i ∧
        (y ∉ L ∨ y ∈ P) := by
    by_cases hyP : y ∈ P
    · obtain ⟨L, hLS⟩ := hversion
      exact ⟨L, hLS, Or.inr hyP⟩
    · have hynotClosure : y ∉ noisyClosure C (↑S : Set α) i := by
        intro hy
        exact hyP (hclosureSubP hy)
      rw [noisyClosure_eq_commonCore hversion] at hynotClosure
      simp only [noisyCommonCore, Set.mem_setOf_eq, not_forall] at hynotClosure
      obtain ⟨L, hLS, hyL⟩ := hynotClosure
      exact ⟨L, hLS, Or.inl hyL⟩
  have hversionP :
      consistentLanguages C (↑P : Set α) i =
        consistentLanguages C (↑S : Set α) i := by
    exact
      consistentLanguages_eq_of_between_closure
        (C := C) (S := S) (P := P) (i := i) hSP hP_between
  have hLP : L ∈ consistentLanguages C (↑P : Set α) i := by
    rw [hversionP]
    exact hLS
  have hLinf : L.Infinite := hInfinite L hLS.1
  let hrest : (L \ (P : Set α)).Infinite := hLinf.diff P.finite_toSet
  let stream :=
    prefixThenInjectiveTarget P L hrest
  have henum : EnumerationWithNoiseAtMost stream L i := by
    exact prefixThenInjectiveTarget_enumerates P L hLinf hLP.2
  let t := P.card - 1
  have htSucc : t + 1 = P.card := by
    dsimp [t]
    omega
  have hTt : T ≤ t := by
    dsimp [t]
    omega
  have houtAtCard :
      gen P.card (fun k : Fin P.card => stream k) =
        gen P.card xs := by
    apply congrArg (gen P.card)
    funext k
    rw [show stream k = prefixThenInjectiveTarget P L hrest k from rfl,
      prefixThenInjectiveTarget_prefix P L hrest k.isLt]
  have hout : outputAt gen stream t = y := by
    unfold outputAt
    rw [htSucc]
    exact houtAtCard
  have hcorrect := hT L hLS.1 stream henum t hTt
  rw [CorrectAt, hout] at hcorrect
  rcases hybad with hyL | hyP
  · exact hyL hcorrect.1
  · exact hcorrect.2 (by
      have hpref :
          GenLimit.Generic.sample stream P.card = P :=
        sample_prefixThenInjectiveTarget P L hrest
      unfold observed
      rw [htSucc, hpref]
      exact hyP)

/-- Lemma 3.1 in the paper's exact fixed-level model. -/
theorem lemma_3_1 [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hInfinite : AllLanguagesInfinite C) :
    UniformGeneratableAtNoiseLevel C i ↔
      FiniteNoisyClosureDimensionAt C i := by
  constructor
  · exact uniform_fixed_level_implies_finite_dimension hInfinite
  · exact finite_dimension_implies_uniform_fixed_level

end GenLimit.QuantifyingNoise
