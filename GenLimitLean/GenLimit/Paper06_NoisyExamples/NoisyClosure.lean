import GenLimit.Paper06_NoisyExamples.UniformIndependent
import Mathlib.Data.Finset.Max

/-!
# #06 Noisy Examples: noisy closure and uniform noise-dependent generation

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Definition 2.5, Definition 3.2, and
Theorem 3.3.

The paper identifies a hypothesis with its support.  A finite set `S`
represents the distinct sequence in Definition 3.2.  Thus
`noisyVersionSpace H S n` consists of the members of `H` that omit at most
`n` elements of `S`, and `noisyClosure` uses `none` for the paper's `bot`.

`FiniteNoisyClosureDimensionAt H n` is the literal finiteness assertion
`NC_n(H) < infinity`: there is a bound beyond which no distinct finite
sequence has a non-bottom finite noisy closure.  It deliberately does not
assign an arbitrary numerical value to the dimension when the set of
witness sizes has gaps.

Paper natural numbers are represented by Lean naturals, including noise
level zero.  The paper's displayed algorithm uses `0` both as a possible
noise level and as a sentinel.  `eligibleNoiseLevels` instead branches on
nonemptiness of the candidate set, which is the same construction for the
paper's positive-natural convention and also handles zero noise correctly.
-/

namespace GenLimit.NoisyExamples

theorem noisyClosure_eq_none_iff
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ} :
    noisyClosure H S n = none ↔ ¬(noisyVersionSpace H S n).Nonempty := by
  classical
  simp [noisyClosure]

theorem noisyClosure_eq_some_iff
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ}
    {C : GenLimit.Generic.Language α} :
    noisyClosure H S n = some C ↔
      (noisyVersionSpace H S n).Nonempty ∧ C = noisyCommonCore H S n := by
  classical
  constructor
  · intro hcl
    by_cases hVS : (noisyVersionSpace H S n).Nonempty
    · refine ⟨hVS, ?_⟩
      have hc : noisyCommonCore H S n = C := by
        simpa [noisyClosure, hVS] using hcl
      exact hc.symm
    · simp [noisyClosure, hVS] at hcl
  · rintro ⟨hVS, rfl⟩
    simp [noisyClosure, hVS]

theorem noisyCommonCore_subset_of_mem_versionSpace
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ}
    {L : GenLimit.Generic.Language α}
    (hL : L ∈ noisyVersionSpace H S n) :
    noisyCommonCore H S n ⊆ L := by
  intro x hx
  exact hx L hL

/-- The finset formulation is equivalent to the paper's formulation by an
injective sequence of `d` distinct examples. -/
theorem noisyClosureWitnessAt_iff_injective_sequence
    {H : GenLimit.Generic.LanguageClass α} {n d : ℕ} :
    NoisyClosureWitnessAt H n d ↔
      ∃ xs : Fin d → α, Function.Injective xs ∧
        (noisyVersionSpace H (GenLimit.Generic.sequenceSample xs) n).Nonempty ∧
        (noisyCommonCore H (GenLimit.Generic.sequenceSample xs) n).Finite := by
  classical
  constructor
  · rintro ⟨S, hScard, hVS, hcore⟩
    let xs : Fin d → α := fun i => ((S.equivFinOfCardEq hScard).symm i).1
    have hxs : Function.Injective xs := by
      intro i j hij
      apply (S.equivFinOfCardEq hScard).symm.injective
      exact Subtype.ext hij
    have hsample : GenLimit.Generic.sequenceSample xs = S := by
      simpa [xs] using sequenceSample_equivFinOfCardEq_symm S hScard
    exact ⟨xs, hxs, hsample.symm ▸ hVS, hsample.symm ▸ hcore⟩
  · rintro ⟨xs, hxs, hVS, hcore⟩
    refine ⟨GenLimit.Generic.sequenceSample xs, ?_, hVS, hcore⟩
    exact sequenceSample_card_of_injective xs hxs

/-- A bound formulation of finite noisy closure dimension, used directly by
the generator in the sufficiency proof of Theorem 3.3. -/
theorem finiteNoisyClosureDimensionAt_iff_eventually_infinite
    {H : GenLimit.Generic.LanguageClass α} {n : ℕ} :
    FiniteNoisyClosureDimensionAt H n ↔
      ∃ D : ℕ, ∀ S : Finset α, D < S.card →
        (noisyVersionSpace H S n).Nonempty →
        (noisyCommonCore H S n).Infinite := by
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨D, ?_⟩
    intro S hDS hVS
    by_contra hnot
    have hfinite : (noisyCommonCore H S n).Finite := Set.not_infinite.mp hnot
    exact hD S.card hDS ⟨S, rfl, hVS, hfinite⟩
  · rintro ⟨D, hD⟩
    refine ⟨D, ?_⟩
    intro d hDd hwit
    obtain ⟨S, hcard, hVS, hfinite⟩ := hwit
    have hinfinite : (noisyCommonCore H S n).Infinite := by
      apply hD S
      · simpa [hcard]
      · exact hVS
    exact hinfinite hfinite

theorem hasNoiseAtMost_mono
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {m n : ℕ}
    (hmn : m ≤ n) (hnoise : HasNoiseAtMost stream L m) :
    HasNoiseAtMost stream L n :=
  GenLimit.Generic.violationsAtMost_mono hmn hnoise

theorem bad_sample_card_le_noise
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {n t : ℕ}
    (hnoise : HasNoiseAtMost stream L n) :
    (negativePart (GenLimit.Generic.sample stream t) L).card ≤ n := by
  classical
  obtain ⟨F, hFcard, hF⟩ :=
    (GenLimit.Generic.violationsAtMost_iff_exists_finset
      stream (fun x => x ∈ L) n).mp hnoise
  have hsub :
      negativePart (GenLimit.Generic.sample stream t) L ⊆
        F.image stream := by
    intro x hx
    simp only [negativePart, Finset.mem_filter] at hx
    obtain ⟨i, hi, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hx.1
    exact Finset.mem_image.mpr ⟨i, (hF i).mpr hx.2, rfl⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le (s := F) (f := stream)).trans hFcard)

/-- A target with at most `n` noisy occurrences belongs to the noisy version
space of every observed distinct sample. -/
theorem target_mem_noisyVersionSpace
    {H : GenLimit.Generic.LanguageClass α}
    {L : GenLimit.Generic.Language α} (hLH : L ∈ H)
    {stream : GenLimit.Generic.Stream α} {n t : ℕ}
    (hnoise : HasNoiseAtMost stream L n) :
    L ∈ noisyVersionSpace H (GenLimit.Generic.sample stream t) n := by
  classical
  refine ⟨hLH, ?_⟩
  let S := GenLimit.Generic.sample stream t
  change S.card ≤ (positivePart S L).card + n
  have hbad : (negativePart S L).card ≤ n :=
    bad_sample_card_le_noise hnoise
  have hsplit :
      (positivePart S L).card + (negativePart S L).card = S.card := by
    simpa [positivePart, negativePart] using
      S.filter_card_add_filter_neg_card_eq_card (fun x => x ∈ L)
  omega

theorem negativePart_card_le_of_mem_noisyVersionSpace
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ}
    {L : GenLimit.Generic.Language α}
    (hL : L ∈ noisyVersionSpace H S n) :
    (negativePart S L).card ≤ n := by
  classical
  have hsplit :
      (positivePart S L).card + (negativePart S L).card = S.card := by
    simpa [positivePart, negativePart] using
      S.filter_card_add_filter_neg_card_eq_card (fun x => x ∈ L)
  exact Nat.le_of_add_le_add_left (hsplit.symm ▸ hL.2)

/-- A finite injective prefix followed by a positive constant tail has at
most as many noisy occurrences as there are negative values in the prefix. -/
theorem hasNoiseAtMost_prefixThen
    {m n : ℕ} {xs : Fin m → α} (hxs : Function.Injective xs)
    {tail : α} {L : GenLimit.Generic.Language α} (htail : tail ∈ L)
    (hbad :
      (negativePart (GenLimit.Generic.sequenceSample xs) L).card ≤ n) :
    HasNoiseAtMost (prefixThen xs tail) L n := by
  classical
  let stream := prefixThen xs tail
  let F := (Finset.range m).filter fun t => stream t ∉ L
  have hstream_inj :
      ∀ a ∈ F, ∀ b ∈ F, stream a = stream b → a = b := by
    intro a ha b hb hab
    have ham : a < m := (Finset.mem_filter.mp ha).1 |> Finset.mem_range.mp
    have hbm : b < m := (Finset.mem_filter.mp hb).1 |> Finset.mem_range.mp
    have hab' : xs ⟨a, ham⟩ = xs ⟨b, hbm⟩ := by
      simpa [stream, prefixThen, ham, hbm] using hab
    have hfin : (⟨a, ham⟩ : Fin m) = ⟨b, hbm⟩ := hxs hab'
    exact congrArg Fin.val hfin
  have himage : F.image stream =
      negativePart (GenLimit.Generic.sequenceSample xs) L := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hiF, hix⟩ := Finset.mem_image.mp hx
      have hi := Finset.mem_filter.mp hiF
      have him : i < m := Finset.mem_range.mp hi.1
      have hsx : stream i = xs ⟨i, him⟩ := by
        simp [stream, prefixThen, him]
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact GenLimit.Generic.mem_sequenceSample_iff.mpr
          ⟨⟨i, him⟩, hsx.symm.trans hix⟩
      · exact hix ▸ hi.2
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      obtain ⟨i, hix⟩ := GenLimit.Generic.mem_sequenceSample_iff.mp hx'.1
      refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
        simpa [stream, prefixThen, i.isLt, hix] using hx'.2
      · simpa [stream, prefixThen, i.isLt] using hix
  have hFcard : F.card ≤ n := by
    have hcard : (F.image stream).card = F.card :=
      Finset.card_image_iff.mpr hstream_inj
    rw [← hcard, himage]
    exact hbad
  apply (GenLimit.Generic.violationsAtMost_iff_exists_finset
    stream (fun x => x ∈ L) n).mpr
  refine ⟨F, hFcard, ?_⟩
  intro t
  constructor
  · intro ht
    exact (Finset.mem_filter.mp ht).2
  · intro htbad
    apply Finset.mem_filter.mpr
    refine ⟨?_, htbad⟩
    apply Finset.mem_range.mpr
    by_contra htm
    have hmt : m ≤ t := Nat.le_of_not_gt htm
    simp only [stream, prefixThen, dif_neg (Nat.not_lt.mpr hmt)] at htbad
    exact htbad htail

/-! ## Constructive sufficiency in Theorem 3.3 -/

/-- A chosen upper bound on the `n`-noisy closure dimension. -/
noncomputable def noisyClosureBound
    (H : GenLimit.Generic.LanguageClass α)
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n)
    (n : ℕ) : ℕ :=
  Classical.choose
    (finiteNoisyClosureDimensionAt_iff_eventually_infinite.mp (hdim n))

theorem noisyClosureBound_spec
    {H : GenLimit.Generic.LanguageClass α}
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n)
    (n : ℕ) (S : Finset α)
    (hlarge : noisyClosureBound H hdim n < S.card)
    (hVS : (noisyVersionSpace H S n).Nonempty) :
    (noisyCommonCore H S n).Infinite := by
  exact Classical.choose_spec
    (finiteNoisyClosureDimensionAt_iff_eventually_infinite.mp (hdim n))
    S hlarge hVS

/-- The finite set of noise levels considered at a history.  Requiring the
version space to be nonempty only makes the generator total on arbitrary
histories; on every stream covered by Definition 2.5, the target witnesses
this condition for all selected levels at least as large as the true noise. -/
noncomputable def eligibleNoiseLevels
    (H : GenLimit.Generic.LanguageClass α)
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n)
    (S : Finset α) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t + 1)).filter fun n =>
    noisyClosureBound H hdim n < S.card ∧
      (noisyVersionSpace H S n).Nonempty

theorem mem_eligibleNoiseLevels_iff
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    {S : Finset α} {t n : ℕ} :
    n ∈ eligibleNoiseLevels H hdim S t ↔
      n ≤ t ∧ noisyClosureBound H hdim n < S.card ∧
        (noisyVersionSpace H S n).Nonempty := by
  classical
  simp [eligibleNoiseLevels, Nat.lt_succ_iff]

/-- The largest eligible noise level at this history.  This definition is
only used with a proof that the eligible set is nonempty. -/
noncomputable def selectedNoiseLevel
    (H : GenLimit.Generic.LanguageClass α)
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n)
    (S : Finset α) (t : ℕ)
    (hE : (eligibleNoiseLevels H hdim S t).Nonempty) : ℕ :=
  (eligibleNoiseLevels H hdim S t).max' hE

theorem selectedNoiseLevel_mem
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    {S : Finset α} {t : ℕ}
    (hE : (eligibleNoiseLevels H hdim S t).Nonempty) :
    selectedNoiseLevel H hdim S t hE ∈
      eligibleNoiseLevels H hdim S t := by
  exact Finset.max'_mem _ _

theorem le_selectedNoiseLevel
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    {S : Finset α} {t n : ℕ}
    (hn : n ∈ eligibleNoiseLevels H hdim S t)
    (hE : (eligibleNoiseLevels H hdim S t).Nonempty) :
    n ≤ selectedNoiseLevel H hdim S t hE := by
  exact Finset.le_max' _ _ hn

/-- Choose a point from an infinite noisy core outside the finite history. -/
noncomputable def freshFromNoisyCore
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) (n : ℕ)
    (hcore : (noisyCommonCore H S n).Infinite) : α :=
  Classical.choose (hcore.diff S.finite_toSet).nonempty

theorem freshFromNoisyCore_spec
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ}
    (hcore : (noisyCommonCore H S n).Infinite) :
    freshFromNoisyCore H S n hcore ∈
      noisyCommonCore H S n \ (S : Set α) := by
  exact Classical.choose_spec (hcore.diff S.finite_toSet).nonempty

/-- The history-level output in the constructive proof of Theorem 3.3. -/
noncomputable def noisyClosureStrategyOutput [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n)
    (S : Finset α) (t : ℕ) : α := by
  classical
  let E := eligibleNoiseLevels H hdim S t
  if hE : E.Nonempty then
    let n := selectedNoiseLevel H hdim S t hE
    have hn := mem_eligibleNoiseLevels_iff.mp (selectedNoiseLevel_mem hE)
    exact freshFromNoisyCore H S n
      (noisyClosureBound_spec hdim n S hn.2.1 hn.2.2)
  else
    exact Classical.choice inferInstance

theorem noisyClosureStrategyOutput_spec [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    {S : Finset α} {t : ℕ}
    (hE : (eligibleNoiseLevels H hdim S t).Nonempty) :
    let n := selectedNoiseLevel H hdim S t hE
    noisyClosureStrategyOutput H hdim S t ∈
      noisyCommonCore H S n \ (S : Set α) := by
  classical
  dsimp only
  rw [noisyClosureStrategyOutput]
  simp only [dif_pos hE]
  exact freshFromNoisyCore_spec _

/-- The single generator that combines the closure strategies at every noise
level, without receiving the adversary's noise level as input. -/
noncomputable def noisyClosureStrategy [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n) :
    GenLimit.Generic.Generator α :=
  fun t xs =>
    noisyClosureStrategyOutput H hdim
      (GenLimit.Generic.sequenceSample xs) t

theorem noisyClosureStrategy_output
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    GenLimit.Generic.output (noisyClosureStrategy H hdim) stream t =
      noisyClosureStrategyOutput H hdim
        (GenLimit.Generic.sample stream t) t := by
  simp only [GenLimit.Generic.output, noisyClosureStrategy,
    GenLimit.Generic.sequenceSample_prefix]

/-- Sufficiency in Theorem 3.3.  At true noise level `n`, the threshold is
the maximum of `n` and one more than the chosen bound on `NC_n(H)`. -/
theorem finite_noisyClosureDimensions_imply_uniform_noiseDependent
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n) :
    UniformNoiseDependentGeneratable H := by
  classical
  let gen := noisyClosureStrategy H hdim
  refine ⟨gen, ?_⟩
  intro n
  let d := max (noisyClosureBound H hdim n + 1) n
  refine ⟨d, ?_⟩
  intro L hLH stream hnoise t ht s hts
  have hdt : d ≤ t := by
    rw [← ht]
    exact GenLimit.Generic.sample_card_le stream t
  have hnt : n ≤ t :=
    (Nat.le_max_right (noisyClosureBound H hdim n + 1) n).trans hdt
  have hbound_t :
      noisyClosureBound H hdim n <
        (GenLimit.Generic.sample stream t).card := by
    rw [ht]
    exact (Nat.lt_succ_self _).trans_le
      (Nat.le_max_left (noisyClosureBound H hdim n + 1) n)
  have hsample_mono :
      GenLimit.Generic.sample stream t ⊆ GenLimit.Generic.sample stream s :=
    GenLimit.Generic.sample_mono hts
  have hbound_s :
      noisyClosureBound H hdim n <
        (GenLimit.Generic.sample stream s).card :=
    hbound_t.trans_le (Finset.card_le_card hsample_mono)
  have hnVS :
      (noisyVersionSpace H (GenLimit.Generic.sample stream s) n).Nonempty :=
    ⟨L, target_mem_noisyVersionSpace hLH hnoise⟩
  have hnE : n ∈ eligibleNoiseLevels H hdim
      (GenLimit.Generic.sample stream s) s := by
    apply mem_eligibleNoiseLevels_iff.mpr
    exact ⟨hnt.trans hts, hbound_s, hnVS⟩
  have hE : (eligibleNoiseLevels H hdim
      (GenLimit.Generic.sample stream s) s).Nonempty := ⟨n, hnE⟩
  let m := selectedNoiseLevel H hdim
    (GenLimit.Generic.sample stream s) s hE
  have hnm : n ≤ m := by
    exact le_selectedNoiseLevel hnE hE
  have htargetM :
      L ∈ noisyVersionSpace H (GenLimit.Generic.sample stream s) m := by
    exact target_mem_noisyVersionSpace hLH
      (hasNoiseAtMost_mono hnm hnoise)
  have hout :
      noisyClosureStrategyOutput H hdim
          (GenLimit.Generic.sample stream s) s ∈
        noisyCommonCore H (GenLimit.Generic.sample stream s) m \
          (GenLimit.Generic.sample stream s : Set α) := by
    simpa [m] using noisyClosureStrategyOutput_spec hE
  have hrun : GenLimit.Generic.output gen stream s =
      noisyClosureStrategyOutput H hdim
        (GenLimit.Generic.sample stream s) s := by
    simpa [gen] using noisyClosureStrategy_output
      (H := H) (hdim := hdim) stream s
  constructor
  · rw [hrun]
    exact noisyCommonCore_subset_of_mem_versionSpace htargetM hout.1
  · rw [hrun]
    exact hout.2



/-! ## Constructive necessity in Theorem 3.3 -/

theorem arbitrarily_large_witness_of_not_finiteNoisyClosureDimensionAt
    {H : GenLimit.Generic.LanguageClass α} {n : ℕ}
    (hnot : ¬FiniteNoisyClosureDimensionAt H n) :
    ∀ D : ℕ, ∃ d : ℕ, D < d ∧ NoisyClosureWitnessAt H n d := by
  intro D
  by_contra hnone
  apply hnot
  refine ⟨D, ?_⟩
  intro d hDd hwit
  exact hnone ⟨d, hDd, hwit⟩

/-- The adversarial finite-core padding construction in the necessity proof
of Theorem 3.3. -/
theorem nonfinite_noisyClosureDimension_defeats_threshold
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    {n : ℕ} (hnot : ¬FiniteNoisyClosureDimensionAt H n)
    (gen : GenLimit.Generic.Generator α) (d : ℕ) :
    ∃ L, L ∈ H ∧ ∃ stream : GenLimit.Generic.Stream α,
      HasNoiseAtMost stream L n ∧
      ∃ t, (GenLimit.Generic.sample stream t).card = d ∧
        ∃ s, t ≤ s ∧ ¬GenLimit.Generic.CorrectAt gen L stream s := by
  classical
  obtain ⟨k, hdk, S, hScard, hVS, hcoreFinite⟩ :=
    arbitrarily_large_witness_of_not_finiteNoisyClosureDimensionAt hnot d
  let C : Finset α := hcoreFinite.toFinset
  let P : Finset α := S ∪ C
  have hSP : S ⊆ P := by
    intro x hx
    exact Finset.mem_union_left C hx
  have hcoreP : noisyCommonCore H S n ⊆ (P : Set α) := by
    intro x hx
    have hxC : x ∈ C := by
      simpa [C] using hx
    exact Finset.mem_union_right S hxC
  let m := P.card
  have hkm : k ≤ m := by
    rw [← hScard]
    exact Finset.card_le_card hSP
  have hdm : d ≤ m := (Nat.le_of_lt hdk).trans hkm
  let xs : Fin m → α := fun i => (P.equivFin.symm i).1
  have hxs : Function.Injective xs := by
    intro i j hij
    apply P.equivFin.symm.injective
    exact Subtype.ext hij
  have hsample : GenLimit.Generic.sequenceSample xs = P := by
    simpa [m, xs] using sequenceSample_equivFin_symm P
  let y : α := gen m xs
  obtain ⟨L, hLVS, hybad⟩ :
      ∃ L, L ∈ noisyVersionSpace H S n ∧ (y ∉ L ∨ y ∈ P) := by
    by_cases hyP : y ∈ P
    · obtain ⟨L, hLVS⟩ := hVS
      exact ⟨L, hLVS, Or.inr hyP⟩
    · have hynotcore : y ∉ noisyCommonCore H S n := by
        intro hycore
        exact hyP (hcoreP hycore)
      simp only [noisyCommonCore, Set.mem_setOf_eq, not_forall] at hynotcore
      obtain ⟨L, hLVS, hyL⟩ := hynotcore
      exact ⟨L, hLVS, Or.inl hyL⟩
  have hnegativeSub : negativePart P L ⊆ negativePart S L := by
    intro x hx
    simp only [negativePart, Finset.mem_filter] at hx ⊢
    refine ⟨?_, hx.2⟩
    rcases Finset.mem_union.mp hx.1 with hxS | hxC
    · exact hxS
    · have hxcore : x ∈ noisyCommonCore H S n := by
        simpa [C] using hxC
      have hxL : x ∈ L :=
        noisyCommonCore_subset_of_mem_versionSpace hLVS hxcore
      exact (hx.2 hxL).elim
  have hnegativeP : (negativePart P L).card ≤ n := by
    exact (Finset.card_le_card hnegativeSub).trans
      (negativePart_card_le_of_mem_noisyVersionSpace hLVS)
  have hLinf : L.Infinite := hUUS L hLVS.1
  let tail : α := Classical.choose hLinf.nonempty
  have htail : tail ∈ L := Classical.choose_spec hLinf.nonempty
  let stream : GenLimit.Generic.Stream α := prefixThen xs tail
  have hnoise : HasNoiseAtMost stream L n := by
    apply hasNoiseAtMost_prefixThen hxs htail
    rw [hsample]
    exact hnegativeP
  have hsampleD : (GenLimit.Generic.sample stream d).card = d := by
    exact sample_prefixThen_card_of_le xs hxs tail hdm
  have hsampleM : GenLimit.Generic.sample stream m = P := by
    calc
      GenLimit.Generic.sample stream m =
          GenLimit.Generic.sequenceSample xs :=
        sample_prefixThen_full xs tail
      _ = P := hsample
  have hout : GenLimit.Generic.output gen stream m = y := by
    apply congrArg (fun f : Fin m → α => gen m f)
    funext i
    simp [stream, prefixThen, i.isLt]
  refine ⟨L, hLVS.1, stream, hnoise, d, hsampleD, m, hdm, ?_⟩
  intro hcorrect
  rcases hybad with hyL | hyP
  · exact hyL (hout ▸ hcorrect.1)
  · exact hcorrect.2 (by simpa [hout, hsampleM] using hyP)

/-- Necessity in Theorem 3.3. -/
theorem uniform_noiseDependent_implies_finite_noisyClosureDimensions
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hgen : UniformNoiseDependentGeneratable H) :
    ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n := by
  classical
  obtain ⟨gen, hgen⟩ := hgen
  intro n
  by_contra hnot
  obtain ⟨d, hd⟩ := hgen n
  obtain ⟨L, hLH, stream, hnoise, t, ht, s, hts, hfail⟩ :=
    nonfinite_noisyClosureDimension_defeats_threshold
      hUUS hnot gen d
  exact hfail (hd L hLH stream hnoise t ht s hts)

/-- Theorem 3.3 (Characterization of Uniform Noise-dependent
Generatability).  `[Nonempty α]` records the paper's implicit convention that
the example space contains an example; without it, the empty class over the
empty example space has finite noisy closure dimensions but admits no total
generator. -/
theorem theorem_3_3 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) :
    UniformNoiseDependentGeneratable H ↔
      ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n := by
  constructor
  · exact uniform_noiseDependent_implies_finite_noisyClosureDimensions hUUS
  · exact finite_noisyClosureDimensions_imply_uniform_noiseDependent

end GenLimit.NoisyExamples
