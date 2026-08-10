import GenLimit.Paper06_NoisyExamples.NonuniformDefinitions
import GenLimit.Paper06_NoisyExamples.FiniteClasses
import GenLimit.Core.ClassCovers
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Range

/-!
# #06 Noisy Examples: non-uniform noise-dependent generation

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Lemmas 3.6 and 3.8 and Corollary 3.7.

The construction in Lemma 3.6 follows the paper's maximum-index strategy.
At a finite history it selects the largest index `i` for which the history is
past a bound on `NC_i(H_i)` and the `i`-noisy version space is nonempty, then
outputs a fresh point in that noisy core.  The candidate set is explicitly
restricted to `i ≤ t`; this makes the displayed maximum well-defined and is
the finite implementation of the paper's `i ∈ [t]`.
-/

namespace GenLimit.NoisyExamples

/-- A selected bound on `NC_i(H_i)`. -/
noncomputable def diagonalNoisyClosureBound
    (classes : ℕ → GenLimit.Generic.LanguageClass α)
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i)
    (i : ℕ) : ℕ :=
  Classical.choose
    (finiteNoisyClosureDimensionAt_iff_eventually_infinite.mp (hdim i))

theorem diagonalNoisyClosureBound_spec
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i)
    (i : ℕ) (S : Finset α)
    (hlarge : diagonalNoisyClosureBound classes hdim i < S.card)
    (hVS : (noisyVersionSpace (classes i) S i).Nonempty) :
    (noisyCommonCore (classes i) S i).Infinite := by
  exact Classical.choose_spec
    (finiteNoisyClosureDimensionAt_iff_eventually_infinite.mp (hdim i))
    S hlarge hVS

/-- The indices considered by the non-uniform construction at one history. -/
noncomputable def diagonalEligibleIndices
    (classes : ℕ → GenLimit.Generic.LanguageClass α)
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i)
    (S : Finset α) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t + 1)).filter fun i ↦
    diagonalNoisyClosureBound classes hdim i < S.card ∧
      (noisyVersionSpace (classes i) S i).Nonempty

theorem mem_diagonalEligibleIndices_iff
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    {S : Finset α} {t i : ℕ} :
    i ∈ diagonalEligibleIndices classes hdim S t ↔
      i ≤ t ∧ diagonalNoisyClosureBound classes hdim i < S.card ∧
        (noisyVersionSpace (classes i) S i).Nonempty := by
  classical
  simp [diagonalEligibleIndices, Nat.lt_succ_iff]

noncomputable def selectedDiagonalIndex
    (classes : ℕ → GenLimit.Generic.LanguageClass α)
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i)
    (S : Finset α) (t : ℕ)
    (hE : (diagonalEligibleIndices classes hdim S t).Nonempty) : ℕ :=
  (diagonalEligibleIndices classes hdim S t).max' hE

theorem selectedDiagonalIndex_mem
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    {S : Finset α} {t : ℕ}
    (hE : (diagonalEligibleIndices classes hdim S t).Nonempty) :
    selectedDiagonalIndex classes hdim S t hE ∈
      diagonalEligibleIndices classes hdim S t :=
  Finset.max'_mem _ _

theorem le_selectedDiagonalIndex
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    {S : Finset α} {t i : ℕ}
    (hi : i ∈ diagonalEligibleIndices classes hdim S t)
    (hE : (diagonalEligibleIndices classes hdim S t).Nonempty) :
    i ≤ selectedDiagonalIndex classes hdim S t hE :=
  Finset.le_max' _ _ hi

/-- The paper's history-level output for Lemma 3.6. -/
noncomputable def diagonalNoisyStrategyOutput [Nonempty α]
    (classes : ℕ → GenLimit.Generic.LanguageClass α)
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i)
    (S : Finset α) (t : ℕ) : α := by
  classical
  let E := diagonalEligibleIndices classes hdim S t
  if hE : E.Nonempty then
    let i := selectedDiagonalIndex classes hdim S t hE
    have hi := mem_diagonalEligibleIndices_iff.mp (selectedDiagonalIndex_mem hE)
    exact freshFromNoisyCore (classes i) S i
      (diagonalNoisyClosureBound_spec hdim i S hi.2.1 hi.2.2)
  else
    exact Classical.choice inferInstance

theorem diagonalNoisyStrategyOutput_spec [Nonempty α]
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    {S : Finset α} {t : ℕ}
    (hE : (diagonalEligibleIndices classes hdim S t).Nonempty) :
    let i := selectedDiagonalIndex classes hdim S t hE
    diagonalNoisyStrategyOutput classes hdim S t ∈
      noisyCommonCore (classes i) S i \ (S : Set α) := by
  classical
  dsimp only
  rw [diagonalNoisyStrategyOutput]
  simp only [dif_pos hE]
  exact freshFromNoisyCore_spec _

noncomputable def diagonalNoisyStrategy [Nonempty α]
    (classes : ℕ → GenLimit.Generic.LanguageClass α)
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i) :
    GenLimit.Generic.Generator α :=
  fun t xs ↦ diagonalNoisyStrategyOutput classes hdim
    (GenLimit.Generic.sequenceSample xs) t

theorem diagonalNoisyStrategy_output [Nonempty α]
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    GenLimit.Generic.output (diagonalNoisyStrategy classes hdim) stream t =
      diagonalNoisyStrategyOutput classes hdim
        (GenLimit.Generic.sample stream t) t := by
  simp only [GenLimit.Generic.output, diagonalNoisyStrategy,
    GenLimit.Generic.sequenceSample_prefix]

/-- Lemma 3.6 (Sufficiency for Non-uniform Noise-dependent
Generatability). -/
theorem lemma_3_6 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (_hUUS : GenLimit.Generic.UUS H)
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hcover : GenLimit.Generic.IsNondecreasingCover H classes)
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i) :
    NonuniformNoiseDependentGeneratable H := by
  classical
  let gen := diagonalNoisyStrategy classes hdim
  refine ⟨gen, ?_⟩
  intro n L hLH
  have hLUnion : L ∈ ⋃ i, classes i := by
    rw [← hcover.2]
    exact hLH
  obtain ⟨i, hLi⟩ := Set.mem_iUnion.mp hLUnion
  let targetIndex := max i n
  have hiTarget : i ≤ targetIndex := Nat.le_max_left _ _
  have hnTarget : n ≤ targetIndex := Nat.le_max_right _ _
  have hLTarget : L ∈ classes targetIndex := hcover.1 hiTarget hLi
  let d := max (diagonalNoisyClosureBound classes hdim targetIndex + 1)
    targetIndex
  refine ⟨d, ?_⟩
  intro stream hnoise t ht s hts
  have hdt : d ≤ t := by
    rw [← ht]
    exact GenLimit.Generic.sample_card_le stream t
  have hindexT : targetIndex ≤ t :=
    (Nat.le_max_right
      (diagonalNoisyClosureBound classes hdim targetIndex + 1)
      targetIndex).trans hdt
  have hsampleMono : GenLimit.Generic.sample stream t ⊆
      GenLimit.Generic.sample stream s := GenLimit.Generic.sample_mono hts
  have hboundT : diagonalNoisyClosureBound classes hdim targetIndex <
      (GenLimit.Generic.sample stream t).card := by
    rw [ht]
    exact (Nat.lt_succ_self _).trans_le (Nat.le_max_left _ _)
  have hboundS : diagonalNoisyClosureBound classes hdim targetIndex <
      (GenLimit.Generic.sample stream s).card :=
    hboundT.trans_le (Finset.card_le_card hsampleMono)
  have htargetVS : L ∈ noisyVersionSpace (classes targetIndex)
      (GenLimit.Generic.sample stream s) targetIndex := by
    exact target_mem_noisyVersionSpace hLTarget
      (hasNoiseAtMost_mono hnTarget hnoise)
  have htargetEligible : targetIndex ∈ diagonalEligibleIndices classes hdim
      (GenLimit.Generic.sample stream s) s := by
    apply mem_diagonalEligibleIndices_iff.mpr
    exact ⟨hindexT.trans hts, hboundS, ⟨L, htargetVS⟩⟩
  have hE : (diagonalEligibleIndices classes hdim
      (GenLimit.Generic.sample stream s) s).Nonempty :=
    ⟨targetIndex, htargetEligible⟩
  let selected := selectedDiagonalIndex classes hdim
    (GenLimit.Generic.sample stream s) s hE
  have htargetSelected : targetIndex ≤ selected :=
    le_selectedDiagonalIndex htargetEligible hE
  have hnSelected : n ≤ selected := hnTarget.trans htargetSelected
  have hLSelected : L ∈ classes selected :=
    hcover.1 htargetSelected hLTarget
  have hselectedVS : L ∈ noisyVersionSpace (classes selected)
      (GenLimit.Generic.sample stream s) selected :=
    target_mem_noisyVersionSpace hLSelected
      (hasNoiseAtMost_mono hnSelected hnoise)
  have hout : diagonalNoisyStrategyOutput classes hdim
      (GenLimit.Generic.sample stream s) s ∈
        noisyCommonCore (classes selected)
          (GenLimit.Generic.sample stream s) selected \
        (GenLimit.Generic.sample stream s : Set α) := by
    simpa [selected] using diagonalNoisyStrategyOutput_spec hE
  have hrun : GenLimit.Generic.output gen stream s =
      diagonalNoisyStrategyOutput classes hdim
        (GenLimit.Generic.sample stream s) s := by
    simpa [gen] using diagonalNoisyStrategy_output
      (classes := classes) (hdim := hdim) stream s
  constructor
  · rw [hrun]
    exact noisyCommonCore_subset_of_mem_versionSpace hselectedVS hout.1
  · rw [hrun]
    exact hout.2

/-! ## Necessity, Lemma 3.8 -/

private theorem fixed_noise_generator_implies_finite_dimension
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (gen : GenLimit.Generic.Generator α) (n d : ℕ)
    (hgen : ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
      HasNoiseAtMost stream L n →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s) :
    FiniteNoisyClosureDimensionAt H n := by
  classical
  by_contra hnot
  obtain ⟨L, hLH, stream, hnoise, t, ht, s, hts, hfail⟩ :=
    nonfinite_noisyClosureDimension_defeats_threshold hUUS hnot gen d
  exact hfail (hgen L hLH stream hnoise t ht s hts)

/-- Lemma 3.8 (Necessity for Non-uniform Noise-dependent
Generatability).  The sequence of subclasses may depend on the fixed noise
level `n`, exactly as in the printed quantifier order. -/
theorem lemma_3_8 [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hgen : NonuniformNoiseDependentGeneratable H) :
    ∀ n : ℕ, ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
      GenLimit.Generic.IsNondecreasingCover H classes ∧
      ∀ i, FiniteNoisyClosureDimensionAt (classes i) n := by
  classical
  obtain ⟨gen, hgen⟩ := hgen
  intro n
  let threshold : ∀ L, L ∈ H → ℕ :=
    fun L hLH ↦ Nat.find (hgen n L hLH)
  let classes : ℕ → GenLimit.Generic.LanguageClass α :=
    fun i ↦ {L | ∃ hLH : L ∈ H, threshold L hLH ≤ i}
  refine ⟨classes, ?_, ?_⟩
  · constructor
    · intro i j hij L hLi
      obtain ⟨hLH, hthreshold⟩ := hLi
      exact ⟨hLH, hthreshold.trans hij⟩
    · ext L
      constructor
      · intro hLH
        exact Set.mem_iUnion.mpr
          ⟨threshold L hLH, hLH, le_rfl⟩
      · intro hLUnion
        obtain ⟨i, hLi⟩ := Set.mem_iUnion.mp hLUnion
        exact hLi.choose
  · intro i
    have hUUSi : GenLimit.Generic.UUS (classes i) := by
      intro L hLi
      exact hUUS L hLi.choose
    apply fixed_noise_generator_implies_finite_dimension hUUSi gen n i
    intro L hLi
    obtain ⟨hLH, hthreshold⟩ := hLi
    intro stream hnoise
    exact GenLimit.Generic.eventualAtExactSize_mono
      (size := fun t ↦ (GenLimit.Generic.sample stream t).card)
      (fun hk ↦ GenLimit.Generic.exists_sample_card_eq_of_le hk)
      hthreshold (Nat.find_spec (hgen n L hLH) stream hnoise)

/-- Corollary 3.7 (All Countable Classes are Noisily Non-uniformly
Generatable).  The finite-prefix cover also handles empty and finite classes,
which the paper's notation `h₁,h₂,...` leaves implicit. -/
theorem corollary_3_7 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hCountable : H.Countable) :
    NonuniformNoiseDependentGeneratable H ∧ NoisilyGeneratableInLimit H := by
  classical
  obtain ⟨enumerate, hEnumerates⟩ :=
    Set.countable_iff_exists_subset_range.mp hCountable
  let classes : ℕ → GenLimit.Generic.LanguageClass α :=
    fun n ↦ {L | L ∈ H ∧ ∃ i < n + 1, enumerate i = L}
  have hcover : GenLimit.Generic.IsNondecreasingCover H classes := by
    constructor
    · intro m n hmn L hLm
      obtain ⟨hLH, i, him, hiL⟩ := hLm
      exact ⟨hLH, i, him.trans_le (Nat.add_le_add_right hmn 1), hiL⟩
    · ext L
      constructor
      · intro hLH
        obtain ⟨i, hiL⟩ := hEnumerates hLH
        exact Set.mem_iUnion.mpr
          ⟨i, hLH, i, Nat.lt_succ_self i, hiL⟩
      · intro hLUnion
        obtain ⟨n, hLn⟩ := Set.mem_iUnion.mp hLUnion
        exact hLn.1
  have hfinite : ∀ n, (classes n).Finite := by
    intro n
    apply (Set.finite_range (fun i : Fin (n + 1) ↦ enumerate i)).subset
    intro L hLn
    obtain ⟨_hLH, i, hin, rfl⟩ := hLn
    exact ⟨⟨i, hin⟩, rfl⟩
  have hnonuniform : NonuniformNoiseDependentGeneratable H := by
    apply lemma_3_6 hUUS hcover
    intro n
    exact finite_class_has_finite_noisyClosureDimensionAt (hfinite n) n
  exact ⟨hnonuniform,
    nonuniform_noiseDependent_implies_noisy_limit hUUS hnonuniform⟩

end GenLimit.NoisyExamples
