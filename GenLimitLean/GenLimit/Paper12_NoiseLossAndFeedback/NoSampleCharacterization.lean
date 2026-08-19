import GenLimit.Paper12_NoiseLossAndFeedback.NoisyWithoutSamples
import GenLimit.Core.ClassCovers
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Countable

/-!
# Noise, Loss, and Feedback: the non-uniform no-sample characterization

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, summary Theorem 1.3,
Algorithm 3, and Theorem 4.7.

Theorem 1.3 characterizes generation in the limit without samples by an
increasing countable cover whose every level has infinite common
intersection.  The construction below implements Algorithm 3 semantically:
at stage `n`, choose a point in the common intersection of the `n`th level
that has not been output earlier.

For a countable collection, Theorem 4.7 simplifies the condition to infinite
common intersection for every finite subcollection.  Both directions below
are the literal biconditionals.  The development makes no computability or
running-time assertion.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## The chain condition in Theorem 1.3 -/

/-- A sequence `C₀ ⊆ C₁ ⊆ ...` covers `C` and every `Cᵢ` has infinite
common intersection. -/
def IsIncreasingInfiniteCoreCover
    (C : LanguageClass α)
    (classes : ℕ → LanguageClass α) : Prop :=
  IsNondecreasingCover C classes ∧
    ∀ i, (languageIntersection (classes i)).Infinite

/-- The right-hand side of summary Theorem 1.3. -/
def HasIncreasingInfiniteCoreCover
    (C : LanguageClass α) : Prop :=
  ∃ classes : ℕ → LanguageClass α,
    IsIncreasingInfiniteCoreCover C classes

theorem increasingCover_monotone
    {C : LanguageClass α} {classes : ℕ → LanguageClass α}
    (hcover : IsIncreasingInfiniteCoreCover C classes) :
    Monotone classes :=
  hcover.1.1

/-! ## Algorithm 3 -/

/-- A point in the common intersection of `classes n` outside the finite
set of earlier outputs. -/
noncomputable def freshCoreValue
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite)
    (n : ℕ) (seen : Finset α) : α :=
  GenLimit.Support.infiniteEnumeration
    (languageIntersection (classes n)) (hcores n)
    (GenLimit.Support.progress
      (languageIntersection (classes n)) (hcores n) seen)

theorem freshCoreValue_mem
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite)
    (n : ℕ) (seen : Finset α) :
    freshCoreValue classes hcores n seen ∈
      languageIntersection (classes n) := by
  exact
    GenLimit.Support.infiniteEnumeration_mem
      (languageIntersection (classes n)) (hcores n)
      (GenLimit.Support.progress
        (languageIntersection (classes n)) (hcores n) seen)

theorem freshCoreValue_not_mem
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite)
    (n : ℕ) (seen : Finset α) :
    freshCoreValue classes hcores n seen ∉ seen := by
  exact
    GenLimit.Support.progress_spec
      (languageIntersection (classes n)) (hcores n) seen

/-- The finite set of values emitted before stage `n`. -/
noncomputable def coreChainSeen
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite)
    (n : ℕ) : Finset α := by
  exact Nat.rec ∅
    (fun i seen =>
      Finset.cons (freshCoreValue classes hcores i seen) seen
        (freshCoreValue_not_mem classes hcores i seen))
    n

/-- Algorithm 3's stage-`n` output. -/
noncomputable def coreChainOutput
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite)
    (n : ℕ) : α :=
  freshCoreValue classes hcores n
    (coreChainSeen classes hcores n)

@[simp] theorem coreChainSeen_zero
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite) :
    coreChainSeen classes hcores 0 = ∅ := by
  simp [coreChainSeen]

theorem coreChainOutput_not_mem_seen
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite)
    (n : ℕ) :
    coreChainOutput classes hcores n ∉
      coreChainSeen classes hcores n :=
  freshCoreValue_not_mem classes hcores n
    (coreChainSeen classes hcores n)

theorem coreChainOutput_mem_core
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite)
    (n : ℕ) :
    coreChainOutput classes hcores n ∈
      languageIntersection (classes n) :=
  freshCoreValue_mem classes hcores n
    (coreChainSeen classes hcores n)

theorem coreChainSeen_monotone
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite) :
    Monotone (coreChainSeen classes hcores) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [coreChainSeen]
  exact Finset.subset_cons _

theorem coreChainOutput_mem_seen_of_lt
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite)
    {m n : ℕ} (hmn : m < n) :
    coreChainOutput classes hcores m ∈
      coreChainSeen classes hcores n := by
  classical
  have hmem :
      coreChainOutput classes hcores m ∈
        coreChainSeen classes hcores (m + 1) := by
    simp [coreChainSeen, coreChainOutput]
  exact
    coreChainSeen_monotone classes hcores
      (Nat.succ_le_iff.mpr hmn) hmem

theorem coreChainOutput_injective
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite) :
    Function.Injective (coreChainOutput classes hcores) := by
  intro m n hmn
  rcases lt_trichotomy m n with hlt | heq | hgt
  · have hmem :=
      coreChainOutput_mem_seen_of_lt classes hcores hlt
    have hnot :=
      coreChainOutput_not_mem_seen classes hcores n
    exact (hnot (hmn ▸ hmem)).elim
  · exact heq
  · have hmem :=
      coreChainOutput_mem_seen_of_lt classes hcores hgt
    have hnot :=
      coreChainOutput_not_mem_seen classes hcores m
    exact (hnot (hmn.symm ▸ hmem)).elim

/-- The repetition-free output stream produced by Algorithm 3. -/
noncomputable def generatorFromInfiniteCoreChain
    [Countable α]
    (classes : ℕ → LanguageClass α)
    (hcores :
      ∀ i, (languageIntersection (classes i)).Infinite) :
    WithoutSamplesGenerator α where
  output := coreChainOutput classes hcores
  injective' := coreChainOutput_injective classes hcores

theorem increasingInfiniteCoreCover_implies_inLimit
    [Countable α]
    {C : LanguageClass α}
    (hcover : HasIncreasingInfiniteCoreCover C) :
    GeneratableInLimitWithoutSamples C := by
  obtain ⟨classes, ⟨hchain, hC⟩, hcores⟩ := hcover
  let gen :=
    generatorFromInfiniteCoreChain classes hcores
  refine ⟨gen, ?_⟩
  intro L hLC
  have hUnion : L ∈ ⋃ i, classes i := by
    rw [← hC]
    exact hLC
  obtain ⟨i, hLi⟩ := Set.mem_iUnion.mp hUnion
  refine ⟨i, ?_⟩
  intro n hin
  have hLin : L ∈ classes n :=
    hchain hin hLi
  exact (coreChainOutput_mem_core classes hcores n) L hLin

/-! ## Recovering the chain from target-dependent thresholds -/

/-- Languages on which `gen` is already permanently correct from time `i`. -/
def tailCorrectClass
    (gen : WithoutSamplesGenerator α)
    (C : LanguageClass α) (i : ℕ) :
    LanguageClass α :=
  {L | L ∈ C ∧ ∀ t, i ≤ t → gen.output t ∈ L}

theorem tailCorrectClass_step
    (gen : WithoutSamplesGenerator α)
    (C : LanguageClass α) (i : ℕ) :
    tailCorrectClass gen C i ⊆
      tailCorrectClass gen C (i + 1) := by
  rintro L ⟨hLC, htail⟩
  refine ⟨hLC, ?_⟩
  intro t hit
  exact htail t (le_trans (Nat.le_succ i) hit)

theorem inLimit_implies_increasingInfiniteCoreCover
    [Countable α]
    {C : LanguageClass α}
    (h : GeneratableInLimitWithoutSamples C) :
    HasIncreasingInfiniteCoreCover C := by
  obtain ⟨gen, hgen⟩ := h
  refine ⟨tailCorrectClass gen C, ⟨?_, ?_⟩, ?_⟩
  · exact monotone_nat_of_le_succ (tailCorrectClass_step gen C)
  · ext L
    constructor
    · intro hLC
      obtain ⟨T, hT⟩ := hgen L hLC
      exact Set.mem_iUnion.mpr ⟨T, hLC, hT⟩
    · intro hL
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hL
      exact hi.1
  · intro i
    apply
      uniform_withoutSamples_implies_infinite_intersection
    refine ⟨gen, i, ?_⟩
    intro L hL t hit
    exact hL.2 t hit

/-- Summary Theorem 1.3, with the source's complete quantifier order. -/
theorem theorem_1_3
    [Countable α]
    (C : LanguageClass α) :
    GeneratableInLimitWithoutSamples C ↔
      HasIncreasingInfiniteCoreCover C :=
  ⟨inLimit_implies_increasingInfiniteCoreCover,
    increasingInfiniteCoreCover_implies_inLimit⟩

/-- Combining Theorems 4.5 and 1.3 gives the advertised characterization of
non-uniform noisy generation over the paper's universe `ℕ`. -/
theorem nonuniform_noisy_iff_increasingInfiniteCoreCover
    (C : LanguageClass ℕ)
    (hInfinite : GenLimit.Generic.UUS C) :
    NonuniformlyNoisilyGeneratable C ↔
      HasIncreasingInfiniteCoreCover C :=
  (theorem_4_5 C hInfinite).trans (theorem_1_3 C)

/-! ## The countable-class simplification, Theorem 4.7 -/

/-- Every finite subcollection of `C` has infinite common intersection. -/
def FiniteSubcollectionsHaveInfiniteCore
    (C : LanguageClass α) : Prop :=
  ∀ C' : LanguageClass α,
    C'.Finite → C' ⊆ C →
      (languageIntersection C').Infinite

theorem inLimit_implies_finiteSubcollectionCores
    {C : LanguageClass α}
    (h : GeneratableInLimitWithoutSamples C) :
    FiniteSubcollectionsHaveInfiniteCore C := by
  classical
  obtain ⟨gen, hgen⟩ := h
  intro C' hfinite hsub
  let threshold : GenLimit.Generic.Language α → ℕ :=
    fun L =>
      if hLC' : L ∈ C' then
        Classical.choose (hgen L (hsub hLC'))
      else 0
  have threshold_spec :
      ∀ L, L ∈ C' → ∀ t, threshold L ≤ t →
        gen.output t ∈ L := by
    intro L hLC'
    dsimp [threshold]
    rw [dif_pos hLC']
    exact Classical.choose_spec (hgen L (hsub hLC'))
  let T := hfinite.toFinset.sup threshold
  apply uniform_withoutSamples_implies_infinite_intersection
  refine ⟨gen, T, ?_⟩
  intro L hLC' t ht
  apply threshold_spec L hLC' t
  have hmem : L ∈ hfinite.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hLC'
  exact (Finset.le_sup (f := threshold) hmem).trans ht

/-- The finite initial subcollection `{f 0, ..., f n}`. -/
def finiteInitialClass
    (f : ℕ → GenLimit.Generic.Language α) (n : ℕ) :
    LanguageClass α :=
  f '' (↑(Finset.range (n + 1)) : Set ℕ)

theorem finiteInitialClass_finite
    (f : ℕ → GenLimit.Generic.Language α) (n : ℕ) :
    (finiteInitialClass f n).Finite :=
  (Finset.range (n + 1)).finite_toSet.image f

theorem finiteInitialClass_step
    (f : ℕ → GenLimit.Generic.Language α) (n : ℕ) :
    finiteInitialClass f n ⊆ finiteInitialClass f (n + 1) := by
  rintro L ⟨i, hin, rfl⟩
  refine ⟨i, ?_, rfl⟩
  rw [Finset.mem_coe, Finset.mem_range] at hin ⊢
  omega

theorem finiteInitialClass_subset_range
    (f : ℕ → GenLimit.Generic.Language α) (n : ℕ) :
    finiteInitialClass f n ⊆ Set.range f := by
  rintro L ⟨i, _hin, rfl⟩
  exact ⟨i, rfl⟩

theorem iUnion_finiteInitialClass
    (f : ℕ → GenLimit.Generic.Language α) :
    (⋃ n, finiteInitialClass f n) = Set.range f := by
  ext L
  constructor
  · intro hL
    obtain ⟨n, i, _hin, rfl⟩ := Set.mem_iUnion.mp hL
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr
      ⟨i, i, (by simp), rfl⟩

theorem countable_finiteCores_implies_inLimit
    [Countable α]
    {C : LanguageClass α}
    (hCountable : C.Countable)
    (hfinite : FiniteSubcollectionsHaveInfiniteCore C) :
    GeneratableInLimitWithoutSamples C := by
  by_cases hC : C.Nonempty
  · obtain ⟨f, hCf⟩ := hCountable.exists_eq_range hC
    apply (theorem_1_3 C).mpr
    refine ⟨finiteInitialClass f, ⟨?_, ?_⟩, ?_⟩
    · exact monotone_nat_of_le_succ (finiteInitialClass_step f)
    · exact hCf.trans (iUnion_finiteInitialClass f).symm
    · intro n
      apply hfinite (finiteInitialClass f n)
        (finiteInitialClass_finite f n)
      intro L hL
      rw [hCf]
      exact finiteInitialClass_subset_range f n hL
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    apply (theorem_1_3 C).mpr
    refine ⟨fun _ => ∅, ⟨?_, ?_⟩, ?_⟩
    · exact monotone_const
    · simp [hCempty]
    · intro i
      exact hfinite ∅ Set.finite_empty (by simp)

/-- Theorem 4.7: for a countable collection, generation in the limit
without samples is equivalent to the finite-subcollection condition. -/
theorem theorem_4_7
    [Countable α]
    (C : LanguageClass α)
    (hCountable : C.Countable) :
    GeneratableInLimitWithoutSamples C ↔
      FiniteSubcollectionsHaveInfiniteCore C :=
  ⟨inLimit_implies_finiteSubcollectionCores,
    countable_finiteCores_implies_inLimit hCountable⟩

/-- Countable-class noisy form obtained from the exact Theorems 4.5 and 4.7. -/
theorem countable_nonuniform_noisy_iff_finiteSubcollectionCores
    (C : LanguageClass ℕ)
    (hInfinite : GenLimit.Generic.UUS C)
    (hCountable : C.Countable) :
    NonuniformlyNoisilyGeneratable C ↔
      FiniteSubcollectionsHaveInfiniteCore C :=
  (theorem_4_5 C hInfinite).trans (theorem_4_7 C hCountable)

end GenLimit.NoiseLossFeedback
