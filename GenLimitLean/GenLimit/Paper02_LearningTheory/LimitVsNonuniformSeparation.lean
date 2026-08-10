import GenLimit.Paper02_LearningTheory.FiniteConeCover
import Mathlib.Data.List.OfFn

/-!
# Generation in the limit is strictly weaker than non-uniform generation

This file formalizes Lemma 3.12 and Lemma 4.2 of Li--Raman--Tewari,
*Generation through the Lens of Learning Theory*, arXiv:2410.13714v5 /
COLT 2025.

The paper works on `ℤ`, partitioned into the positive integers and the
non-positive integers.  The proof is cleaner, and has exactly the same
mathematical content, for two disjoint infinite subsets `P` and `N` of any
countable example space.  The concrete `ℤ` statements at the end instantiate
this abstraction with the paper's two sets.

For the hard direction we retain the paper's diagonal idea.  Given a proposed
non-uniform generator, correctness on the all-`P` language lets us construct
an infinite stream in `P` while permanently withholding every output made on
that stream.  Its range is then used as the paper's adversarial subset `A`.
-/

namespace GenLimit.LiRamanTewari

/-- The paper's first class: languages `N ∪ A`, where `A ⊆ P`. -/
def subsetConeClass (P N : Set α) : GenLimit.Generic.LanguageClass α :=
  {L | ∃ A : Set α, A ⊆ P ∧ L = N ∪ A}

/-- The class used in Lemma 3.12: the subset cone together with the all-`P`
language. -/
def limitNonuniformSeparationClass (P N : Set α) :
    GenLimit.Generic.LanguageClass α :=
  subsetConeClass P N ∪ ({P} : Set (Set α))

theorem mem_limitNonuniformSeparationClass_iff {P N L : Set α} :
    L ∈ limitNonuniformSeparationClass P N ↔
      (∃ A : Set α, A ⊆ P ∧ L = N ∪ A) ∨ L = P := by
  rw [limitNonuniformSeparationClass, Set.mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)
  · rintro (h | hLP)
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mpr hLP)

private noncomputable def freshFrom
    (S : Set α) (hS : S.Infinite) (seen : Finset α) : α :=
  Classical.choose (hS.diff seen.finite_toSet).nonempty

private theorem freshFrom_mem
    (S : Set α) (hS : S.Infinite) (seen : Finset α) :
    freshFrom S hS seen ∈ S :=
  (Classical.choose_spec (hS.diff seen.finite_toSet).nonempty).1

private theorem freshFrom_not_mem
    (S : Set α) (hS : S.Infinite) (seen : Finset α) :
    freshFrom S hS seen ∉ seen :=
  (Classical.choose_spec (hS.diff seen.finite_toSet).nonempty).2

/-- The generator in the first half of the proof of Lemma 3.12.  As long as
the observed history lies in `P`, it emits a fresh point of `P`; after the
first observation outside `P`, it emits fresh points of `N`. -/
noncomputable def partitionLimitGenerator
    (P N : Set α) (hP : P.Infinite) (hN : N.Infinite) :
    GenLimit.Generic.Generator α := by
  classical
  exact fun _ xs ↦
    let seen := GenLimit.Generic.sequenceSample xs
    if h : (↑seen : Set α) ⊆ P then
      freshFrom P hP seen
    else
      freshFrom N hN seen

private theorem partitionLimitGenerator_correct_in_P
    (P N : Set α) (hP : P.Infinite) (hN : N.Infinite)
    (stream : GenLimit.Generic.Stream α) (t : ℕ)
    (hseen : (↑(GenLimit.Generic.sample stream t) : Set α) ⊆ P) :
    GenLimit.Generic.CorrectAt
      (partitionLimitGenerator P N hP hN) P stream t := by
  classical
  constructor
  · unfold GenLimit.Generic.output partitionLimitGenerator
    rw [GenLimit.Generic.sequenceSample_prefix]
    simp only [dif_pos hseen]
    exact freshFrom_mem P hP _
  · unfold GenLimit.Generic.output partitionLimitGenerator
    rw [GenLimit.Generic.sequenceSample_prefix]
    simp only [dif_pos hseen]
    exact freshFrom_not_mem P hP _

private theorem partitionLimitGenerator_correct_in_N
    (P N : Set α) (hP : P.Infinite) (hN : N.Infinite)
    (stream : GenLimit.Generic.Stream α) (t : ℕ)
    (hseen : ¬(↑(GenLimit.Generic.sample stream t) : Set α) ⊆ P) :
    GenLimit.Generic.CorrectAt
      (partitionLimitGenerator P N hP hN) N stream t := by
  classical
  constructor
  · unfold GenLimit.Generic.output partitionLimitGenerator
    rw [GenLimit.Generic.sequenceSample_prefix]
    simp only [dif_neg hseen]
    exact freshFrom_mem N hN _
  · unfold GenLimit.Generic.output partitionLimitGenerator
    rw [GenLimit.Generic.sequenceSample_prefix]
    simp only [dif_neg hseen]
    exact freshFrom_not_mem N hN _

theorem separation_class_uus
    {P N : Set α} (hP : P.Infinite) (hN : N.Infinite) :
    UUS (limitNonuniformSeparationClass P N) := by
  intro L hL
  rw [mem_limitNonuniformSeparationClass_iff] at hL
  rcases hL with ⟨A, _hAP, rfl⟩ | rfl
  · exact hN.mono Set.subset_union_left
  · exact hP

/-- The first half of Lemma 3.12: the paper's class is generatable in the
limit. -/
theorem separation_class_generatable_in_limit
    {P N : Set α} (hP : P.Infinite) (hN : N.Infinite)
    (hDisjoint : Disjoint P N) :
    GeneratableInLimit (limitNonuniformSeparationClass P N) := by
  classical
  let gen := partitionLimitGenerator P N hP hN
  refine ⟨gen, ?_⟩
  intro L hL stream hPresentation
  rw [mem_limitNonuniformSeparationClass_iff] at hL
  rcases hL with ⟨A, hAP, rfl⟩ | hLP
  · obtain ⟨z, hzN⟩ := hN.nonempty
    have hzTarget : z ∈ N ∪ A := Set.mem_union_left A hzN
    obtain ⟨T, hT⟩ :=
      GenLimit.Generic.eventually_mem_sample_of_presents hPresentation hzTarget
    refine ⟨T, ?_⟩
    intro t hTt
    have hzSeen : z ∈ GenLimit.Generic.sample stream t := hT t hTt
    have hnotSubset :
        ¬(↑(GenLimit.Generic.sample stream t) : Set α) ⊆ P := by
      intro hsub
      exact Set.disjoint_left.mp hDisjoint (hsub hzSeen) hzN
    have hcorrectN :=
      partitionLimitGenerator_correct_in_N P N hP hN stream t hnotSubset
    exact ⟨Set.mem_union_left A hcorrectN.1, hcorrectN.2⟩
  · refine ⟨0, ?_⟩
    intro t _ht
    have hPresentationP : GenLimit.Generic.Presents stream P := by
      simpa [hLP] using hPresentation
    have hcorrect := partitionLimitGenerator_correct_in_P P N hP hN stream t
      (sample_subset_of_streamIn
        (GenLimit.Generic.streamIn_of_presents hPresentationP) t)
    simpa [gen, hLP] using hcorrect

/-! ## The diagonal stream -/

private def listPrefix (l : List α) (k : ℕ) (hk : k ≤ l.length) : Fin k → α :=
  fun i ↦ l.get ⟨i, i.isLt.trans_le hk⟩

/-- All outputs the proposed generator makes on prefixes of `l`, including
the output on the whole history `l`. -/
private noncomputable def pastOutputs
    (gen : GenLimit.Generic.Generator α) (l : List α) : Finset α := by
  classical
  exact Finset.univ.image (fun i : Fin (l.length + 1) ↦
    gen i (listPrefix l i (Nat.le_of_lt_succ i.isLt)))

private noncomputable def diagonalFresh
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (l : List α) : α := by
  classical
  exact freshFrom P hP (l.toFinset ∪ pastOutputs gen l)

private noncomputable def diagonalHistory
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite) :
    ℕ → List α
  | 0 => []
  | n + 1 =>
      let l := diagonalHistory gen P hP n
      l ++ [diagonalFresh gen P hP l]

private noncomputable def diagonalStream
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite) :
    GenLimit.Generic.Stream α :=
  fun n ↦ diagonalFresh gen P hP (diagonalHistory gen P hP n)

@[simp] private theorem diagonalHistory_zero
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite) :
    diagonalHistory gen P hP 0 = [] :=
  rfl

private theorem diagonalHistory_succ
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (n : ℕ) :
    diagonalHistory gen P hP (n + 1) =
      diagonalHistory gen P hP n ++ [diagonalStream gen P hP n] :=
  rfl

@[simp] private theorem diagonalHistory_length
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (n : ℕ) :
    (diagonalHistory gen P hP n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [diagonalHistory_succ, ih]

private theorem diagonalHistory_eq_ofFn
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (n : ℕ) :
    diagonalHistory gen P hP n =
      List.ofFn (fun i : Fin n ↦ diagonalStream gen P hP i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [diagonalHistory_succ, ih]
      simpa using
        (List.ofFn_succ'
          (fun i : Fin (n + 1) ↦ diagonalStream gen P hP i)).symm

private theorem diagonalFresh_mem
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (l : List α) :
    diagonalFresh gen P hP l ∈ P :=
  freshFrom_mem P hP _

private theorem diagonalFresh_not_mem_history
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (l : List α) :
    diagonalFresh gen P hP l ∉ l := by
  classical
  intro hmem
  exact (freshFrom_not_mem P hP (l.toFinset ∪ pastOutputs gen l))
    (Finset.mem_union_left _ (List.mem_toFinset.mpr hmem))

private theorem diagonalFresh_not_mem_outputs
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (l : List α) :
    diagonalFresh gen P hP l ∉ pastOutputs gen l := by
  classical
  intro hmem
  exact (freshFrom_not_mem P hP (l.toFinset ∪ pastOutputs gen l))
    (Finset.mem_union_right _ hmem)

private theorem diagonalStream_mem
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (n : ℕ) :
    diagonalStream gen P hP n ∈ P :=
  diagonalFresh_mem gen P hP _

private theorem diagonalStream_mem_history
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    {m n : ℕ} (hmn : m < n) :
    diagonalStream gen P hP m ∈ diagonalHistory gen P hP n := by
  rw [diagonalHistory_eq_ofFn]
  simp only [List.mem_ofFn]
  exact ⟨⟨m, hmn⟩, rfl⟩

private theorem diagonalStream_not_mem_own_history
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (n : ℕ) :
    diagonalStream gen P hP n ∉ diagonalHistory gen P hP n :=
  diagonalFresh_not_mem_history gen P hP _

private theorem diagonalStream_injective
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite) :
    Function.Injective (diagonalStream gen P hP) := by
  intro m n hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (diagonalStream_not_mem_own_history gen P hP n)
      (hmn ▸ diagonalStream_mem_history gen P hP hlt)
  · exact (diagonalStream_not_mem_own_history gen P hP m)
      (hmn.symm ▸ diagonalStream_mem_history gen P hP hgt)

private theorem diagonal_sample_card
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    (n : ℕ) :
    (GenLimit.Generic.sample (diagonalStream gen P hP) n).card = n := by
  classical
  rw [← GenLimit.Generic.sequenceSample_prefix,
    GenLimit.Generic.sequenceSample, Finset.card_image_iff.mpr]
  · simp
  · intro i _hi j _hj hij
    exact Fin.ext (diagonalStream_injective gen P hP hij)

private theorem diagonal_listPrefix_eq
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    {n k : ℕ} (hnk : n ≤ k) :
    listPrefix (diagonalHistory gen P hP k) n
      (by simpa using hnk) =
        fun i : Fin n ↦ diagonalStream gen P hP i := by
  funext i
  simp [listPrefix, diagonalHistory_eq_ofFn]

private theorem diagonal_output_mem_pastOutputs
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    {n k : ℕ} (hnk : n ≤ k) :
    GenLimit.Generic.output gen (diagonalStream gen P hP) n ∈
      pastOutputs gen (diagonalHistory gen P hP k) := by
  classical
  unfold pastOutputs
  apply Finset.mem_image.mpr
  let i : Fin ((diagonalHistory gen P hP k).length + 1) :=
    ⟨n, by simpa using Nat.lt_succ_of_le hnk⟩
  refine ⟨i, Finset.mem_univ _, ?_⟩
  unfold GenLimit.Generic.output
  change gen n (listPrefix (diagonalHistory gen P hP k) n _) =
    gen n (fun j : Fin n ↦ diagonalStream gen P hP j)
  rw [diagonal_listPrefix_eq gen P hP hnk]

private theorem diagonal_output_not_mem_range
    (gen : GenLimit.Generic.Generator α) (P : Set α) (hP : P.Infinite)
    {n : ℕ}
    (hcorrect : GenLimit.Generic.CorrectAt gen P
      (diagonalStream gen P hP) n) :
    GenLimit.Generic.output gen (diagonalStream gen P hP) n ∉
      Set.range (diagonalStream gen P hP) := by
  classical
  rintro ⟨k, hk⟩
  by_cases hkn : k < n
  · exact hcorrect.2
      (GenLimit.Generic.mem_sample_iff.mpr ⟨k, hkn, hk⟩)
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    have hout := diagonal_output_mem_pastOutputs gen P hP hnk
    have hstreamNot := diagonalFresh_not_mem_outputs gen P hP
      (diagonalHistory gen P hP k)
    change diagonalStream gen P hP k ∉
      pastOutputs gen (diagonalHistory gen P hP k) at hstreamNot
    apply hstreamNot
    rw [hk]
    exact hout

/-- The hard half of Lemma 3.12. -/
theorem separation_class_not_nonuniformly_generatable
    {P N : Set α} (hP : P.Infinite) (_hN : N.Infinite)
    (hDisjoint : Disjoint P N) :
    ¬NonuniformlyGeneratable (limitNonuniformSeparationClass P N) := by
  classical
  rintro ⟨gen, hgen⟩
  have hPClass : P ∈ limitNonuniformSeparationClass P N :=
    mem_limitNonuniformSeparationClass_iff.mpr (Or.inr rfl)
  obtain ⟨dP, hdP⟩ := hgen P hPClass
  let stream := diagonalStream gen P hP
  have hstreamP : GenLimit.Generic.StreamIn stream P := by
    rintro x ⟨n, rfl⟩
    exact diagonalStream_mem gen P hP n
  have hcard : ∀ n, (GenLimit.Generic.sample stream n).card = n := by
    intro n
    exact diagonal_sample_card gen P hP n
  let A : Set α := Set.range stream
  have hAP : A ⊆ P := hstreamP
  let L : Set α := N ∪ A
  have hLClass : L ∈ limitNonuniformSeparationClass P N := by
    apply mem_limitNonuniformSeparationClass_iff.mpr
    exact Or.inl ⟨A, hAP, rfl⟩
  obtain ⟨dL, hdL⟩ := hgen L hLClass
  let s := max dP dL
  have hcorrectP : GenLimit.Generic.CorrectAt gen P stream s :=
    hdP stream hstreamP dP (hcard dP) s (Nat.le_max_left _ _)
  have houtputNotA : GenLimit.Generic.output gen stream s ∉ A := by
    exact diagonal_output_not_mem_range gen P hP hcorrectP
  have houtputNotN : GenLimit.Generic.output gen stream s ∉ N := by
    intro houtN
    exact Set.disjoint_left.mp hDisjoint hcorrectP.1 houtN
  have hstreamL : GenLimit.Generic.StreamIn stream L := by
    intro x hx
    exact Set.mem_union_right N hx
  have hcorrectL : GenLimit.Generic.CorrectAt gen L stream s :=
    hdL stream hstreamL dL (hcard dL) s (Nat.le_max_right _ _)
  rcases hcorrectL.1 with houtN | houtA
  · exact houtputNotN houtN
  · exact houtputNotA houtA

/-- The first component class in Lemma 4.2 has closure dimension zero. -/
theorem subsetConeClass_has_closure_dimension_zero
    {P N : Set α} (hN : N.Infinite) :
    HasClosureDimension (subsetConeClass P N) 0 := by
  refine ⟨?_, Or.inl rfl⟩
  intro sample _hcard _hVS
  apply hN.mono
  intro x hx L hL
  obtain ⟨A, _hAP, hLA⟩ := hL.1
  rw [hLA]
  exact Set.mem_union_left A hx

/-- The singleton all-`P` class in Lemma 4.2 has closure dimension zero. -/
theorem singleton_infinite_language_has_closure_dimension_zero
    {P : Set α} (hP : P.Infinite) :
    HasClosureDimension ({P} : GenLimit.Generic.LanguageClass α) 0 := by
  refine ⟨?_, Or.inl rfl⟩
  intro sample _hcard _hVS
  apply hP.mono
  intro x hx L hL
  have hLP : L = P := Set.mem_singleton_iff.mp hL.1
  rwa [hLP]

/-- Lemma 4.2 in its structural form: two closure-dimension-zero classes
whose union is not non-uniformly generatable. -/
theorem two_zero_closure_classes_union_not_nonuniform
    {P N : Set α} (hP : P.Infinite) (hN : N.Infinite)
    (hDisjoint : Disjoint P N) :
    HasClosureDimension (subsetConeClass P N) 0 ∧
      HasClosureDimension ({P} : GenLimit.Generic.LanguageClass α) 0 ∧
      ¬NonuniformlyGeneratable
        (subsetConeClass P N ∪ ({P} : Set (Set α))) := by
  exact ⟨subsetConeClass_has_closure_dimension_zero hN,
    singleton_infinite_language_has_closure_dimension_zero hP,
    separation_class_not_nonuniformly_generatable hP hN hDisjoint⟩

/-! ## The paper's concrete integer partition -/

/-- The positive integers, viewed as a subset of `ℤ`. -/
def paperPositiveIntegers : Set ℤ := {z | 0 < z}

/-- The non-positive integers, viewed as a subset of `ℤ`. -/
def paperNonpositiveIntegers : Set ℤ := {z | z ≤ 0}

theorem paperPositiveIntegers_infinite : paperPositiveIntegers.Infinite := by
  let f : ℕ → ℤ := fun n ↦ (n : ℤ) + 1
  have hf : Function.Injective f := by
    intro m n hmn
    have hcast : (m : ℤ) = (n : ℤ) := by
      dsimp [f] at hmn
      omega
    exact_mod_cast hcast
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨n, rfl⟩
  change 0 < (n : ℤ) + 1
  omega

theorem paperNonpositiveIntegers_infinite : paperNonpositiveIntegers.Infinite := by
  let f : ℕ → ℤ := fun n ↦ -(n : ℤ)
  have hf : Function.Injective f := by
    intro m n hmn
    have hcast : (m : ℤ) = (n : ℤ) := by
      dsimp [f] at hmn
      omega
    exact_mod_cast hcast
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨n, rfl⟩
  change -(n : ℤ) ≤ 0
  omega

theorem paper_integer_partition_disjoint :
    Disjoint paperPositiveIntegers paperNonpositiveIntegers := by
  rw [Set.disjoint_left]
  intro z hzP hzN
  change 0 < z at hzP
  change z ≤ 0 at hzN
  omega

/-- Lemma 3.12 (`lem:notnonunifgen`) with the exact integer class displayed
in the paper. -/
theorem exists_generatable_in_limit_not_nonuniformly_generatable :
    ∃ H : GenLimit.Generic.LanguageClass ℤ,
      UUS H ∧ GeneratableInLimit H ∧ ¬NonuniformlyGeneratable H := by
  let H := limitNonuniformSeparationClass
    paperPositiveIntegers paperNonpositiveIntegers
  refine ⟨H, ?_, ?_, ?_⟩
  · exact separation_class_uus paperPositiveIntegers_infinite
      paperNonpositiveIntegers_infinite
  · exact separation_class_generatable_in_limit
      paperPositiveIntegers_infinite paperNonpositiveIntegers_infinite
      paper_integer_partition_disjoint
  · exact separation_class_not_nonuniformly_generatable
      paperPositiveIntegers_infinite paperNonpositiveIntegers_infinite
      paper_integer_partition_disjoint

/-- Lemma 4.2 (`lem:nonunifclos`) with the same two integer classes used in
the source proof. -/
theorem exists_two_zero_closure_classes_union_not_nonuniform :
    ∃ H₁ H₂ : GenLimit.Generic.LanguageClass ℤ,
      HasClosureDimension H₁ 0 ∧ HasClosureDimension H₂ 0 ∧
        ¬NonuniformlyGeneratable (H₁ ∪ H₂) := by
  refine ⟨subsetConeClass paperPositiveIntegers paperNonpositiveIntegers,
    ({paperPositiveIntegers} : GenLimit.Generic.LanguageClass ℤ), ?_⟩
  exact two_zero_closure_classes_union_not_nonuniform
    paperPositiveIntegers_infinite paperNonpositiveIntegers_infinite
    paper_integer_partition_disjoint

end GenLimit.LiRamanTewari
