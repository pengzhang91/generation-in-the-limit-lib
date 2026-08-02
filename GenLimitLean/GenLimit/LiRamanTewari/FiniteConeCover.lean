import GenLimit.LiRamanTewari.GenerationInLimitCharacterization

/-!
# The finite-cone corollary after Theorem 3.10

This file formalizes Corollary 3.11 of Li--Raman--Tewari,
*Generation through the Lens of Learning Theory*, arXiv:2410.13714v5 /
COLT 2025 (the unlabelled corollary immediately after Theorem 3.10 in the
pinned source).

The paper writes
`H_i = {x \mapsto 1{x \in S_i \cup A} : A \in 2^N}`.  As a class of
supports this is exactly the upward cone of `S_i`, namely all sets containing
`S_i`.  The proof below keeps that equality visible rather than silently
replacing the displayed class.
-/

namespace GenLimit.LiRamanTewari

/-- The class represented in the paper by
`{S \cup A : A \subseteq \alpha}`. -/
def upwardCone (S : Set α) : GenLimit.Generic.LanguageClass α :=
  {L | S ⊆ L}

theorem mem_upwardCone_iff {S L : Set α} :
    L ∈ upwardCone S ↔ S ⊆ L :=
  Iff.rfl

/-- The paper's displayed union-with-an-arbitrary-set representation is
literally the upward cone. -/
theorem upwardCone_eq_union_class (S : Set α) :
    upwardCone S = {L : Set α | ∃ A : Set α, L = S ∪ A} := by
  ext L
  constructor
  · intro hSL
    exact ⟨L, (Set.union_eq_right.mpr hSL).symm⟩
  · rintro ⟨A, rfl⟩
    exact Set.subset_union_left

/-- Every upward cone with an infinite base has closure dimension zero. -/
theorem upwardCone_has_closure_dimension_zero
    {S : Set α} (hS : S.Infinite) :
    HasClosureDimension (upwardCone S) 0 := by
  refine ⟨?_, Or.inl rfl⟩
  intro sample _hcard _hVS
  apply hS.mono
  intro x hx L hL
  exact hL.1 hx

theorem upwardCone_has_finite_closure_dimension
    {S : Set α} (hS : S.Infinite) :
    HasFiniteClosureDimension (upwardCone S) :=
  ⟨0, upwardCone_has_closure_dimension_zero hS⟩

private theorem finite_upwardCone_cover_uus
    {n : ℕ} (bases : Fin n → Set α)
    (hInfinite : ∀ i, (bases i).Infinite) :
    UUS (⋃ i, upwardCone (bases i)) := by
  intro L hL
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hL
  exact (hInfinite i).mono hi

/-- Corollary 3.11, in a type-generic form.

For a finite list of infinite base sets, the union of the classes of all
languages containing each base is generatable in the limit. -/
theorem finite_union_of_infinite_upwardCones_generatable_in_limit
    [Nonempty α] [Countable α]
    {n : ℕ} (bases : Fin n → Set α)
    (hInfinite : ∀ i, (bases i).Infinite) :
    GeneratableInLimit (⋃ i, upwardCone (bases i)) := by
  let classes : Fin n → GenLimit.Generic.LanguageClass α :=
    fun i ↦ upwardCone (bases i)
  apply finite_closure_dimension_cover_implies_generatable_in_limit
    (finite_upwardCone_cover_uus bases hInfinite)
  refine ⟨n, classes, rfl, ?_⟩
  intro i
  exact upwardCone_has_finite_closure_dimension (hInfinite i)

/-- Corollary 3.11 exactly on the paper's example space `ℕ`, with the
displayed `S_i \cup A` class expanded rather than abbreviated. -/
theorem finite_union_of_paper_cone_classes_generatable_in_limit
    {n : ℕ} (bases : Fin n → Set ℕ)
    (hInfinite : ∀ i, (bases i).Infinite) :
    GeneratableInLimit
      (⋃ i, {L : Set ℕ | ∃ A : Set ℕ, L = bases i ∪ A}) := by
  rw [show (⋃ i, {L : Set ℕ | ∃ A : Set ℕ, L = bases i ∪ A}) =
      ⋃ i, upwardCone (bases i) by
    congr 1
    funext i
    exact (upwardCone_eq_union_class (bases i)).symm]
  exact finite_union_of_infinite_upwardCones_generatable_in_limit bases hInfinite

end GenLimit.LiRamanTewari
