import GenLimit.Paper02_LearningTheory.FiniteConeCover
import GenLimit.Paper02_LearningTheory.LimitVsNonuniformSeparation
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization
import Mathlib.Data.Set.Countable

/-!
# The two Section 3 existence examples

This file formalizes Lemmas 3.4 and 3.9 of Li--Raman--Tewari,
*Generation through the Lens of Learning Theory*, arXiv:2410.13714v5 /
COLT 2025.  They occur before the already formalized characterization
theorems but were not part of the earlier checkpoint.

For Lemma 3.9 the source itself observes that the triangular-number and
even/odd arithmetic is inessential: one only needs pairwise indexed finite
blocks of unbounded size and two disjoint infinite tails.  `BlockUniverse`
is the direct typed realization of exactly that observation, avoiding an
irrelevant integer-arithmetic encoding while preserving the proof.
-/

namespace GenLimit.LiRamanTewari

/-! ## Lemma 3.4 -/

private theorem powerSet_not_countable (β : Type*)
    [Infinite β] [Countable β] : ¬Countable (Set β) := by
  intro hCountable
  letI : Countable (Set β) := hCountable
  let den : Denumerable β := Classical.choice (nonempty_denumerable β)
  let e : ℕ ≃ β := (@Denumerable.eqv β den).symm
  obtain ⟨f, hf⟩ :=
    (countable_iff_exists_surjective (α := Set β)).mp hCountable
  let D : Set β := {p | p ∉ f (e.symm p)}
  obtain ⟨n, hn⟩ := hf D
  let p : β := e n
  have hdiag : p ∈ D ↔ p ∉ D := by
    have hep : e.symm p = n := by simp [p]
    constructor
    · intro hp
      change p ∉ f (e.symm p) at hp
      rw [hep, hn] at hp
      exact hp
    · intro hp
      change p ∉ f (e.symm p)
      rw [hep, hn]
      exact hp
  by_cases hp : p ∈ D
  · exact (hdiag.mp hp) hp
  · exact hp (hdiag.mpr hp)

private theorem subtype_image_mem_iff
    {P : Set α} (A : Set P) (p : P) :
    p.1 ∈ ((fun q : P ↦ q.1) '' A : Set α) ↔ p ∈ A := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    have hqEq : q = p := Subtype.ext hqp
    simpa [hqEq] using hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- An upward cone is uncountable as soon as the complement of its base
contains an infinite set. -/
theorem upwardCone_not_countable [Countable α]
    {P N : Set α} (hP : P.Infinite) (hDisjoint : Disjoint P N) :
    ¬(upwardCone N).Countable := by
  letI : Infinite P := hP.to_subtype
  let f : Set P → Set α := fun A ↦ N ∪ (fun p : P ↦ p.1) '' A
  have hfMem : ∀ A, f A ∈ upwardCone N := by
    intro A
    exact Set.subset_union_left
  let g : Set P → (upwardCone N) := fun A ↦ ⟨f A, hfMem A⟩
  have hg : Function.Injective g := by
    intro A B hAB
    have hsets : f A = f B := congrArg Subtype.val hAB
    apply Set.ext
    intro p
    have hpNotN : p.1 ∉ N := by
      intro hpN
      exact Set.disjoint_left.mp hDisjoint p.2 hpN
    have hmem := Set.ext_iff.mp hsets p.1
    change (p.1 ∈ N ∪ (fun q : P ↦ q.1) '' A) ↔
      (p.1 ∈ N ∪ (fun q : P ↦ q.1) '' B) at hmem
    rw [Set.mem_union, Set.mem_union, subtype_image_mem_iff,
      subtype_image_mem_iff] at hmem
    simpa [hpNotN] using hmem
  intro hCountable
  letI : Countable (upwardCone N) := hCountable.to_subtype
  have hDomainCountable : Countable (Set P) := hg.countable
  exact powerSet_not_countable P hDomainCountable

/-- Lemma 3.4 (`lem:uncountunifgen`) with the exact integer upward cone from
the source proof.

Source repair: the paper claims that
`⟨x⟩_H = ℤ_{≤ 0}` for every `x : ℤ`.  When `x > 0`, the correct singleton
closure is `ℤ_{≤ 0} ∪ {x}`, since every language in the corresponding version
space must contain the observed positive example `x`.  This does not affect
the argument: every consistent nonempty sample has a common core containing
the infinite base `ℤ_{≤ 0}`, which is sufficient to prove `C(H) = 0`.  The
Lean proof below uses this correct inclusion rather than the printed
equality. -/
theorem exists_uncountable_uniformly_generatable_class :
    ∃ H : GenLimit.Generic.LanguageClass ℤ,
      ¬H.Countable ∧ UUS H ∧ UniformlyGeneratable H := by
  let H := upwardCone paperNonpositiveIntegers
  refine ⟨H, ?_, ?_, ?_⟩
  · exact upwardCone_not_countable paperPositiveIntegers_infinite
      paper_integer_partition_disjoint
  · intro L hL
    exact paperNonpositiveIntegers_infinite.mono hL
  · apply (uniform_generatability_iff_finite_closure_dimension
      (H := H) (by
        intro L hL
        exact paperNonpositiveIntegers_infinite.mono hL)).mpr
    exact upwardCone_has_finite_closure_dimension
      paperNonpositiveIntegers_infinite

/-! ## Lemma 3.9 -/

/-- A countable universe containing indexed finite blocks and two tails. -/
abbrev BlockUniverse := (ℕ × ℕ) ⊕ (Bool × ℕ)

def blockFinset (d : ℕ) : Finset BlockUniverse :=
  (Finset.range d).image (fun j ↦ Sum.inl (d, j))

def blockSet (d : ℕ) : Set BlockUniverse := ↑(blockFinset d)

def blockTail (b : Bool) : Set BlockUniverse :=
  Set.range (fun n : ℕ ↦ Sum.inr (b, n))

def blockLanguage (b : Bool) (d : ℕ) : Set BlockUniverse :=
  blockSet d ∪ blockTail b

def blockSeparationClass : GenLimit.Generic.LanguageClass BlockUniverse :=
  Set.range (fun p : Bool × ℕ ↦ blockLanguage p.1 p.2)

theorem blockFinset_card (d : ℕ) : (blockFinset d).card = d := by
  classical
  unfold blockFinset
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _hi j _hj hij
    simpa using hij

theorem blockTail_infinite (b : Bool) : (blockTail b).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n hmn
  simpa using hmn

theorem blockSeparationClass_countable : blockSeparationClass.Countable :=
  Set.countable_range _

theorem blockSeparationClass_uus : UUS blockSeparationClass := by
  intro L hL
  obtain ⟨⟨b, d⟩, rfl⟩ := hL
  exact (blockTail_infinite b).mono Set.subset_union_right

private theorem blockLanguage_mem (b : Bool) (d : ℕ) :
    blockLanguage b d ∈ blockSeparationClass :=
  ⟨(b, d), rfl⟩

private theorem blockSet_subset_blockLanguage (b : Bool) (d : ℕ) :
    blockSet d ⊆ blockLanguage b d :=
  Set.subset_union_left

theorem commonCore_blockSeparationClass_eq (d : ℕ) :
    commonCore blockSeparationClass (blockFinset d) = blockSet d := by
  apply Set.Subset.antisymm
  · intro x hx
    have hFalse := hx (blockLanguage false d)
      ⟨blockLanguage_mem false d, blockSet_subset_blockLanguage false d⟩
    have hTrue := hx (blockLanguage true d)
      ⟨blockLanguage_mem true d, blockSet_subset_blockLanguage true d⟩
    rcases x with x | ⟨b, n⟩
    · simpa [blockLanguage, blockTail] using hFalse
    · cases b with
      | false => simpa [blockLanguage, blockTail] using hTrue
      | true => simpa [blockLanguage, blockTail] using hFalse
  · exact sample_subset_commonCore

theorem blockSeparationClass_infinite_closure_dimension :
    HasInfiniteClosureDimension blockSeparationClass := by
  intro d
  refine ⟨blockFinset d, (blockFinset_card d).ge, ?_⟩
  constructor
  · exact ⟨blockLanguage false d, blockLanguage_mem false d,
      blockSet_subset_blockLanguage false d⟩
  · rw [show GenLimit.Generic.commonCore blockSeparationClass (blockFinset d) =
        blockSet d from commonCore_blockSeparationClass_eq d]
    exact (blockFinset d).finite_toSet

/-- Lemma 3.9 (`lem:nonunifvsunifgen`). -/
theorem exists_countable_nonuniform_not_uniform_class :
    ∃ H : GenLimit.Generic.LanguageClass BlockUniverse,
      H.Countable ∧ UUS H ∧ NonuniformlyGeneratable H ∧
        ¬UniformlyGeneratable H := by
  refine ⟨blockSeparationClass, blockSeparationClass_countable,
    blockSeparationClass_uus, ?_, ?_⟩
  · exact countable_classes_are_nonuniformly_generatable
      blockSeparationClass_uus blockSeparationClass_countable
  · exact closure_dimension_necessity blockSeparationClass_uus
      blockSeparationClass_infinite_closure_dimension

end GenLimit.LiRamanTewari
