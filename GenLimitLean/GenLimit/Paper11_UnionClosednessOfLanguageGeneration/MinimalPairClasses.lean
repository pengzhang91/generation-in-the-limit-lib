import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.MainClasses
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization

/-!
# The two language classes in detailed Theorem 4.3

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, detailed Theorem 4.3.

The first class contains every negative integer and an arbitrary subset of
the positive integers.  The second class contains an exact finite initial
segment `{-i, ..., -1}` of the negative integers and all but finitely many
positive integers.  This module defines those literal classes and proves the
positive half of the theorem: the first class is uncountable and uniformly
generatable, while the second is countable and non-uniformly generatable.
-/

namespace GenLimit.UnionClosedness

open GenLimit.Generic

/-- Detailed Theorem 4.3's first language `ℤ₋ ∪ A`. -/
def theorem43FirstLanguage (A : Set ℤ) : Set ℤ :=
  negativeIntegers ∪ A

/-- Detailed Theorem 4.3's first class: all negative integers together with
an arbitrary subset of the positive integers. -/
def theorem43FirstClass : LanguageClass ℤ :=
  {L | ∃ A : Set ℤ,
    A ⊆ positiveIntegers ∧ L = theorem43FirstLanguage A}

/-- The exact finite negative prefix `{-i, ..., -1}`.  The parameter `i`
is its cardinality, so the prefix is empty when `i = 0`. -/
def negativePrefix (i : ℕ) : Set ℤ :=
  ((Finset.range i).image negativeCode : Finset ℤ)

/-- Detailed Theorem 4.3's language
`{-i, ..., -1} ∪ (ℤ₊ \ B)`. -/
def theorem43SecondLanguage (i : ℕ) (B : Set ℤ) : Set ℤ :=
  negativePrefix i ∪ (positiveIntegers \ B)

/-- Detailed Theorem 4.3's second class.  The explicit language `ℕ` in the
paper is the case `i = 0`, `B = ∅`. -/
def theorem43SecondClass : LanguageClass ℤ :=
  {L | ∃ i : ℕ, ∃ B : Set ℤ,
    B ⊆ positiveIntegers ∧ B.Finite ∧
    (i = 0 → B = ∅) ∧
    L = theorem43SecondLanguage i B}

theorem negativePrefix_mem_iff (i k : ℕ) :
    negativeCode k ∈ negativePrefix i ↔ k < i := by
  classical
  simp [negativePrefix, negativeCode_injective.eq_iff]

theorem negativePrefix_finite (i : ℕ) :
    (negativePrefix i).Finite :=
  ((Finset.range i).image negativeCode).finite_toSet

theorem negativePrefix_subset_negativeIntegers (i : ℕ) :
    negativePrefix i ⊆ negativeIntegers := by
  intro z hz
  change z ∈ ((Finset.range i).image negativeCode : Finset ℤ) at hz
  obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hz
  exact negativeCode_mem k

theorem positiveIntegers_mem_theorem43SecondClass :
    positiveIntegers ∈ theorem43SecondClass := by
  refine
    ⟨0, ∅, Set.empty_subset _, Set.finite_empty,
      fun _ => rfl, ?_⟩
  simp [theorem43SecondLanguage, negativePrefix]

private theorem theorem43FirstLanguage_injective :
    Function.Injective
      (fun A : Set positiveIntegers =>
        theorem43FirstLanguage ((fun z : positiveIntegers => z.1) '' A)) := by
  intro A B hAB
  apply Set.ext
  intro p
  have hpNotNegative : p.1 ∉ negativeIntegers := by
    exact Int.not_lt_of_ge (Int.le_of_lt p.2)
  have hpImage (C : Set positiveIntegers) :
      p.1 ∈ (fun z : positiveIntegers => z.1) '' C ↔ p ∈ C := by
    constructor
    · rintro ⟨q, hq, hqp⟩
      have hqEq : q = p := Subtype.ext hqp
      simpa [hqEq] using hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  have hmem := Set.ext_iff.mp hAB p.1
  change
    p.1 ∈
        negativeIntegers ∪
          (fun z : positiveIntegers => z.1) '' A ↔
      p.1 ∈
        negativeIntegers ∪
          (fun z : positiveIntegers => z.1) '' B at hmem
  rw [Set.mem_union, Set.mem_union, hpImage, hpImage] at hmem
  simpa [hpNotNegative] using hmem

/-- The first detailed Theorem 4.3 class is uncountable. -/
theorem theorem43FirstClass_uncountable :
    ¬theorem43FirstClass.Countable := by
  letI : Infinite positiveIntegers :=
    positiveIntegers_infinite.to_subtype
  intro hcountable
  let f : Set positiveIntegers → theorem43FirstClass :=
    fun A =>
      ⟨theorem43FirstLanguage
          ((fun z : positiveIntegers => z.1) '' A),
        ⟨(fun z : positiveIntegers => z.1) '' A,
          by
            rintro z ⟨p, _hp, rfl⟩
            exact p.2,
          rfl⟩⟩
  have hf : Function.Injective f := by
    intro A B hAB
    apply theorem43FirstLanguage_injective
    exact congrArg Subtype.val hAB
  letI : Countable theorem43FirstClass := hcountable.to_subtype
  have hpower : Countable (Set positiveIntegers) := hf.countable
  exact powerSet_not_countable positiveIntegers hpower

/-- The descending negative sweep is uniformly correct for the first
detailed Theorem 4.3 class, from threshold zero. -/
theorem theorem43FirstClass_uniformlyGeneratable :
    GenLimit.Generic.UniformlyGeneratable theorem43FirstClass := by
  classical
  refine ⟨descendingNegativeGenerator, 0, ?_⟩
  intro L hL stream _hstream _t _ht s _hts
  obtain ⟨A, _hApositive, rfl⟩ := hL
  obtain ⟨n, _hsn, hout, hfresh⟩ :=
    descendingNegativeGenerator_spec (fun i : Fin s => stream i)
  have houtput :
      output descendingNegativeGenerator stream s =
        negativeCode n := hout
  constructor
  · rw [houtput]
    exact Or.inl (negativeCode_mem n)
  · rw [houtput]
    simpa [hout, GenLimit.Generic.sequenceSample_prefix] using hfresh

/-- Every language in the first detailed Theorem 4.3 class is infinite. -/
theorem theorem43FirstClass_uus :
    GenLimit.Generic.UUS theorem43FirstClass := by
  intro L hL
  obtain ⟨A, _hApositive, rfl⟩ := hL
  exact negativeIntegers_infinite.mono Set.subset_union_left

/-- The second detailed Theorem 4.3 class is countable. -/
theorem theorem43SecondClass_countable :
    theorem43SecondClass.Countable := by
  let finitePositiveSets : Set (Set ℤ) :=
    {B | B.Finite ∧ B ⊆ positiveIntegers}
  have hfinitePositiveSets : finitePositiveSets.Countable := by
    simpa [finitePositiveSets, and_comm] using
      Set.countable_setOf_finite_subset
        (Set.to_countable positiveIntegers)
  have hparameters :
      (Set.univ ×ˢ finitePositiveSets : Set (ℕ × Set ℤ)).Countable :=
    Set.countable_univ.prod hfinitePositiveSets
  have himage :
      ((fun p : ℕ × Set ℤ =>
          theorem43SecondLanguage p.1 p.2) ''
        (Set.univ ×ˢ finitePositiveSets :
          Set (ℕ × Set ℤ))).Countable :=
    hparameters.image _
  apply himage.mono
  intro L hL
  obtain
    ⟨i, B, hBpositive, hBfinite, _hzero, rfl⟩ := hL
  exact ⟨(i, B), ⟨Set.mem_univ _, ⟨hBfinite, hBpositive⟩⟩, rfl⟩

/-- Every language in the second detailed Theorem 4.3 class is infinite. -/
theorem theorem43SecondClass_uus :
    GenLimit.Generic.UUS theorem43SecondClass := by
  intro L hL
  obtain
    ⟨i, B, _hBpositive, hBfinite, _hzero, rfl⟩ := hL
  apply (positiveIntegers_infinite.diff hBfinite).mono
  exact Set.subset_union_right

/-- The second detailed Theorem 4.3 class is non-uniformly generatable by
P02's general theorem that every countable UUS class is non-uniformly
generatable.  The standard predicate records the generation guarantee; it
does not separately encode the paper's stronger prose claim that a generator
can operate "without examples." -/
theorem theorem43SecondClass_nonuniformlyGeneratable :
    GenLimit.Generic.NonuniformlyGeneratable theorem43SecondClass :=
  GenLimit.LiRamanTewari.countable_classes_are_nonuniformly_generatable
    theorem43SecondClass_uus theorem43SecondClass_countable

end GenLimit.UnionClosedness
