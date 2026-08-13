import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.AlternatingPhaseRecursion
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Cardinality

/-!
# Uncountability assertions for the overview Theorem 3.1 witness

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, overview Theorem 3.1 and detailed Theorem 4.1.

The existing development proves the two non-uniform generators and the hard
union lower bound from detailed Theorem 4.1.  This file proves overview
Theorem 3.1's two uncountability assertions for those same classes.  For each
class, every encoded deletion set contains an infinite even-code scaffold; an
arbitrary set of naturals controls the odd-code deletions.  Membership of the
corresponding odd probe recovers the encoded set, giving an injection from
`Set ℕ`.
-/

namespace GenLimit.UnionClosedness

/-! ## Infinite deletion-set encodings -/

/-- An infinite positive deletion set: all even-indexed positive codes,
plus the odd-indexed codes selected by `S`. -/
def positiveDeletionEncoding (S : Set ℕ) : Set ℤ :=
  {z |
    (∃ n : ℕ, z = positiveCode (2 * n)) ∨
      ∃ n : ℕ, n ∈ S ∧ z = positiveCode (2 * n + 1)}

/-- An infinite negative deletion set: all even-indexed negative codes,
plus the odd-indexed codes selected by `S`. -/
def negativeDeletionEncoding (S : Set ℕ) : Set ℤ :=
  {z |
    (∃ n : ℕ, z = negativeCode (2 * n)) ∨
      ∃ n : ℕ, n ∈ S ∧ z = negativeCode (2 * n + 1)}

theorem positiveDeletionEncoding_subset (S : Set ℕ) :
    positiveDeletionEncoding S ⊆ positiveIntegers := by
  rintro z (⟨n, rfl⟩ | ⟨n, _hn, rfl⟩)
  · exact positiveCode_mem _
  · exact positiveCode_mem _

theorem negativeDeletionEncoding_subset (S : Set ℕ) :
    negativeDeletionEncoding S ⊆ negativeIntegers := by
  rintro z (⟨n, rfl⟩ | ⟨n, _hn, rfl⟩)
  · exact negativeCode_mem _
  · exact negativeCode_mem _

theorem positiveDeletionEncoding_infinite (S : Set ℕ) :
    (positiveDeletionEncoding S).Infinite := by
  have heven :
      Set.range (fun n : ℕ => positiveCode (2 * n)) ⊆
        positiveDeletionEncoding S := by
    rintro _ ⟨n, rfl⟩
    exact Or.inl ⟨n, rfl⟩
  apply (Set.infinite_range_of_injective ?_).mono heven
  intro m n hmn
  have hindex : 2 * m = 2 * n :=
    positiveCode_injective hmn
  omega

theorem negativeDeletionEncoding_infinite (S : Set ℕ) :
    (negativeDeletionEncoding S).Infinite := by
  have heven :
      Set.range (fun n : ℕ => negativeCode (2 * n)) ⊆
        negativeDeletionEncoding S := by
    rintro _ ⟨n, rfl⟩
    exact Or.inl ⟨n, rfl⟩
  apply (Set.infinite_range_of_injective ?_).mono heven
  intro m n hmn
  have hindex : 2 * m = 2 * n :=
    negativeCode_injective hmn
  omega

@[simp] theorem oddPositive_mem_positiveDeletionEncoding
    (S : Set ℕ) (n : ℕ) :
    positiveCode (2 * n + 1) ∈ positiveDeletionEncoding S ↔
      n ∈ S := by
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hkS, hk⟩)
    · have hindex : 2 * n + 1 = 2 * k :=
        positiveCode_injective hk
      omega
    · have hindex : 2 * n + 1 = 2 * k + 1 :=
        positiveCode_injective hk
      have hnk : n = k := by omega
      simpa [hnk] using hkS
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

@[simp] theorem oddNegative_mem_negativeDeletionEncoding
    (S : Set ℕ) (n : ℕ) :
    negativeCode (2 * n + 1) ∈ negativeDeletionEncoding S ↔
      n ∈ S := by
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hkS, hk⟩)
    · have hindex : 2 * n + 1 = 2 * k :=
        negativeCode_injective hk
      omega
    · have hindex : 2 * n + 1 = 2 * k + 1 :=
        negativeCode_injective hk
      have hnk : n = k := by omega
      simpa [hnk] using hkS
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

/-! ## Injective class encodings -/

/-- The first Theorem 4.1 class with no negative deletions and a
positive deletion set encoding `S`. -/
def theorem41FirstEncodedLanguage (S : Set ℕ) : Set ℤ :=
  signedDeletionLanguage ∅ (positiveDeletionEncoding S)

/-- The second Theorem 4.1 class with a negative deletion set encoding
`S` and no positive deletions. -/
def theorem41SecondEncodedLanguage (S : Set ℕ) : Set ℤ :=
  signedDeletionLanguage (negativeDeletionEncoding S) ∅

theorem theorem41FirstEncodedLanguage_mem (S : Set ℕ) :
    theorem41FirstEncodedLanguage S ∈
      finiteNegativeInfinitePositiveClass := by
  exact
    ⟨∅, positiveDeletionEncoding S,
      Set.empty_subset _, Set.finite_empty,
      positiveDeletionEncoding_subset S,
      positiveDeletionEncoding_infinite S, rfl⟩

theorem theorem41SecondEncodedLanguage_mem (S : Set ℕ) :
    theorem41SecondEncodedLanguage S ∈
      infiniteNegativeFinitePositiveClass := by
  exact
    ⟨negativeDeletionEncoding S, ∅,
      negativeDeletionEncoding_subset S,
      negativeDeletionEncoding_infinite S,
      Set.empty_subset _, Set.finite_empty, rfl⟩

@[simp] theorem oddPositive_mem_theorem41FirstEncodedLanguage
    (S : Set ℕ) (n : ℕ) :
    positiveCode (2 * n + 1) ∈
        theorem41FirstEncodedLanguage S ↔
      n ∉ S := by
  have hpositive :
      positiveCode (2 * n + 1) ∈ positiveIntegers :=
    positiveCode_mem _
  have hnotNegative :
      positiveCode (2 * n + 1) ∉ negativeIntegers := by
    simp [negativeIntegers, positiveCode]
    omega
  simp [theorem41FirstEncodedLanguage, signedDeletionLanguage,
    hpositive, hnotNegative]

@[simp] theorem oddNegative_mem_theorem41SecondEncodedLanguage
    (S : Set ℕ) (n : ℕ) :
    negativeCode (2 * n + 1) ∈
        theorem41SecondEncodedLanguage S ↔
      n ∉ S := by
  have hnegative :
      negativeCode (2 * n + 1) ∈ negativeIntegers :=
    negativeCode_mem _
  have hnotPositive :
      negativeCode (2 * n + 1) ∉ positiveIntegers := by
    simp [positiveIntegers, negativeCode]
  simp [theorem41SecondEncodedLanguage, signedDeletionLanguage,
    hnegative, hnotPositive]

theorem theorem41FirstEncodedLanguage_injective :
    Function.Injective theorem41FirstEncodedLanguage := by
  classical
  intro S T hST
  apply Set.ext
  intro n
  have hprobe :=
    Set.ext_iff.mp hST (positiveCode (2 * n + 1))
  rw [oddPositive_mem_theorem41FirstEncodedLanguage,
    oddPositive_mem_theorem41FirstEncodedLanguage] at hprobe
  simpa using not_congr hprobe

theorem theorem41SecondEncodedLanguage_injective :
    Function.Injective theorem41SecondEncodedLanguage := by
  classical
  intro S T hST
  apply Set.ext
  intro n
  have hprobe :=
    Set.ext_iff.mp hST (negativeCode (2 * n + 1))
  rw [oddNegative_mem_theorem41SecondEncodedLanguage,
    oddNegative_mem_theorem41SecondEncodedLanguage] at hprobe
  simpa using not_congr hprobe

/-! ## Overview Theorem 3.1 cardinalities -/

/-- The first class used by overview Theorem 3.1 is uncountable. -/
theorem finiteNegativeInfinitePositiveClass_uncountable :
    ¬finiteNegativeInfinitePositiveClass.Countable := by
  intro hcountable
  let f : Set ℕ → finiteNegativeInfinitePositiveClass :=
    fun S =>
      ⟨theorem41FirstEncodedLanguage S,
        theorem41FirstEncodedLanguage_mem S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply theorem41FirstEncodedLanguage_injective
    exact congrArg Subtype.val hST
  letI : Countable finiteNegativeInfinitePositiveClass :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact powerSet_not_countable ℕ hpower

/-- The second class used by overview Theorem 3.1 is uncountable. -/
theorem infiniteNegativeFinitePositiveClass_uncountable :
    ¬infiniteNegativeFinitePositiveClass.Countable := by
  intro hcountable
  let f : Set ℕ → infiniteNegativeFinitePositiveClass :=
    fun S =>
      ⟨theorem41SecondEncodedLanguage S,
        theorem41SecondEncodedLanguage_mem S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply theorem41SecondEncodedLanguage_injective
    exact congrArg Subtype.val hST
  letI : Countable infiniteNegativeFinitePositiveClass :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact powerSet_not_countable ℕ hpower

theorem theorem_3_1_cardinalities :
    ¬finiteNegativeInfinitePositiveClass.Countable ∧
      ¬infiniteNegativeFinitePositiveClass.Countable :=
  ⟨finiteNegativeInfinitePositiveClass_uncountable,
    infiniteNegativeFinitePositiveClass_uncountable⟩

/-- A fixed witness for overview Theorem 3.1: the classes from detailed
Theorem 4.1 are both uncountable and non-uniformly generatable, while their
union is not generatable in the limit on injective presentations. -/
theorem theorem_3_1_witness :
    ¬finiteNegativeInfinitePositiveClass.Countable ∧
      GenLimit.Generic.NonuniformlyGeneratable
        finiteNegativeInfinitePositiveClass ∧
      ¬infiniteNegativeFinitePositiveClass.Countable ∧
      GenLimit.Generic.NonuniformlyGeneratable
        infiniteNegativeFinitePositiveClass ∧
      ¬GeneratableInLimitOnInjectivePresentations
        (finiteNegativeInfinitePositiveClass ∪
          infiniteNegativeFinitePositiveClass) :=
  ⟨finiteNegativeInfinitePositiveClass_uncountable,
    theorem_4_1_individual_classes.1,
    infiniteNegativeFinitePositiveClass_uncountable,
    theorem_4_1_individual_classes.2,
    theorem_4_1_union_not_generatable_on_injective_presentations⟩

end GenLimit.UnionClosedness
