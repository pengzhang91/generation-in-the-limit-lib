import GenLimit.Paper15_PartialEnumeration.FullTextSeparation

/-!
# A counterexample to separation from arbitrary partial texts

The exact-full-text qualification in `corollary_4_10_fullText` is essential.
Even if the observed partial language is required to be infinite, two
incomparable infinite languages may share it.  A stream confined to that
common language supplies no finite positive-history refutation of either
candidate.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration
namespace FullTopology
namespace PartialSeparationCounterexample

/-- An injective stream whose range leaves `0` and `1` available as private
markers for two candidate languages. -/
def commonStream (n : ℕ) : ℕ := n + 2

def commonLanguage : Language := Set.range commonStream

def leftLanguage : Language := commonLanguage ∪ {0}

def rightLanguage : Language := commonLanguage ∪ {1}

def counterexampleClass : Set Language := {leftLanguage, rightLanguage}

theorem commonStream_injective : Function.Injective commonStream := by
  intro m n h
  simp only [commonStream] at h
  omega

theorem commonLanguage_infinite : commonLanguage.Infinite :=
  Set.infinite_range_of_injective commonStream_injective

theorem leftLanguage_infinite : leftLanguage.Infinite :=
  commonLanguage_infinite.mono Set.subset_union_left

theorem rightLanguage_infinite : rightLanguage.Infinite :=
  commonLanguage_infinite.mono Set.subset_union_left

@[simp] theorem zero_not_mem_commonLanguage : 0 ∉ commonLanguage := by
  rintro ⟨n, hn⟩
  simp only [commonStream] at hn
  omega

@[simp] theorem one_not_mem_commonLanguage : 1 ∉ commonLanguage := by
  rintro ⟨n, hn⟩
  simp only [commonStream] at hn
  omega

theorem left_not_subset_right : ¬ leftLanguage ⊆ rightLanguage := by
  intro hSubset
  have hZero : 0 ∈ rightLanguage := hSubset (by simp [leftLanguage])
  simp [rightLanguage] at hZero

theorem right_not_subset_left : ¬ rightLanguage ⊆ leftLanguage := by
  intro hSubset
  have hOne : 1 ∈ leftLanguage := hSubset (by simp [rightLanguage])
  simp [leftLanguage] at hOne

theorem counterexampleClass_inclusionAntichain :
    InclusionAntichain counterexampleClass := by
  intro K L hSubset
  rcases K with ⟨K, hK⟩
  rcases L with ⟨L, hL⟩
  simp only [counterexampleClass, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hK hL
  rcases hK with rfl | rfl <;> rcases hL with rfl | rfl
  · rfl
  · exact (left_not_subset_right hSubset).elim
  · exact (right_not_subset_left hSubset).elim
  · rfl

/-- The two-point counterexample class satisfies the topological `T₁`
condition appearing in Corollary 4.10. -/
theorem counterexampleClass_tOneSpace : TOneSpace counterexampleClass :=
  (tOneSpace_iff_inclusionAntichain counterexampleClass).mpr
    counterexampleClass_inclusionAntichain

theorem commonStream_presents_commonLanguage :
    Presents commonStream commonLanguage := rfl

/-- A positive history drawn from a sublanguage of `L` cannot refute `L`.
This is independent of the stream's order and of the prefix length. -/
theorem no_refutation_of_presented_sublanguage
    {stream : ℕ → ℕ} {A L : Language}
    (hPresents : Presents stream A) (hSubset : A ⊆ L) (t : ℕ) :
    ¬ RefutedByHistory (textPrefix stream t) L := by
  rintro ⟨x, hxHistory, hxL⟩
  rw [mem_textPrefix_iff] at hxHistory
  obtain ⟨s, _hs, hsx⟩ := hxHistory
  apply hxL
  apply hSubset
  rw [← hPresents]
  exact ⟨s, hsx⟩

theorem commonStream_never_refutes_left (t : ℕ) :
    ¬ RefutedByHistory (textPrefix commonStream t) leftLanguage :=
  no_refutation_of_presented_sublanguage
    commonStream_presents_commonLanguage Set.subset_union_left t

theorem commonStream_never_refutes_right (t : ℕ) :
    ¬ RefutedByHistory (textPrefix commonStream t) rightLanguage :=
  no_refutation_of_presented_sublanguage
    commonStream_presents_commonLanguage Set.subset_union_left t

/-- Separation under the source's stronger "possibly a subset" reading,
still granting the learner an infinite observed sublanguage. -/
def SeparatesFromInfinitePartialTexts (K L : Language) : Prop :=
  ∀ stream : ℕ → ℕ, (Set.range stream).Infinite →
    Set.range stream ⊆ K →
      ∃ T, ∀ t, T ≤ t →
        RefutedByHistory (textPrefix stream t) L

theorem left_not_separated_from_right_on_infinite_partial_texts :
    ¬ SeparatesFromInfinitePartialTexts leftLanguage rightLanguage := by
  intro hSeparates
  obtain ⟨T, hT⟩ := hSeparates commonStream commonLanguage_infinite
    Set.subset_union_left
  exact commonStream_never_refutes_right T (hT T le_rfl)

theorem right_not_separated_from_left_on_infinite_partial_texts :
    ¬ SeparatesFromInfinitePartialTexts rightLanguage leftLanguage := by
  intro hSeparates
  obtain ⟨T, hT⟩ := hSeparates commonStream commonLanguage_infinite
    Set.subset_union_left
  exact commonStream_never_refutes_left T (hT T le_rfl)

/-- Machine-checked diagnostic for the failed stronger reading: the class is
`T₁`, both candidates and their common observed language are infinite, the
candidates are incomparable, yet the common exact stream never supplies a
finite refutation of either one. -/
theorem possiblySubset_corollary_4_10_counterexample :
    TOneSpace counterexampleClass ∧
      commonLanguage.Infinite ∧
      leftLanguage.Infinite ∧ rightLanguage.Infinite ∧
      (¬ leftLanguage ⊆ rightLanguage) ∧
      (¬ rightLanguage ⊆ leftLanguage) ∧
      Presents commonStream commonLanguage ∧
      commonLanguage ⊆ leftLanguage ∧
      commonLanguage ⊆ rightLanguage ∧
      (∀ t, ¬ RefutedByHistory (textPrefix commonStream t) leftLanguage) ∧
      (∀ t, ¬ RefutedByHistory (textPrefix commonStream t) rightLanguage) := by
  exact ⟨counterexampleClass_tOneSpace,
    commonLanguage_infinite,
    leftLanguage_infinite,
    rightLanguage_infinite,
    left_not_subset_right,
    right_not_subset_left,
    commonStream_presents_commonLanguage,
    Set.subset_union_left,
    Set.subset_union_left,
    commonStream_never_refutes_left,
    commonStream_never_refutes_right⟩

end PartialSeparationCounterexample
end FullTopology
end PartialEnumeration
end KleinbergWei
end GenLimit
