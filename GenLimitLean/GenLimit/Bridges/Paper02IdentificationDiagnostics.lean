import GenLimit.Bridges.AngluinToPaper02

/-!
# Diagnostic for P02 Theorem 2.3

Angluin's 1980 Theorem 1 concerns an indexed family and therefore has a
countable extensional range.  P02 restates its semantic tell-tale condition
for an arbitrary hypothesis class.  That restatement is false without the
lost countability assumption.

The counterexample below assigns to every `A : Set ℕ` a language containing
exactly one of `(n, true)` and `(n, false)` for each `n`.  These languages form
an uncountable inclusion antichain.  Hence the empty set is a tell-tale for
every member, while no language-valued finite-history identifier can identify
the whole class: over a countable example space it has only countably many
possible outputs.
-/

namespace GenLimit.Paper02IdentificationDiagnostics

abbrev SelectorUniverse := ℕ × Bool

/-- The language encoding the characteristic function of `A`, with exactly
one selected point over each natural number. -/
def selectorLanguage (A : Set ℕ) : Set SelectorUniverse :=
  {p | (p.2 = true) ↔ p.1 ∈ A}

@[simp] theorem mem_selectorLanguage_true (A : Set ℕ) (n : ℕ) :
    (n, true) ∈ selectorLanguage A ↔ n ∈ A := by
  simp [selectorLanguage]

@[simp] theorem mem_selectorLanguage_false (A : Set ℕ) (n : ℕ) :
    (n, false) ∈ selectorLanguage A ↔ n ∉ A := by
  simp [selectorLanguage]

/-- The canonical exact positive presentation of `selectorLanguage A`. -/
noncomputable def selectorPoint (A : Set ℕ) (n : ℕ) : SelectorUniverse := by
  classical
  exact if n ∈ A then (n, true) else (n, false)

@[simp] theorem selectorPoint_fst (A : Set ℕ) (n : ℕ) :
    (selectorPoint A n).1 = n := by
  classical
  rw [selectorPoint]
  split <;> rfl

theorem selectorPoint_mem (A : Set ℕ) (n : ℕ) :
    selectorPoint A n ∈ selectorLanguage A := by
  classical
  by_cases hn : n ∈ A <;> simp [selectorPoint, hn]

theorem selectorPoint_injective (A : Set ℕ) :
    Function.Injective (selectorPoint A) := by
  intro m n hmn
  simpa using congrArg Prod.fst hmn

theorem selectorPoint_presents (A : Set ℕ) :
    GenLimit.Generic.Presents (selectorPoint A) (selectorLanguage A) := by
  apply Set.Subset.antisymm
  · rintro p ⟨n, rfl⟩
    exact selectorPoint_mem A n
  · rintro ⟨n, b⟩ hp
    cases b with
    | false =>
        have hn : n ∉ A := mem_selectorLanguage_false A n |>.mp hp
        exact ⟨n, by simp [selectorPoint, hn]⟩
    | true =>
        have hn : n ∈ A := mem_selectorLanguage_true A n |>.mp hp
        exact ⟨n, by simp [selectorPoint, hn]⟩

theorem selectorLanguage_infinite (A : Set ℕ) :
    (selectorLanguage A).Infinite := by
  rw [← selectorPoint_presents A]
  exact Set.infinite_range_of_injective (selectorPoint_injective A)

/-- Inclusion between selector languages already forces equality of their
codes, so the class is an inclusion antichain. -/
theorem selectorLanguage_subset_iff {A B : Set ℕ} :
    selectorLanguage A ⊆ selectorLanguage B ↔ A = B := by
  constructor
  · intro hSubset
    apply Set.ext
    intro n
    constructor
    · intro hnA
      exact (mem_selectorLanguage_true B n).mp
        (hSubset ((mem_selectorLanguage_true A n).mpr hnA))
    · intro hnB
      by_contra hnA
      have hnNotB := (mem_selectorLanguage_false B n).mp
        (hSubset ((mem_selectorLanguage_false A n).mpr hnA))
      exact hnNotB hnB
  · rintro rfl
    exact Set.Subset.rfl

theorem selectorLanguage_injective :
    Function.Injective selectorLanguage := by
  intro A B hAB
  apply selectorLanguage_subset_iff.mp
  rw [hAB]

/-- The extensional class containing every selector language. -/
def selectorClass : GenLimit.Generic.LanguageClass SelectorUniverse :=
  Set.range selectorLanguage

private theorem powerSetNat_not_countable : ¬Countable (Set ℕ) := by
  intro hCountable
  obtain ⟨enumerate, hEnumerate⟩ :=
    (countable_iff_exists_surjective (α := Set ℕ)).mp hCountable
  let diagonal : Set ℕ := {n | n ∉ enumerate n}
  obtain ⟨n, hn⟩ := hEnumerate diagonal
  have hdiag : n ∈ diagonal ↔ n ∉ diagonal := by
    change n ∉ enumerate n ↔ n ∉ diagonal
    rw [hn]
  by_cases hmem : n ∈ diagonal
  · exact (hdiag.mp hmem) hmem
  · exact hmem (hdiag.mpr hmem)

theorem selectorClass_not_countable : ¬selectorClass.Countable := by
  intro hCountable
  let embed : Set ℕ → selectorClass := fun A ↦
    ⟨selectorLanguage A, ⟨A, rfl⟩⟩
  have hInjective : Function.Injective embed := by
    intro A B hAB
    apply selectorLanguage_injective
    exact congrArg Subtype.val hAB
  letI : Countable selectorClass := hCountable.to_subtype
  exact powerSetNat_not_countable hInjective.countable

theorem selectorClass_uus : GenLimit.Generic.UUS selectorClass := by
  rintro L ⟨A, rfl⟩
  exact selectorLanguage_infinite A

/-- Every selector language has the empty tell-tale, because the class is an
inclusion antichain. -/
theorem selectorClass_extensionalTellTaleCondition :
    GenLimit.Angluin.ExtensionalTellTaleCondition selectorClass := by
  rintro L ⟨A, rfl⟩
  refine ⟨∅, by simp, ?_⟩
  rintro K ⟨B, rfl⟩ _ hBA
  have hEq : B = A := selectorLanguage_subset_iff.mp hBA
  subst B
  exact Set.Subset.rfl

theorem selectorClass_not_extensionallyIdentifiable :
    ¬GenLimit.Angluin.ExtensionallyIdentifiable selectorClass := by
  intro hIdentifiable
  apply selectorClass_not_countable
  exact GenLimit.Angluin.extensionallyIdentifiable_implies_countable
    (fun L hL ↦ (selectorClass_uus L hL).nonempty)
    hIdentifiable

/-- The arbitrary-class wording of P02 Theorem 2.3 is false.  The example
space is countable and every language is infinite, but the tell-tale side
holds while identification fails.  This does not contradict Angluin's
original theorem, whose language family is indexed and hence countable. -/
theorem printed_theorem_2_3_is_false :
    ∃ H : GenLimit.Generic.LanguageClass SelectorUniverse,
      ¬H.Countable ∧ GenLimit.Generic.UUS H ∧
        GenLimit.Angluin.ExtensionalTellTaleCondition H ∧
        ¬GenLimit.Angluin.ExtensionallyIdentifiable H :=
  ⟨selectorClass, selectorClass_not_countable, selectorClass_uus,
    selectorClass_extensionalTellTaleCondition,
    selectorClass_not_extensionallyIdentifiable⟩

end GenLimit.Paper02IdentificationDiagnostics
