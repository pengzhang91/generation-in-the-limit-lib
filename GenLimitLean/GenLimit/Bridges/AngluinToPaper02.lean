import GenLimit.Core.IdentificationGeneration
import GenLimit.Bridges.IndexedFamilyToClass
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper02_LearningTheory.Hierarchy
import Mathlib.Logic.Equiv.List

/-!
# Angluin identification to #02 generation

This bridge makes explicit that Angluin's indexed semantic identifier has
exactly the stabilization interface expected by the paper-independent
identification-to-generation theorem.  No generator proof is duplicated here.
-/

namespace GenLimit.Angluin

/-- Definition 2.6's semantic identifier, represented extensionally by the
positive support of each hypothesis. -/
abbrev ExtensionalIdentifier (α : Type*) :=
  GenLimit.Learner α (GenLimit.Generic.Language α)

/-- Definition 2.7: on every exact positive presentation, the language-valued
guess eventually stabilizes to the target itself. -/
def ExtensionalIdentifies
    (M : ExtensionalIdentifier α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream L →
      GenLimit.IdentifiesInLimit id M stream L

/-- Existence of a possibly noncomputable identifier in the literal
language-valued interface of P02 Definition 2.7. -/
def ExtensionallyIdentifiable
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ M : ExtensionalIdentifier α, ExtensionalIdentifies M H

/-- The extensional form of Angluin's finite tell-tale condition: each target
has finite positive evidence excluding every proper sublanguage in the class. -/
def ExtensionalTellTaleCondition
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∃ T : Finset α,
    (↑T : Set α) ⊆ L ∧
      ∀ K, K ∈ H → (↑T : Set α) ⊆ K → K ⊆ L → L ⊆ K

/-- Every nonempty language over a countable example space has an exact
positive presentation. -/
theorem exists_presentation_of_nonempty [Countable α]
    {L : GenLimit.Generic.Language α} (hL : L.Nonempty) :
    ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream L := by
  classical
  letI : Nonempty L := hL.to_subtype
  obtain ⟨enumerate, hEnumerate⟩ := exists_surjective_nat L
  let stream : GenLimit.Generic.Stream α := fun n ↦ (enumerate n).1
  refine ⟨stream, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨n, rfl⟩
    exact (enumerate n).2
  · intro x hx
    obtain ⟨n, hn⟩ := hEnumerate ⟨x, hx⟩
    exact ⟨n, congrArg Subtype.val hn⟩

/-- A language-valued identifier on a countable example space can identify
only countably many nonempty languages: every successfully identified target
must occur among the identifier's countably many finite-history outputs. -/
theorem extensionallyIdentifiable_implies_countable [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hNonempty : ∀ L, L ∈ H → L.Nonempty)
    (hIdentifiable : ExtensionallyIdentifiable H) :
    H.Countable := by
  obtain ⟨M, hM⟩ := hIdentifiable
  apply (Set.countable_range M).mono
  intro L hL
  obtain ⟨stream, hPresentation⟩ :=
    exists_presentation_of_nonempty (hNonempty L hL)
  obtain ⟨guess, hguess, T, hstable⟩ :=
    hM L hL stream hPresentation
  refine ⟨GenLimit.textPrefix stream T, ?_⟩
  exact (hstable T le_rfl).trans hguess

/-- Angluin's indexed Condition 2 depends only on the extensional range of
the chosen family. -/
theorem conditionTwo_iff_extensionalTellTaleCondition
    {H : GenLimit.Generic.LanguageClass α}
    (E : GenLimit.Bridge.ClassEnumeration H) :
    ConditionTwo E.family ↔ ExtensionalTellTaleCondition H := by
  constructor
  · intro hCondition L hL
    obtain ⟨i, hi⟩ := E.exists_index hL
    obtain ⟨T, hT⟩ := hCondition i
    refine ⟨T, ?_, ?_⟩
    · simpa [hi] using hT.1
    · intro K hK hTK hKL
      obtain ⟨j, hj⟩ := E.exists_index hK
      have hback := hT.2 j (by simpa [hj] using hTK)
        (by simpa [hi, hj] using hKL)
      simpa [hi, hj] using hback
  · intro hExt i
    obtain ⟨T, hT, hmin⟩ := hExt (E.family i) (E.family_mem i)
    refine ⟨T, hT, ?_⟩
    intro j hTj hji
    exact hmin (E.family j) (E.family_mem j) hTj hji

/-- An indexed Angluin identifier induces the literal language-valued P02
identifier by interpreting each conjectured index. -/
theorem semanticallyInferrable_implies_extensionallyIdentifiable
    {H : GenLimit.Generic.LanguageClass α}
    (E : GenLimit.Bridge.ClassEnumeration H)
    (hInfer : SemanticallyInferrable E.family) :
    ExtensionallyIdentifiable H := by
  obtain ⟨M, hM⟩ := hInfer
  let Mext : ExtensionalIdentifier α := fun history ↦ E.family (M history)
  refine ⟨Mext, ?_⟩
  intro L hL stream hPresentation
  obtain ⟨z, hz⟩ := E.exists_index hL
  obtain ⟨j, hj, T, hT⟩ := hM z stream (by simpa [hz] using hPresentation)
  refine ⟨L, rfl, T, ?_⟩
  intro t ht
  change E.family (M (GenLimit.textPrefix stream t)) = L
  have hguess : M (GenLimit.textPrefix stream t) = j := hT t ht
  calc
    E.family (M (GenLimit.textPrefix stream t)) = E.family j :=
      congrArg E.family hguess
    _ = E.family z := hj
    _ = L := hz

/-- Choose the least index naming `L`, with the irrelevant default `0` for a
language outside the enumerated class. -/
noncomputable def leastName
    {H : GenLimit.Generic.LanguageClass α}
    (E : GenLimit.Bridge.ClassEnumeration H)
    (L : GenLimit.Generic.Language α) : ℕ := by
  classical
  exact if h : ∃ i, E.family i = L then Nat.find h else 0

theorem leastName_spec
    {H : GenLimit.Generic.LanguageClass α}
    (E : GenLimit.Bridge.ClassEnumeration H)
    {L : GenLimit.Generic.Language α} (hL : L ∈ H) :
    E.family (leastName E L) = L := by
  classical
  let hex := E.exists_index hL
  simp only [leastName, dif_pos hex]
  exact Nat.find_spec hex

/-- A language-valued P02 identifier can be named by a chosen enumeration:
at each history choose the least index denoting its current language guess,
falling back to `0` only for guesses outside the class. -/
theorem extensionallyIdentifiable_implies_semanticallyInferrable
    {H : GenLimit.Generic.LanguageClass α}
    (E : GenLimit.Bridge.ClassEnumeration H)
    (hIdent : ExtensionallyIdentifiable H) :
    SemanticallyInferrable E.family := by
  classical
  obtain ⟨M, hM⟩ := hIdent
  let named : SemanticIdentifier α := fun history ↦ leastName E (M history)
  refine ⟨named, ?_⟩
  intro z stream hPresentation
  have hTarget : E.family z ∈ H := E.family_mem z
  obtain ⟨L, hL, T, hT⟩ := hM (E.family z) hTarget stream hPresentation
  let j := leastName E (E.family z)
  have hj : E.family j = E.family z := leastName_spec E hTarget
  refine ⟨j, hj, T, ?_⟩
  intro t ht
  have hguess : M (GenLimit.textPrefix stream t) = E.family z := by
    exact (hT t ht).trans hL
  change leastName E (M (GenLimit.textPrefix stream t)) = j
  exact congrArg (leastName E) hguess

/-- For a chosen enumeration, the indexed and literal language-valued
identification interfaces are equivalent. -/
theorem semanticallyInferrable_iff_extensionallyIdentifiable
    {H : GenLimit.Generic.LanguageClass α}
    (E : GenLimit.Bridge.ClassEnumeration H) :
    SemanticallyInferrable E.family ↔ ExtensionallyIdentifiable H :=
  ⟨semanticallyInferrable_implies_extensionallyIdentifiable E,
    extensionallyIdentifiable_implies_semanticallyInferrable E⟩

/-- Semantic identification of an indexed family of infinite languages
implies #02-style generation in the limit for its extensional range. -/
theorem semanticallyInferrable_implies_generatableInLimit
    (C : GenLimit.Generic.LanguageFamily α)
    (hInfinite : ∀ i, (C i).Infinite)
    (hInfer : SemanticallyInferrable C) :
    GenLimit.Generic.GeneratableInLimit (Set.range C) := by
  obtain ⟨M, hM⟩ := hInfer
  exact GenLimit.Generic.stabilizingIndexIdentifier_implies_generatableInLimit
    C hInfinite M hM

/-- Angluin's finite tell-tale condition therefore implies generation for
families of infinite languages. -/
theorem conditionTwo_implies_generatableInLimit
    (C : GenLimit.Generic.LanguageFamily α)
    (hInfinite : ∀ i, (C i).Infinite)
    (hTellTales : ConditionTwo C) :
    GenLimit.Generic.GeneratableInLimit (Set.range C) :=
  semanticallyInferrable_implies_generatableInLimit C hInfinite
    (semanticallyInferrable_of_conditionTwo C hTellTales)

/-- P02 Theorem 2.3 for a nonempty countably enumerated class, in the literal
language-valued identifier interface of Definitions 2.6--2.7. -/
theorem extensionallyIdentifiable_iff_extensionalTellTaleCondition
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (E : GenLimit.Bridge.ClassEnumeration H) :
    ExtensionallyIdentifiable H ↔ ExtensionalTellTaleCondition H :=
  (semanticallyInferrable_iff_extensionallyIdentifiable E).symm.trans
    ((semanticallyInferrable_iff_conditionTwo E.family).trans
    (conditionTwo_iff_extensionalTellTaleCondition E)
    )

/-- P02 Theorem 2.3 for an arbitrary countable extensional class.  The empty
class is handled directly; a nonempty class is transported through a chosen
enumeration and Angluin's indexed characterization. -/
theorem countable_extensionallyIdentifiable_iff_extensionalTellTaleCondition
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hCountable : H.Countable) :
    ExtensionallyIdentifiable H ↔ ExtensionalTellTaleCondition H := by
  classical
  by_cases hEmpty : H = ∅
  · subst H
    simp [ExtensionallyIdentifiable, ExtensionalIdentifies,
      ExtensionalTellTaleCondition]
  · let E := GenLimit.Bridge.ClassEnumeration.ofCountable hCountable
      (Set.nonempty_iff_ne_empty.mpr hEmpty)
    exact extensionallyIdentifiable_iff_extensionalTellTaleCondition E

/-- Corrected, source-facing form of P02 Theorem 2.3.  Countability of the
hypothesis class is necessary for the printed language-valued identifier
interface; `Paper02IdentificationDiagnostics` supplies a counterexample when
it is omitted. -/
theorem theorem_2_3_countable
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hCountable : H.Countable) :
    ExtensionallyIdentifiable H ↔ ExtensionalTellTaleCondition H :=
  countable_extensionallyIdentifiable_iff_extensionalTellTaleCondition
    hCountable

/-- The tell-tale side of P02 Theorem 2.3, combined with identification-to-
generation, yields generation for an extensional UUS class. -/
theorem extensionalTellTales_imply_generatableInLimit
    {H : GenLimit.Generic.LanguageClass α}
    (E : GenLimit.Bridge.ClassEnumeration H)
    (hUUS : GenLimit.Generic.UUS H)
    (hTellTales : ExtensionalTellTaleCondition H) :
    GenLimit.Generic.GeneratableInLimit H := by
  rw [← E.range_eq]
  exact conditionTwo_implies_generatableInLimit E.family
    ((E.uus_iff).mp hUUS)
    ((conditionTwo_iff_extensionalTellTaleCondition E).mpr hTellTales)

end GenLimit.Angluin
