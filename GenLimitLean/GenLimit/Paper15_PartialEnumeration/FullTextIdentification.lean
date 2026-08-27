import GenLimit.Paper15_PartialEnumeration.FullTopology
import GenLimit.Bridges.AngluinToPaper02

/-!
# Full-text learners and the complete Theorem 4.9 bridge

This module connects Paper 15's full-enumeration topology to the shared
Angluin theorems.  Every learner consumes only a finite ordered observation
history.  The indexed interface returns a name in an explicitly supplied
family; the source-facing extensional interface returns a language directly.
Neither learner has access to the future of the text or to the target.

The source-facing set-valued formulation uses the earlier language-valued
Angluin interface.  This matters: countability is then a theorem forced by a
causal learner on nonempty languages, rather than an assumption hidden in an
enumeration bundled into the definition.  An explicitly indexed variant is
retained separately for direct reuse of the indexed characterization.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration
namespace FullTopology

/-- A causal full-text learner: its guess is a function only of the finite
ordered observation history presented to it. -/
abbrev FullTextLearner := Learner ℕ ℕ

/-- One learner identifies every member of an indexed family from every exact
positive text.  Repeated indices are allowed, and convergence is to one fixed
index whose denotation is the target language. -/
def IdentifiesIndexedClassOnFullTexts
    (C : LanguageFamily) (learner : FullTextLearner) : Prop :=
  Angluin.SemanticallyIdentifies learner C

/-- Existence of a possibly noncomputable causal learner for an indexed
family. -/
def IndexedClassIdentifiableOnFullTexts (C : LanguageFamily) : Prop :=
  ∃ learner : FullTextLearner,
    IdentifiesIndexedClassOnFullTexts C learner

/-- The point of the range class denoted by one family index. -/
def rangePoint (C : LanguageFamily) (i : ℕ) : Point (Set.range C) :=
  ⟨C i, ⟨i, rfl⟩⟩

/-- The indexed and set-valued tell-tale predicates agree on the range of an
indexed family. -/
theorem indexedTellTale_iff_rangeTellTale
    (C : LanguageFamily) (i : ℕ) (T : Finset ℕ) :
    Angluin.IsTellTale C i T ↔ IsTellTale (rangePoint C i) T := by
  constructor
  · intro hT
    refine ⟨hT.1, ?_⟩
    intro L hLrange hTL hLCi
    obtain ⟨j, rfl⟩ := hLrange
    exact Set.Subset.antisymm hLCi (hT.2 j hTL hLCi)
  · intro hT
    refine ⟨hT.1, ?_⟩
    intro j hTj hjI
    have hEq : C j = C i :=
      hT.2 (C j) ⟨j, rfl⟩ hTj hjI
    exact hEq.symm.subset

/-- Angluin's indexed Condition 2 is exactly the pointwise tell-tale
condition on the extensional range class. -/
theorem conditionTwo_iff_rangeTellTales (C : LanguageFamily) :
    Angluin.ConditionTwo C ↔
      ∀ K : Point (Set.range C), ∃ T : Finset ℕ, IsTellTale K T := by
  constructor
  · intro hCondition K
    rcases K with ⟨_, ⟨i, rfl⟩⟩
    obtain ⟨T, hT⟩ := hCondition i
    exact ⟨T, (indexedTellTale_iff_rangeTellTale C i T).mp hT⟩
  · intro hPoint i
    obtain ⟨T, hT⟩ := hPoint (rangePoint C i)
    exact ⟨T, (indexedTellTale_iff_rangeTellTale C i T).mpr hT⟩

/-- Indexed full-text identification is equivalent to `T_D` for the full
topology on the range class.  This is the complete countably indexed form of
Paper 15, Theorem 4.9. -/
theorem indexedClassIdentifiableOnFullTexts_iff_tdSpace_range
    (C : LanguageFamily) :
    IndexedClassIdentifiableOnFullTexts C ↔ TDSpace (Set.range C) := by
  rw [show IndexedClassIdentifiableOnFullTexts C =
      Angluin.SemanticallyInferrable C from rfl]
  rw [Angluin.semanticallyInferrable_iff_conditionTwo]
  exact (conditionTwo_iff_rangeTellTales C).trans
    (theorem_4_9_topological_core (Set.range C))

/-- A class together with an explicit natural-number enumeration and a
causal learner for that enumeration.  This is useful as an indexed corollary,
but is not used as the source-facing definition because it assumes
countability by construction. -/
def CountablyIndexedIdentifiableOnFullTexts (X : Set Language) : Prop :=
  ∃ C : LanguageFamily,
    Set.range C = X ∧ IndexedClassIdentifiableOnFullTexts C

/-- The explicitly indexed set-valued corollary.  Its nonempty clause is the
exact representability boundary of an enumeration `C : ℕ → Language`. -/
theorem countablyIndexedIdentifiableOnFullTexts_iff
    (X : Set Language) :
    CountablyIndexedIdentifiableOnFullTexts X ↔
      X.Nonempty ∧ X.Countable ∧ TDSpace X := by
  classical
  constructor
  · rintro ⟨C, hRange, hIdent⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨C 0, ?_⟩
      rw [← hRange]
      exact ⟨0, rfl⟩
    · rw [← hRange]
      exact Set.countable_range C
    · rw [← hRange]
      exact
        (indexedClassIdentifiableOnFullTexts_iff_tdSpace_range C).mp hIdent
  · rintro ⟨hNonempty, hCountable, hTD⟩
    letI : Countable (Point X) := hCountable.to_subtype
    letI : Nonempty (Point X) := hNonempty.to_subtype
    obtain ⟨enumerate, hEnumerate⟩ := exists_surjective_nat (Point X)
    let C : LanguageFamily := fun n => (enumerate n).1
    have hRange : Set.range C = X := by
      apply Set.Subset.antisymm
      · rintro L ⟨n, rfl⟩
        exact (enumerate n).2
      · intro L hLX
        obtain ⟨n, hn⟩ := hEnumerate ⟨L, hLX⟩
        refine ⟨n, ?_⟩
        exact congrArg Subtype.val hn
    refine ⟨C, hRange, ?_⟩
    apply
      (indexedClassIdentifiableOnFullTexts_iff_tdSpace_range C).mpr
    simpa [hRange] using hTD

/-- Source-facing full-text identification by a causal, language-valued
learner. -/
abbrev IdentifiableOnFullTexts (X : Set Language) : Prop :=
  Angluin.ExtensionallyIdentifiable X

/-- The earlier extensional Angluin tell-tale condition is exactly the
pointwise tell-tale condition of Paper 15's full-enumeration topology. -/
theorem extensionalTellTaleCondition_iff_tdSpace (X : Set Language) :
    Angluin.ExtensionalTellTaleCondition X ↔ TDSpace X := by
  rw [← theorem_4_9_topological_core X]
  constructor
  · intro h K
    obtain ⟨T, hTK, hminimal⟩ := h K.1 K.2
    exact ⟨T, hTK, fun L hLX hTL hLK =>
      Set.Subset.antisymm hLK (hminimal L hLX hTL hLK)⟩
  · intro h L hLX
    obtain ⟨T, hT⟩ := h ⟨L, hLX⟩
    exact ⟨T, hT.1, fun K hKX hTK hKL =>
      (hT.2 K hKX hTK hKL).symm.subset⟩

/-- Complete source-facing form of Paper 15, Theorem 4.9.

For the paper's standing nonempty-language class, causal full-text
identification itself forces the class to be countable.  Thus countability is
derived on the forward path and is not bundled into the definition. -/
theorem theorem_4_9_fullText
    (X : Set Language)
    (hLanguagesNonempty : ∀ L, L ∈ X → L.Nonempty) :
    IdentifiableOnFullTexts X ↔ X.Countable ∧ TDSpace X := by
  constructor
  · intro hIdent
    have hCountable :=
      Angluin.extensionallyIdentifiable_implies_countable
        hLanguagesNonempty hIdent
    refine ⟨hCountable, ?_⟩
    apply (extensionalTellTaleCondition_iff_tdSpace X).mp
    exact
      (Angluin.countable_extensionallyIdentifiable_iff_extensionalTellTaleCondition
        hCountable).mp hIdent
  · rintro ⟨hCountable, hTD⟩
    apply
      (Angluin.countable_extensionallyIdentifiable_iff_extensionalTellTaleCondition
        hCountable).mpr
    exact (extensionalTellTaleCondition_iff_tdSpace X).mpr hTD

end FullTopology
end PartialEnumeration
end KleinbergWei
end GenLimit
