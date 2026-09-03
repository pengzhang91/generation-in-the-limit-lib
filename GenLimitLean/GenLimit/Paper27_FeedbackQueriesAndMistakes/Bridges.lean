import GenLimit.Paper27_FeedbackQueriesAndMistakes.QuerySeparation

/-!
# Feedback-query bridge consequences

These consequences compare two auxiliary whole-set feedback semantics in this
directory.  They are useful for the paper-relationship graph but are not
numbered-source wrappers.  The paper's exact first-element mistake
model and source-timed one-query model are formalized separately in
`SourceSetMistake.lean` and `SourceQuery.lean`.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-- In the checked sample-free set-output semantics, mistake feedback and
finite membership-query feedback have exactly the same power.  Both are
characterized by a countable inner cover. -/
theorem setMistake_iff_setQuery
    [Countable α] [Infinite α]
    (targets : LanguageClass α) :
    SetMistakeGeneratable targets ↔
      SetQueryGeneratable targets := by
  rw [setMistake_core_characterization,
    setQuery_squareCore_characterization]

theorem setMistake_to_setQuery
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (h : SetMistakeGeneratable targets) :
    SetQueryGeneratable targets :=
  (setMistake_iff_setQuery targets).mp h

theorem setQuery_to_setMistake
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (h : SetQueryGeneratable targets) :
    SetMistakeGeneratable targets :=
  (setMistake_iff_setQuery targets).mpr h

/-- The diagonal class also separates element-query generation from the
checked set-valued mistake-feedback core. -/
theorem allInfiniteNatLanguages_not_setMistakeGeneratable :
    ¬ SetMistakeGeneratable allInfiniteNatLanguages := by
  intro hmistake
  exact no_countableInnerCover_allInfiniteNatLanguages
    (setMistake_implies_countableInnerCover hmistake)

/-- Combined hierarchy statement for the explicit diagonal witness. -/
theorem queryAndMistake_feedbackHierarchy_core :
    ElementQueryGeneratable allInfiniteNatLanguages ∧
      ¬ SetQueryGeneratable allInfiniteNatLanguages ∧
      ¬ SetMistakeGeneratable allInfiniteNatLanguages :=
  ⟨allInfiniteNatLanguages_elementQueryGeneratable,
    allInfiniteNatLanguages_not_setQueryGeneratable,
    allInfiniteNatLanguages_not_setMistakeGeneratable⟩

end GenLimit.FeedbackQueries
