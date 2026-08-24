import GenLimit.Paper05_HallucinationsBreadthAndStability.ExactBreadth

/-!
# A coherent sample-allowing repair of the stable statements

The pinned source's literal definitions require exact support
`K \ sample(stream,t)` while simultaneously requiring the raw support to
become constant. `StabilityGap.lean` proves that conjunction impossible for an
infinite target.

The source's footnotes also discuss the standard sample-allowing convention.
Here it is made precise in two equivalent ways:

* require whole-target support `K`, whose raw support can stabilize; or
* restore the observed sample before comparing supports across time.

Under either repair, the intended Angluin characterization is valid.  These
theorems are deliberately named as corrected statements and are not labels
for the inconsistent literal theorem.
-/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Generic

/-- Stability after adding back the observations seen so far. -/
def IsStableAfterRestoringObserved
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  IsStableGenerator (restoreObserved G) F

/-- Eventual whole-target support is automatically raw-support stable. -/
theorem wholeTargetGenerator_isStable
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hWhole : IsWholeTargetGenerator G F) :
    IsStableGenerator G F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hWhole z stream hP
  refine ⟨T, ?_⟩
  intro n n' hn hn'
  rw [show supportAt G stream n = F z by
      simpa [WholeTargetCorrectAt] using hT n hn,
    show supportAt G stream n' = F z by
      simpa [WholeTargetCorrectAt] using hT n' hn']

/-- A literal exact-breadth generator is stable once its observed sample is
restored. -/
theorem exactBreadthGenerator_stableAfterRestoringObserved
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hExact : IsExactBreadthGenerator G F) :
    IsStableAfterRestoringObserved G F := by
  exact wholeTargetGenerator_isStable
    (literalExact_implies_wholeTarget hExact)

/-- Corrected stable-exact sufficiency under the whole-target convention. -/
theorem conditionTwo_implies_stableWholeTarget
    {F : Generic.LanguageFamily α}
    (h : GenLimit.Angluin.ConditionTwo F) :
    ∃ G : SupportAlgorithm α,
      IsWholeTargetGenerator G F ∧ IsStableGenerator G F := by
  let G := restoreObserved (exactBreadthFromConditionTwo h)
  have hWhole : IsWholeTargetGenerator G F :=
    literalExact_implies_wholeTarget
      (conditionTwo_implies_literalExact h)
  exact ⟨G, hWhole, wholeTargetGenerator_isStable hWhole⟩

/-- The intended Theorem 3.15 after replacing literal shrinking support by
the coherent whole-target/sample-allowing convention. -/
theorem stableWholeTargetGeneratable_iff_conditionTwo
    [Nonempty α] [Countable α]
    (F : Generic.LanguageFamily α) :
    (∃ G : SupportAlgorithm α,
        IsWholeTargetGenerator G F ∧ IsStableGenerator G F) ↔
      GenLimit.Angluin.ConditionTwo F := by
  constructor
  · rintro ⟨G, hWhole, -⟩
    exact GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable F
      ⟨wholeTargetIdentifier G F,
        wholeTargetGenerator_semanticallyIdentifies hWhole⟩
  · exact conditionTwo_implies_stableWholeTarget

end GenLimit.BreadthCharacterizations
