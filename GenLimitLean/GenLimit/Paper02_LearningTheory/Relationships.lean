import GenLimit.Paper02_LearningTheory.GenerationInLimitCharacterization
import GenLimit.Paper02_LearningTheory.FiniteEUCUnion

/-!
# Relationships among the #02 sufficient conditions

The main text and Appendix C use the same finite-candidate race with different
ways of obtaining stable infinite cores.  These short corollaries record the
logical relationship without replacing either source-facing proof.
-/

namespace GenLimit.LiRamanTewari

/-- A finite cover by finite-closure-dimension classes is, under UUS, a
finite cover by Eventually Unbounded Closure classes. -/
theorem finite_closure_cover_implies_finite_euc_cover
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {n : ℕ} {classes : Fin n → GenLimit.Generic.LanguageClass α}
    (hcover : IsFiniteCover H classes)
    (hfinite : ∀ i, HasFiniteClosureDimension (classes i)) :
    ∀ i, EventuallyUnboundedClosure (classes i) := by
  intro i
  apply finite_closure_dimension_implies_eventuallyUnboundedClosure
  · intro L hLi
    apply hUUS L
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨i, hLi⟩
  · exact hfinite i

/-- Alternative factorization of Theorem 3.10 through Appendix Theorem C.2.
The direct source-order proof remains the public theorem in
`GenerationInLimitCharacterization`. -/
theorem finite_closure_dimension_cover_implies_generatable_via_euc
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hcover : ∃ n : ℕ,
      ∃ classes : Fin n → GenLimit.Generic.LanguageClass α,
        IsFiniteCover H classes ∧
          ∀ i, HasFiniteClosureDimension (classes i)) :
    GeneratableInLimit H := by
  obtain ⟨n, classes, hclasses, hfinite⟩ := hcover
  exact finite_euc_cover_implies_generatable_in_limit classes hclasses
    (finite_closure_cover_implies_finite_euc_cover
      hUUS hclasses hfinite)

end GenLimit.LiRamanTewari
