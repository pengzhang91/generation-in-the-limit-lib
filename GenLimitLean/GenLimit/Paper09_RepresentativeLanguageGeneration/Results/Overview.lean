import GenLimit.Paper09_RepresentativeLanguageGeneration.Relationships
import GenLimit.Paper09_RepresentativeLanguageGeneration.GroupClosure
import GenLimit.Paper09_RepresentativeLanguageGeneration.NonuniformCharacterization
import GenLimit.Paper09_RepresentativeLanguageGeneration.FinitePartitionCorollaries
import GenLimit.Paper09_RepresentativeLanguageGeneration.UniformSeparation
import GenLimit.Paper09_RepresentativeLanguageGeneration.FiniteSupport
import GenLimit.Paper09_RepresentativeLanguageGeneration.TailCounterexample
import GenLimit.Paper09_RepresentativeLanguageGeneration.LimitFoundations
import GenLimit.Paper09_RepresentativeLanguageGeneration.ExactProfileSupport
import GenLimit.Paper09_RepresentativeLanguageGeneration.QueryImpossibility

/-!
# Published results of Representative Language Generation

This is the compact audit surface for Peale--Raman--Reingold,
*Representative Language Generation* (ICML 2025 / PMLR 267).  The wrappers
below use the numbering and statements of the published PMLR version.

Theorem 4.4 is false as printed: `printed_theorem_4_4_counterexample` verifies all of
its stated premises and refutes its conclusion.  Consequently there is no
misleading wrapper named `theorem_4_4`.  The repaired result is exposed as
`corrected_theorem_4_4`, using exact group profiles in place of the printed
positive-membership intersections.  The same distinction applies to
published Lemma 4.8.
-/

namespace GenLimit.RepresentativeGeneration.Published

/-- Published Theorem 3.3 (group-closure characterization). -/
theorem theorem_3_3
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (_hUUS : GenLimit.Generic.UUS H)
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha) :
    AlphaRepresentativeUniformlyGeneratable H groups alpha ↔
      HasFiniteGroupClosureDimension H groups alpha :=
  alphaRepresentativeUniformlyGeneratable_iff_finite_groupClosureDimension
    hpartition halpha

/-- Published Corollary 3.4. -/
theorem corollary_3_4
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α)
    (_hUUS : GenLimit.Generic.UUS H)
    (hpartition : IsCountablePartition groups) :
    RepresentativelyUniformlyGeneratable H groups ↔
      ∀ alpha : ℝ, 0 < alpha →
        HasFiniteGroupClosureDimension H groups alpha :=
  representativelyUniformlyGeneratable_iff_all_finite_groupClosureDimension
    hpartition

/-- Published Corollary 3.5. -/
theorem corollary_3_5
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α) (hH : H.Finite)
    (_hUUS : GenLimit.Generic.UUS H)
    {k : ℕ} (groups : Fin k → Set α)
    (hpartition : IsFinitePartition groups) :
    RepresentativelyUniformlyGeneratable H
      (extendFinitePartition groups) :=
  finiteClass_finitePartition_representativelyUniformlyGeneratable
    hH groups hpartition

/-- Published Corollary 3.6, with its infinite-universe witness made
explicit. -/
theorem corollary_3_6 :
    ∃ H : GenLimit.Generic.LanguageClass UniformSeparationUniverse,
      ∃ groups : Fin 2 → Set UniformSeparationUniverse,
        H.Countable ∧
        GenLimit.Generic.UUS H ∧
        IsFinitePartition groups ∧
        GenLimit.Generic.UniformlyGeneratable H ∧
        ¬ RepresentativelyUniformlyGeneratable H
            (extendFinitePartition groups) :=
  uniformGeneration_not_representativeUniformGeneration

/-- Published Theorem 3.7 (non-uniform characterization). -/
theorem theorem_3_7
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} :
    RepresentativelyNonuniformlyGeneratable H groups ↔
      ∀ alpha : ℝ, 0 < alpha →
        ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
          GenLimit.Generic.IsNondecreasingCover H classes ∧
          ∀ n, AlphaRepresentativeUniformlyGeneratable
            (classes n) groups alpha :=
  representative_nonuniform_iff_uniform_nondecreasing_cover

/-- Published Corollary 3.8. -/
theorem corollary_3_8
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α)
    (hCountable : H.Countable) (hInfinite : H.Infinite)
    (hUUS : GenLimit.Generic.UUS H)
    {k : ℕ} (groups : Fin k → Set α)
    (hpartition : IsFinitePartition groups) :
    RepresentativelyNonuniformlyGeneratable H
        (extendFinitePartition groups) ∧
      RepresentativelyGeneratableInLimit H
        (extendFinitePartition groups) :=
  countableClass_finitePartition_nonuniform_and_limit
    H hCountable hInfinite hUUS groups hpartition

/-- Published Lemma 4.3, with the statement/proof quantifier mismatch
repaired by one alpha-independent partition. -/
theorem lemma_4_3 :
    ∃ groups : ℕ → Set ℕ,
      ∃ H : GenLimit.Generic.LanguageClass ℕ,
        IsCountablePartition groups ∧
        Function.Injective groups ∧
        (∀ n, (groups n).Nonempty) ∧
        H.Finite ∧
        H.ncard = 1 ∧
        GenLimit.Generic.UUS H ∧
        ¬ HasFiniteSupport H groups ∧
        ¬ RepresentativelyGeneratableInLimit H groups ∧
        ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
          ¬ AlphaRepresentativelyGeneratableInLimit H groups alpha :=
  finiteSupport_necessity

/-- Published Lemma 4.6 (eventual criticality of the target). -/
theorem lemma_4_6
    {family : GenLimit.Generic.LanguageFamily α}
    {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (family z)) :
    ∃ T, ∀ t, T ≤ t → IsCriticalAt family stream t z :=
  target_eventually_critical hP

/-- Counterexample to published Lemma 4.8 and Theorem 4.4. -/
theorem printed_theorem_4_4_counterexample :
    tailClass.Countable ∧
    GenLimit.Generic.UUS tailClass ∧
    GroupsCover tailGroups ∧
    HasFiniteSupport tailClass tailGroups ∧
    ¬ RepresentativelyGeneratableInLimit tailClass tailGroups :=
  GenLimit.RepresentativeGeneration.printed_theorem_4_4_counterexample

/-- Corrected published Lemma 4.8, using finite exact-profile support. -/
theorem corrected_lemma_4_8
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (hUUS : GenLimit.Generic.UUS H)
    (hsupport : HasFiniteExactProfileSupport H groups)
    {L : GenLimit.Generic.Language α} (hLH : L ∈ H)
    {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream L)
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ T, ∀ t, T ≤ t →
      IsAlphaFeasibleAt L groups alpha stream t :=
  GenLimit.RepresentativeGeneration.corrected_lemma_4_8
    hUUS hsupport hLH hP halpha

/-- Corrected published Theorem 4.4, using finite exact-profile support. -/
theorem corrected_theorem_4_4
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α)
    (hHcountable : H.Countable)
    (hUUS : GenLimit.Generic.UUS H)
    (hcover : GroupsCover groups)
    (hsupport : HasFiniteExactProfileSupport H groups) :
    RepresentativelyGeneratableInLimit H groups :=
  GenLimit.RepresentativeGeneration.corrected_theorem_4_4
    H groups hHcountable hUUS hcover hsupport

/-- Published Lemma 4.9, proved in the stronger semantic finite-dialogue
model documented by `QueryImpossibility`. -/
theorem lemma_4_9 :
    MembershipQuery.finiteQuery_impossibility_statement :=
  MembershipQuery.finiteQuery_impossibility

end GenLimit.RepresentativeGeneration.Published
