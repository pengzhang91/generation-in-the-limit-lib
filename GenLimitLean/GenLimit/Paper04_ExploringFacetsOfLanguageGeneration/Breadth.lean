import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Exhaustive
import GenLimit.Dependency_Angluin1980.LockingExistence

/-!
# Charikar--Pabbaraju: exact breadth forces Angluin tell-tales

This file formalizes the proposition in Section 6.3 of
Charikar--Pabbaraju, *Exploring Facets of Language Generation in the Limit*,
arXiv:2411.15364v2: if an indexed collection can be generated with exact
breadth, then it satisfies Angluin's Condition with Existence.

The paper proves the result by a direct locking diagonal.  We preserve that
structure through the library's Angluin locking lemmas.  An exact-breadth
algorithm gives a semantic positive-data identifier: at each stage, conjecture
the least family index whose language is the range of the current generator.
Breadth makes this identifier converge, and the locking diagonal then extracts
a finite tell-tale.  No effective claim is made here; this proposition is
about Condition with Existence, exactly as in the source.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## Exact generation with breadth -/

/-- Exact breadth at one time: the generate-only range is the target
language. -/
def BreadthCorrectAt
    (A : ExhaustiveAlgorithm α) (K : Generic.Language α)
    (stream : Generic.Stream α) (t : ℕ) : Prop :=
  generateOnly A stream t = K

/-- The paper's definition of generation with (exact) breadth, for an indexed
collection. -/
def IsBreadthGenerator
    (A : ExhaustiveAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Generic.Stream α, Generic.Presents stream (F z) →
    ∃ T : ℕ, ∀ t, T ≤ t → BreadthCorrectAt A (F z) stream t

def BreadthGeneratable (F : Generic.LanguageFamily α) : Prop :=
  ∃ A : ExhaustiveAlgorithm α, IsBreadthGenerator A F

/-! ## A breadth generator induces a positive-data identifier -/

/-- On a finite history, conjecture the least family index whose language is
exactly the range of the generator returned by `A`; use index zero if there
is no such index. -/
noncomputable def breadthIdentifier
    (A : ExhaustiveAlgorithm ℕ) (F : Generic.LanguageFamily ℕ) :
    List ℕ → ℕ := by
  classical
  exact fun xs =>
    if h : ∃ i, Set.range (A xs.length xs.get) = F i
    then Nat.find h
    else 0

/- The canonical least index denoting the target. -/
noncomputable def leastTargetIndex
    (F : Generic.LanguageFamily ℕ) (z : ℕ) : ℕ := by
  classical
  exact Nat.find (⟨z, rfl⟩ : ∃ i, F i = F z)

theorem leastTargetIndex_spec
    (F : Generic.LanguageFamily ℕ) (z : ℕ) :
    F (leastTargetIndex F z) = F z := by
  classical
  exact Nat.find_spec (⟨z, rfl⟩ : ∃ i, F i = F z)

theorem leastTargetIndex_le_of_eq
    (F : Generic.LanguageFamily ℕ) (z i : ℕ) (hi : F i = F z) :
    leastTargetIndex F z ≤ i := by
  classical
  exact Nat.find_min' (⟨z, rfl⟩ : ∃ j, F j = F z) hi

theorem breadthIdentifier_eq_least_target
    (A : ExhaustiveAlgorithm ℕ) (F : Generic.LanguageFamily ℕ)
    (stream : Generic.Stream ℕ) (z t : ℕ)
    (hbreadth : BreadthCorrectAt A (F z) stream t) :
    breadthIdentifier A F (GenLimit.Angluin.streamPrefix stream t) =
      leastTargetIndex F z := by
  classical
  let xs := GenLimit.Angluin.streamPrefix stream t
  have hinput : A xs.length xs.get =
      A t (fun i : Fin t => stream i) := by
    let f : Fin t → ℕ := fun i => stream i
    have hp :
        (⟨(List.ofFn f).length, (List.ofFn f).get⟩ :
          Σ n, Fin n → ℕ) = ⟨t, f⟩ := by
      exact List.equivSigmaTuple.apply_symm_apply ⟨t, f⟩
    have hA := congrArg (fun p : Σ n, Fin n → ℕ => A p.1 p.2) hp
    simpa [xs, GenLimit.Angluin.streamPrefix, f] using hA
  have hrange : Set.range (A xs.length xs.get) = F z := by
    rw [hinput]
    simpa [BreadthCorrectAt, generateOnly, generatorAt] using hbreadth
  let hcandidates : ∃ i, Set.range (A xs.length xs.get) = F i :=
    ⟨z, hrange⟩
  have hcandSpec : Set.range (A xs.length xs.get) =
      F (Nat.find hcandidates) := Nat.find_spec hcandidates
  have hcandTarget : F (Nat.find hcandidates) = F z :=
    hcandSpec.symm.trans hrange
  have htargetCandidate : Set.range (A xs.length xs.get) =
      F (leastTargetIndex F z) :=
    hrange.trans (leastTargetIndex_spec F z).symm
  have hle₁ : Nat.find hcandidates ≤ leastTargetIndex F z :=
    Nat.find_min' hcandidates htargetCandidate
  have hle₂ : leastTargetIndex F z ≤ Nat.find hcandidates :=
    leastTargetIndex_le_of_eq F z _ hcandTarget
  have heq : Nat.find hcandidates = leastTargetIndex F z :=
    Nat.le_antisymm hle₁ hle₂
  rw [breadthIdentifier, dif_pos hcandidates]
  exact heq

/-- Exact breadth gives semantic positive-data identification, with syntactic
convergence to the least index denoting the target language. -/
theorem breadthGenerator_semanticallyIdentifies
    {A : ExhaustiveAlgorithm ℕ} {F : Generic.LanguageFamily ℕ}
    (hA : IsBreadthGenerator A F) :
    ∀ z, ∀ stream : Generic.Stream ℕ, Generic.Presents stream (F z) →
      ∃ j, F j = F z ∧
        GenLimit.Angluin.EffectiveConvergesTo
          (breadthIdentifier A F) stream j := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hA z stream hP
  refine ⟨leastTargetIndex F z, leastTargetIndex_spec F z, T, ?_⟩
  intro t ht
  exact breadthIdentifier_eq_least_target A F stream z t (hT t ht)

/-! ## Locking yields Condition with Existence -/

/-- Semantic identification is enough for Angluin's non-effective Condition
2.  This packages the locking-sequence existence and tell-tale lemmas without
adding the effective hypotheses of Angluin's full Theorem 1. -/
theorem semanticIdentification_conditionTwo
    {F : Generic.LanguageFamily ℕ} (hNonempty : ∀ i, (F i).Nonempty)
    {M : List ℕ → ℕ}
    (hIdentifies : ∀ z, ∀ stream : Generic.Stream ℕ,
      Generic.Presents stream (F z) →
        ∃ j, F j = F z ∧
          GenLimit.Angluin.EffectiveConvergesTo M stream j) :
    GenLimit.Angluin.ConditionTwo F := by
  intro z
  have hTarget : ∀ stream : Generic.Stream ℕ,
      Generic.Presents stream (F z) →
        ∃ j, GenLimit.Angluin.EffectiveConvergesTo M stream j := by
    intro stream hP
    obtain ⟨j, -, hj⟩ := hIdentifies z stream hP
    exact ⟨j, hj⟩
  obtain ⟨xs, j, hlock⟩ :=
    GenLimit.Angluin.exists_lockingSequence_of_identifies
      (hNonempty z) hTarget
  have hcorrect : F j = F z :=
    GenLimit.Angluin.lockingSequence_correct_of_identifies
      (hNonempty z) (hIdentifies z) hlock
  have hPresentable : ∀ i, ∃ stream : Generic.Stream ℕ,
      Generic.Presents stream (F i) := by
    intro i
    exact ⟨GenLimit.Angluin.presentationOfNonempty (F i) (hNonempty i),
      GenLimit.Angluin.presentationOfNonempty_presents (F i) (hNonempty i)⟩
  exact ⟨xs.toFinset,
    GenLimit.Angluin.lockingSequence_isTellTale
      hIdentifies hPresentable hlock hcorrect⟩

/-- Proposition `prop:generation-with-breadth-necessary-condition`: exact
breadth implies Angluin's Condition with Existence for an indexed collection
of nonempty languages. -/
theorem generation_with_breadth_implies_conditionTwo
    {F : Generic.LanguageFamily ℕ} (hNonempty : ∀ i, (F i).Nonempty)
    (hBreadth : BreadthGeneratable F) :
    GenLimit.Angluin.ConditionTwo F := by
  obtain ⟨A, hA⟩ := hBreadth
  exact semanticIdentification_conditionTwo hNonempty
    (breadthGenerator_semanticallyIdentifies hA)

/-- Indexed Condition 2 is the collection-valued Angluin Condition with
Existence used in the Charikar--Pabbaraju proposition. -/
theorem conditionTwo_implies_angluinExistence_range
    {F : Generic.LanguageFamily ℕ}
    (hCondition : GenLimit.Angluin.ConditionTwo F) :
    ∀ L, L ∈ Set.range F → ∃ T : Finset ℕ,
      IsAngluinTellTale (Set.range F) L T := by
  intro L hL
  obtain ⟨i, rfl⟩ := hL
  obtain ⟨T, hT⟩ := hCondition i
  refine ⟨T, hT.1, ?_⟩
  intro L' hL' hTL' hproper
  obtain ⟨j, rfl⟩ := hL'
  have hback : F i ⊆ F j := hT.2 j hTL' hproper.subset
  exact hproper.not_subset hback

/-- The exact collection-valued conclusion printed in the paper. -/
theorem generation_with_breadth_implies_angluinExistence
    {F : Generic.LanguageFamily ℕ} (hNonempty : ∀ i, (F i).Nonempty)
    (hBreadth : BreadthGeneratable F) :
    ∀ L, L ∈ Set.range F → ∃ T : Finset ℕ,
      IsAngluinTellTale (Set.range F) L T :=
  conditionTwo_implies_angluinExistence_range
    (generation_with_breadth_implies_conditionTwo hNonempty hBreadth)

end GenLimit.CharikarPabbaraju
