import GenLimit.Gold.Text.Consistency
import Mathlib.Data.Set.Finite.Basic

/-!
# Identification of finite languages from arbitrary positive text

The learner conjectures exactly the finite set of values observed so far.
When the target language is finite, every target value has appeared by one
finite time, so this conjecture stabilizes to the target.

## Correspondence with Gold's paper

This file formalizes the semantic mathematical content of Gold's Theorem I.6
(Appendix I, printed p. 469; PDF p. 23).  That theorem states that, under
information presentation by arbitrary text and the tester-naming relation,
the class of finite-cardinality languages is identifiable in the limit.
Gold also summarizes the same learner in Section 7 (printed p. 459): at each
time, conjecture exactly the elements that have appeared in the text so far.

The two class-level declarations corresponding to Theorem I.6 are
`finiteLearner_identifiesFiniteLanguages`, which verifies Gold's explicit
learner, and `finiteLanguages_identifiableWith`, which states the resulting
existential identifiability claim.

Gold uses indices of effective testers as names.  Here `finiteNaming` uses
finite sets themselves as names, so the file formalizes the convergence
claim but not compilation of a finite set into a tester program.

There is no exact presentation `ℕ → ℕ` of the empty language.  Consequently,
the identification theorem for the empty target is (faithfully) vacuous in
the present stream model; no pause symbol is added.
-/

namespace GenLimit
namespace Gold
namespace Text

/-- The class of all finite languages. -/
def finiteLanguages : Set Language :=
  {L | L.Finite}

@[simp] theorem mem_finiteLanguages {L : Language} :
    L ∈ finiteLanguages ↔ L.Finite := by
  rfl

/-- Every finite subset of a presented language is eventually contained in
the observed sample. -/
theorem finite_subset_eventually_subset_sample
    {stream : ℕ → ℕ} {L : Language} (hP : Presents stream L)
    (F : Finset ℕ) (hF : (↑F : Set ℕ) ⊆ L) :
    ∃ T, ∀ t, T ≤ t → F ⊆ sample stream t := by
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert u F hu ih =>
      have huL : u ∈ L := hF (Finset.mem_insert_self u F)
      have hFL : (↑F : Set ℕ) ⊆ L := by
        intro x hx
        exact hF (Finset.mem_insert_of_mem hx)
      obtain ⟨Tu, hTu⟩ := eventually_mem_sample_of_presents hP huL
      obtain ⟨TF, hTF⟩ := ih hFL
      refine ⟨max Tu TF, ?_⟩
      intro t ht
      have hTu_t : Tu ≤ t := le_trans (Nat.le_max_left Tu TF) ht
      have hTF_t : TF ≤ t := le_trans (Nat.le_max_right Tu TF) ht
      rw [Finset.insert_subset_iff]
      exact ⟨hTu t hTu_t, hTF t hTF_t⟩

/-- Under an exact presentation of a finite target, the accumulated sample is
eventually exactly the target language. -/
theorem eventually_sample_eq_of_finite
    {stream : ℕ → ℕ} {L : Language}
    (hP : Presents stream L) (hfin : L.Finite) :
    ∃ T, ∀ t, T ≤ t → (↑(sample stream t) : Set ℕ) = L := by
  obtain ⟨T, hT⟩ :=
    finite_subset_eventually_subset_sample hP hfin.toFinset (by simp)
  refine ⟨T, ?_⟩
  intro t ht
  apply Set.Subset.antisymm
  · intro u hu
    exact mem_language_of_mem_sample_of_presents hP hu
  · intro u hu
    have huF : u ∈ hfin.toFinset := by simpa
    exact hT t ht huF

/-- Finite sets serve as names for their underlying languages. -/
def finiteNaming : Naming (Finset ℕ) where
  language F := (↑F : Language)

/-- Conjecture exactly the set of positive examples observed so far. -/
def finiteLearner : TextLearner (Finset ℕ) :=
  List.toFinset

/-- The finite-set learner identifies a finite target on every exact text for
that target. -/
theorem finiteLearner_identifiesOnText
    {stream : ℕ → ℕ} {L : Language}
    (hP : Presents stream L) (hfin : L.Finite) :
    IdentifiesOnText finiteNaming finiteLearner stream L := by
  refine ⟨hfin.toFinset, by simp [finiteNaming], ?_⟩
  obtain ⟨T, hT⟩ := eventually_sample_eq_of_finite hP hfin
  refine ⟨T, ?_⟩
  intro t ht
  change (textPrefix stream t).toFinset = hfin.toFinset
  rw [textPrefix_toFinset]
  apply Finset.coe_injective
  simpa using hT t ht

/-- The finite-set learner identifies every finite language from arbitrary
positive text.  This is Gold's Theorem I.6 under `finiteNaming`,
where finite sets serve as names for their underlying languages.
Gold's original theorem uses the tester-naming relation and
also requires an effective compilation from each observed finite set to a
tester program; that compilation is not formalized here.
For the empty language, although
`finiteLanguages` includes the empty language, every total positive text
`stream : ℕ → ℕ` has a nonempty range.  Hence no stream satisfies
`Presents stream ∅`, and the universally quantified identification statement
for `∅` holds vacuously. -/
theorem finiteLearner_identifiesFiniteLanguages :
    IdentifiesClass finiteNaming finiteLearner finiteLanguages := by
  intro L hfin stream hP
  exact finiteLearner_identifiesOnText hP hfin

/-- The class of finite languages is identifiable relative to finite-set
names. -/
theorem finiteLanguages_identifiableWith :
    IdentifiableWith finiteNaming finiteLanguages :=
  ⟨finiteLearner, finiteLearner_identifiesFiniteLanguages⟩

/-- The finite-language class is identifiable in the representation-
independent semantic specialization. -/
theorem finiteLanguages_semanticallyIdentifiable :
    SemanticallyIdentifiable finiteLanguages :=
  identifiableWith_implies_semanticallyIdentifiable
    finiteLanguages_identifiableWith

end Text
end Gold
end GenLimit
