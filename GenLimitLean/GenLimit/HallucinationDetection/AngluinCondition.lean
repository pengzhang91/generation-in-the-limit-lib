import GenLimit.HallucinationDetection.Reductions
import GenLimit.Angluin.SemanticNecessity

/-!
# Angluin's condition and hallucination detection

This module proves Corollary 2.2 of Karbasi--Montasser--Sous--Velegkas at
the paper's semantic oracle level. Its Angluin condition is exactly finite
tell-tale existence (`ConditionTwo` in the shared Angluin development).

The source describes an enumeration as an infinite sequence all of whose
entries lie in the language. Consequently an empty language has no legal
enumeration. The public equivalence below handles that edge case exactly:
identification is vacuous there, and the empty set is a tell-tale. Nonempty
targets use the generic locking-sequence argument in
`GenLimit.Angluin.SemanticNecessity`.
-/

namespace GenLimit.HallucinationDetection

open GenLimit.Generic

noncomputable local instance angluinConditionPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## Tell-tales suffice semantically -/

/-- Choose one finite tell-tale for each indexed language. -/
noncomputable def chosenTellTale
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) (i : ℕ) : Finset α :=
  Classical.choose (h i)

theorem chosenTellTale_spec
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) (i : ℕ) :
    GenLimit.Angluin.IsTellTale C i (chosenTellTale C h i) :=
  Classical.choose_spec (h i)

/-- A fixed tell-tale is a constant finite-stage approximation. -/
noncomputable def constantTellTaleApproximation
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    ℕ → ℕ → Finset α :=
  fun i _stage => chosenTellTale C h i

theorem constantTellTaleApproximation_spec
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    GenLimit.Angluin.IsTellTaleApproximation C
      (constantTellTaleApproximation C h) := by
  constructor
  · intro i n m _hnm
    exact Finset.Subset.refl _
  · intro i
    refine ⟨chosenTellTale C h i, chosenTellTale_spec C h i, 0, ?_⟩
    intro n _hn
    rfl

theorem identifiable_of_conditionTwo
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    IdentifiableInLimit C := by
  let A := constantTellTaleApproximation C h
  exact ⟨GenLimit.Angluin.semanticLearner C A,
    GenLimit.Angluin.semanticLearner_semanticallyIdentifies
      (constantTellTaleApproximation_spec C h)⟩

/-! ## Source-facing wrappers for semantic necessity

The generic implementations live in `GenLimit.Angluin.SemanticNecessity` so
later papers can reuse them without importing hallucination detection. These
declarations preserve the original paper-facing names and signatures.
-/

/-- Turn the shared finite-function identifier interface into the list
interface used by the locking-sequence development. -/
def listIdentifierOf
    (M : GenLimit.Angluin.SemanticIdentifier α) : List α → ℕ :=
  GenLimit.Angluin.listIdentifierOf M

theorem listIdentifierOf_streamPrefix
    (M : GenLimit.Angluin.SemanticIdentifier α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    listIdentifierOf M (GenLimit.Angluin.streamPrefix stream t) =
      GenLimit.Angluin.identifierOutput M stream t := by
  simpa [listIdentifierOf] using
    GenLimit.Angluin.listIdentifierOf_streamPrefix M stream t

/-- Syntactic convergence for a list identifier over an arbitrary domain. -/
def ListConvergesTo
    (M : List α → ℕ) (stream : GenLimit.Generic.Stream α) (j : ℕ) : Prop :=
  GenLimit.Angluin.ListConvergesTo M stream j

/-- A fixed surjective domain enumeration yields an exact presentation of
every nonempty language, using one target point as padding. -/
noncomputable def presentationFromDomainEnumeration
    (enumerate : ℕ → α) (L : Set α) (hL : L.Nonempty) :
    GenLimit.Generic.Stream α :=
  GenLimit.Angluin.presentationFromDomainEnumeration enumerate L hL

theorem presentationFromDomainEnumeration_presents
    (enumerate : ℕ → α) (henumerate : Function.Surjective enumerate)
    (L : Set α) (hL : L.Nonempty) :
    GenLimit.Generic.Presents
      (presentationFromDomainEnumeration enumerate L hL) L := by
  simpa [presentationFromDomainEnumeration] using
    GenLimit.Angluin.presentationFromDomainEnumeration_presents
      enumerate henumerate L hL

/-- Generic form of the locking-existence diagonal. -/
theorem exists_lockingSequence_of_identifies_with_presentation
    {M : List α → ℕ} {L : Set α}
    {base : GenLimit.Generic.Stream α}
    (hbaseP : GenLimit.Generic.Presents base L)
    (hIdentifies : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream L →
        ∃ j, ListConvergesTo M stream j) :
    ∃ xs : List α, ∃ j, GenLimit.Angluin.IsLockingSequence M L xs j := by
  apply GenLimit.Angluin.exists_lockingSequence_of_identifies_with_presentation
    hbaseP
  simpa [ListConvergesTo] using hIdentifies

/-- A locking sequence obtained for a correctly identified target names that
target. -/
theorem lockingSequence_correct_with_presentation
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    {z j : ℕ} {xs : List α}
    {base : GenLimit.Generic.Stream α}
    (hbaseP : GenLimit.Generic.Presents base (C z))
    (hIdentifies : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ ell, C ell = C z ∧
          ListConvergesTo M stream ell)
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j) :
    C j = C z := by
  apply GenLimit.Angluin.lockingSequence_correct_with_presentation
    hbaseP _ hlock
  simpa [ListConvergesTo] using hIdentifies

/-- Generic form of the locking-sequence-to-tell-tale lemma. -/
theorem lockingSequence_isTellTale_with_presentations
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    (hIdentifies : ∀ z, ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ j, C j = C z ∧ ListConvergesTo M stream j)
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C i))
    {z j : ℕ} {xs : List α}
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j)
    (hcorrect : C j = C z) :
    GenLimit.Angluin.IsTellTale C z xs.toFinset := by
  apply GenLimit.Angluin.lockingSequence_isTellTale_with_presentations
    _ hPresentable hlock hcorrect
  simpa [ListConvergesTo] using hIdentifies

/-- Variant for indexed collections that may contain empty languages. -/
theorem lockingSequence_isTellTale_with_nonempty_presentations
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    (hIdentifies : ∀ z, ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ j, C j = C z ∧ ListConvergesTo M stream j)
    (hPresentable : ∀ i, (C i).Nonempty →
      ∃ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream (C i))
    {z j : ℕ} {xs : List α}
    (hxs : xs ≠ [])
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j)
    (hcorrect : C j = C z) :
    GenLimit.Angluin.IsTellTale C z xs.toFinset := by
  apply GenLimit.Angluin.lockingSequence_isTellTale_with_nonempty_presentations
    _ hPresentable hxs hlock hcorrect
  simpa [ListConvergesTo] using hIdentifies

/-- Extending a locking sequence by one target point preserves locking and
makes its content nonempty. -/
theorem append_mem_isLockingSequence
    {M : List α → ℕ} {L : Set α} {xs : List α} {j : ℕ}
    (hlock : GenLimit.Angluin.IsLockingSequence M L xs j)
    {x : α} (hx : x ∈ L) :
    GenLimit.Angluin.IsLockingSequence M L (xs ++ [x]) j :=
  GenLimit.Angluin.append_mem_isLockingSequence hlock hx

theorem conditionTwo_of_identifiable
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (hID : IdentifiableInLimit C) :
    GenLimit.Angluin.ConditionTwo C :=
  GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable C hID

/-- Corollary 2.2. The shared name `ConditionTwo` is the finite-tell-tale
condition printed as Definition 4 in the hallucination-detection paper. -/
theorem corollary_2_2
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ GenLimit.Angluin.ConditionTwo C := by
  rw [theorem_2_1 C]
  constructor
  · exact conditionTwo_of_identifiable C
  · exact identifiable_of_conditionTwo C

end GenLimit.HallucinationDetection
