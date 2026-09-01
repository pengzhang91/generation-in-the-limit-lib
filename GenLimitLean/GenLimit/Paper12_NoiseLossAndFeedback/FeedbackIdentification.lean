import GenLimit.Paper12_NoiseLossAndFeedback.MandatoryQuery
import GenLimit.Paper00_LanguageIdentification.Informant.Enumeration
import GenLimit.Bridges.IndexedFamilyToClass

/-!
# Noise, Loss, and Feedback: non-uniform identification with feedback

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Section 6.2,
Definitions 6.8--6.9, Algorithm 6, and Theorem 1.8.

An identifier receives the positive observations and all earlier membership
answers, asks one membership query, and then outputs an index in the fixed
language family.  The convergence time may depend on the target language but
not on its positive enumeration.

The proof reuses the complete-informant elimination theorem from the Gold
development.  Algorithm 6 queries `t` at time `t`, so its answers form the
canonical complete informant for the target.  Positive observations impose
additional consistency constraints, but never eliminate the true target.

This is a semantic formalization: membership answers and least consistent
indices are selected classically, with no computability or runtime claim.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## Definitions 6.8--6.9 -/

/-- Definition 6.8.  A mandatory-query machine whose post-answer output is
a family index. -/
abbrev FeedbackIdentifier (α : Type*) :=
  MandatoryQueryMachine α ℕ

namespace FeedbackIdentifier

/-- Compatibility constructor retaining the original paper-facing API. -/
abbrev mk
    (query :
      (t : ℕ) → (Fin (t + 1) → α) → (Fin t → Bool) → α)
    (output :
      (t : ℕ) → (Fin (t + 1) → α) → (Fin (t + 1) → Bool) → ℕ) :
    FeedbackIdentifier α :=
  MandatoryQueryMachine.mk query output

/-- Paper-facing query projection. -/
abbrev query (identifier : FeedbackIdentifier α) :=
  MandatoryQueryMachine.query identifier

/-- Paper-facing output projection. -/
abbrev output (identifier : FeedbackIdentifier α) :=
  MandatoryQueryMachine.output identifier

end FeedbackIdentifier

/-- Paper-facing name for the shared truthful mandatory-query response. -/
noncomputable abbrev actualIdentifierResponse
    (identifier : FeedbackIdentifier α)
    (target : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α)
    (t : ℕ) : Bool :=
  actualMandatoryQueryResponse identifier target stream t

/-- Paper-facing name for the shared post-answer output execution. -/
noncomputable abbrev actualIdentifierOutput
    (identifier : FeedbackIdentifier α)
    (target : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α)
    (t : ℕ) : ℕ :=
  actualMandatoryQueryOutput identifier target stream t

/-- Definition 6.9 at a fixed identifier.  The threshold may depend on the
target index, but is uniform over all repetition-free exact enumerations of
that target. -/
def NonuniformlyIdentifiesWithFeedback
    (identifier : FeedbackIdentifier α)
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∃ T, ∀ stream,
    ExactEnumeration stream (C z) →
      ∀ t, T ≤ t →
        C (actualIdentifierOutput identifier (C z) stream t) = C z

/-- Existence of a non-uniform feedback identifier for an indexed family. -/
def NonuniformlyIdentifiableWithFeedback
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ identifier : FeedbackIdentifier α,
    NonuniformlyIdentifiesWithFeedback identifier C

/-! ## Algorithm 6 -/

/-- The membership-query answers through the current time, viewed as a
finite informant prefix.  Algorithm 6 queries universe element `j` at time
`j`. -/
def queriedInformantHistory
    {n : ℕ} (responses : Fin n → Bool) :
    List GenLimit.Gold.Informant.InformantDatum :=
  List.ofFn (fun j => (j.1, responses j))

/-- Algorithm 6's consistency test: all positive observations belong to the
candidate, and all membership answers agree with it. -/
def FeedbackIdentificationCandidate
    (C : GenLimit.Generic.LanguageFamily ℕ) {n : ℕ}
    (observations : Fin n → ℕ)
    (responses : Fin n → Bool) (i : ℕ) : Prop :=
  (∀ j, observations j ∈ C i) ∧
    GenLimit.Gold.Informant.InformantCompatible
      (queriedInformantHistory responses) (C i)

/-- Candidate indices considered by Algorithm 6 at time `t`. -/
noncomputable def feedbackIdentificationCandidates
    (C : GenLimit.Generic.LanguageFamily ℕ) (t : ℕ)
    (observations : Fin (t + 1) → ℕ)
    (responses : Fin (t + 1) → Bool) : Finset ℕ := by
  classical
  exact (Finset.range (t + 1)).filter
    (FeedbackIdentificationCandidate C observations responses)

@[simp] theorem mem_feedbackIdentificationCandidates
    {C : GenLimit.Generic.LanguageFamily ℕ} {t i : ℕ}
    {observations : Fin (t + 1) → ℕ}
    {responses : Fin (t + 1) → Bool} :
    i ∈ feedbackIdentificationCandidates C t observations responses ↔
      i < t + 1 ∧
        FeedbackIdentificationCandidate C observations responses i := by
  classical
  simp [feedbackIdentificationCandidates]

/-- Algorithm 6: query `t`, then output the least currently consistent index
among `0,...,t`, using `0` only when there is no candidate. -/
noncomputable def algorithmSix
    (C : GenLimit.Generic.LanguageFamily ℕ) : FeedbackIdentifier ℕ where
  query := fun t _observations _responses => t
  output := by
    classical
    intro t observations responses
    let candidates :=
      feedbackIdentificationCandidates C t observations responses
    exact if h : candidates.Nonempty then candidates.min' h else 0

@[simp] theorem algorithmSix_query
    (C : GenLimit.Generic.LanguageFamily ℕ) (t : ℕ)
    (observations : Fin (t + 1) → ℕ)
    (responses : Fin t → Bool) :
    (algorithmSix C).query t observations responses = t :=
  rfl

@[simp] theorem actualIdentifierResponse_algorithmSix
    (C : GenLimit.Generic.LanguageFamily ℕ)
    (target : GenLimit.Generic.Language ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    actualIdentifierResponse (algorithmSix C) target stream t =
      membershipAnswer target t := by
  change
    actualMandatoryQueryResponse (algorithmSix C) target stream t =
      membershipAnswer target t
  rw [actualMandatoryQueryResponse_eq]
  rfl

/-- The canonical complete informant obtained by querying natural numbers in
order. -/
noncomputable def membershipInformant
    (target : GenLimit.Generic.Language ℕ) :
    GenLimit.Gold.Informant.InformantStream :=
  fun t => (t, membershipAnswer target t)

theorem membershipInformant_isInformantFor
    (target : GenLimit.Generic.Language ℕ) :
    GenLimit.Gold.Informant.IsInformantFor
      (membershipInformant target) target := by
  constructor
  · intro t
    classical
    simp [membershipInformant, membershipAnswer]
  · intro u
    exact ⟨u, rfl⟩

theorem queriedInformantHistory_actualAlgorithmSix
    (C : GenLimit.Generic.LanguageFamily ℕ)
    (target : GenLimit.Generic.Language ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    queriedInformantHistory
        (fun i : Fin (t + 1) =>
          actualIdentifierResponse (algorithmSix C) target stream i) =
      GenLimit.textPrefix (membershipInformant target) (t + 1) := by
  simp [queriedInformantHistory, GenLimit.textPrefix_eq_ofFn,
    membershipInformant]

theorem algorithmSix_output_eq_min'
    {C : GenLimit.Generic.LanguageFamily ℕ} {t : ℕ}
    {observations : Fin (t + 1) → ℕ}
    {responses : Fin (t + 1) → Bool}
    (hne :
      (feedbackIdentificationCandidates C t observations responses).Nonempty) :
    (algorithmSix C).output t observations responses =
      (feedbackIdentificationCandidates C t observations responses).min' hne := by
  classical
  unfold FeedbackIdentifier.output
  simp only [algorithmSix]
  rw [dif_pos hne]

theorem algorithmSix_output_mem
    {C : GenLimit.Generic.LanguageFamily ℕ} {t : ℕ}
    {observations : Fin (t + 1) → ℕ}
    {responses : Fin (t + 1) → Bool}
    (hne :
      (feedbackIdentificationCandidates C t observations responses).Nonempty) :
    (algorithmSix C).output t observations responses ∈
      feedbackIdentificationCandidates C t observations responses := by
  rw [algorithmSix_output_eq_min' hne]
  exact Finset.min'_mem _ _

theorem algorithmSix_output_le
    {C : GenLimit.Generic.LanguageFamily ℕ} {t i : ℕ}
    {observations : Fin (t + 1) → ℕ}
    {responses : Fin (t + 1) → Bool}
    (hi :
      i ∈ feedbackIdentificationCandidates C t observations responses) :
    (algorithmSix C).output t observations responses ≤ i := by
  have hne :
      (feedbackIdentificationCandidates C t observations responses).Nonempty :=
    ⟨i, hi⟩
  rw [algorithmSix_output_eq_min' hne]
  exact Finset.min'_le _ _ hi

/-! ## Correctness and Theorem 1.8 -/

/-- The true target (or any index denoting it) remains an Algorithm 6
candidate on every valid positive presentation. -/
theorem target_mem_feedbackIdentificationCandidates
    {C : GenLimit.Generic.LanguageFamily ℕ} {z i t : ℕ}
    {stream : GenLimit.Generic.Stream ℕ}
    (hExact : ExactEnumeration stream (C z))
    (hi : C i = C z) (hit : i < t + 1) :
    i ∈ feedbackIdentificationCandidates C t
      (fun j => stream j)
      (fun j =>
        actualIdentifierResponse (algorithmSix C) (C z) stream j) := by
  rw [mem_feedbackIdentificationCandidates]
  refine ⟨hit, ?_, ?_⟩
  · intro j
    rw [hi]
    exact hExact.streamIn ⟨j, rfl⟩
  · rw [queriedInformantHistory_actualAlgorithmSix]
    rw [hi]
    exact GenLimit.Gold.Informant.informantCompatible_target
      (membershipInformant_isInformantFor (C z)) (t + 1)

/-- Algorithm 6 stabilizes to the least family index denoting the target.
This strengthens Definition 6.9, which asks only for eventual extensional
correctness of the output index. -/
theorem algorithmSix_stabilizesTo_leastEqualName
    (C : GenLimit.Generic.LanguageFamily ℕ) (z : ℕ) :
    ∃ T, ∀ stream,
      ExactEnumeration stream (C z) →
        ∀ t, T ≤ t →
          actualIdentifierOutput (algorithmSix C) (C z) stream t =
            GenLimit.Gold.Informant.leastEqualName C z := by
  classical
  let k := GenLimit.Gold.Informant.leastEqualName C z
  have hkTarget : C k = C z :=
    GenLimit.Gold.Informant.leastEqualName_spec C z
  obtain ⟨T, hT⟩ :=
    GenLimit.Gold.Informant.finite_scope_eventually_informantCompatible_iff_eq
      (membershipInformant_isInformantFor (C z)) (k + 1)
  refine ⟨max T k, ?_⟩
  intro stream hExact t ht
  have hTt : T ≤ t + 1 :=
    le_trans (Nat.le_max_left T k) ht |>.trans (Nat.le_succ t)
  have hkt : k < t + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.le_max_right T k) ht)
  have hkMem :
      k ∈ feedbackIdentificationCandidates C t
        (fun j => stream j)
        (fun j =>
          actualIdentifierResponse (algorithmSix C) (C z) stream j) :=
    target_mem_feedbackIdentificationCandidates hExact hkTarget hkt
  have hne :
      (feedbackIdentificationCandidates C t
        (fun j => stream j)
        (fun j =>
          actualIdentifierResponse (algorithmSix C) (C z) stream j)).Nonempty :=
    ⟨k, hkMem⟩
  let n := actualIdentifierOutput (algorithmSix C) (C z) stream t
  have hnOutput :
      n = (algorithmSix C).output t
        (fun j => stream j)
        (fun j =>
          actualIdentifierResponse (algorithmSix C) (C z) stream j) :=
    rfl
  have hnMem :
      n ∈ feedbackIdentificationCandidates C t
        (fun j => stream j)
        (fun j =>
          actualIdentifierResponse (algorithmSix C) (C z) stream j) := by
    rw [hnOutput]
    exact algorithmSix_output_mem hne
  have hnk : n ≤ k := by
    rw [hnOutput]
    exact algorithmSix_output_le hkMem
  have hnCompatible :
      GenLimit.Gold.Informant.InformantCompatible
        (GenLimit.textPrefix (membershipInformant (C z)) (t + 1))
        (C n) := by
    have hnCandidate := (mem_feedbackIdentificationCandidates.mp hnMem).2.2
    rw [queriedInformantHistory_actualAlgorithmSix] at hnCandidate
    exact hnCandidate
  have hnTarget : C n = C z :=
    (hT (t + 1) hTt n (Nat.lt_succ_of_le hnk)).mp hnCompatible
  have hkn : k ≤ n :=
    GenLimit.Gold.Informant.leastEqualName_minimal C z n hnTarget
  exact Nat.le_antisymm hnk hkn

theorem algorithmSix_nonuniformlyIdentifiesWithFeedback
    (C : GenLimit.Generic.LanguageFamily ℕ) :
    NonuniformlyIdentifiesWithFeedback (algorithmSix C) C := by
  intro z
  obtain ⟨T, hT⟩ := algorithmSix_stabilizesTo_leastEqualName C z
  refine ⟨T, ?_⟩
  intro stream hExact t ht
  rw [hT stream hExact t ht]
  exact GenLimit.Gold.Informant.leastEqualName_spec C z

/-- Theorem 1.8: every explicitly indexed countable collection of languages
is non-uniformly identifiable with membership feedback. -/
theorem theorem_1_8 (C : GenLimit.Generic.LanguageFamily ℕ) :
    NonuniformlyIdentifiableWithFeedback C :=
  ⟨algorithmSix C, algorithmSix_nonuniformlyIdentifiesWithFeedback C⟩

/-- Extensional class-facing form of Theorem 1.8.  A nonempty countable class
admits an indexed presentation, and that presentation is non-uniformly
identifiable with feedback. -/
theorem theorem_1_8_countable_class
    {C : GenLimit.Generic.LanguageClass ℕ} (hCountable : C.Countable)
    (hNonempty : C.Nonempty) :
    ∃ E : GenLimit.Bridge.ClassEnumeration C,
      NonuniformlyIdentifiableWithFeedback E.family := by
  let E := GenLimit.Bridge.ClassEnumeration.ofCountable hCountable hNonempty
  exact ⟨E, theorem_1_8 E.family⟩

end GenLimit.NoiseLossFeedback
