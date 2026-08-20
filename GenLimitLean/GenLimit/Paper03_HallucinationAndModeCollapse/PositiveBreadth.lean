import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineReductions

/-!
# The positive online direction of Theorem 3.5

Once a positive-data identifier has stabilized, use the identified language
itself as the generator support, deleting the finite positive sample under the
fresh-output convention.  A uniform membership oracle for the indexed family
supplies the support-membership oracle required by Definitions 5--6.

The construction is semantic with respect to the identifier: it does not
assert that an arbitrary Lean function is a Turing-machine implementation.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic

noncomputable local instance positiveBreadthPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Support of the language currently named by `M`, with the positive sample
removed. -/
noncomputable def identifiedFreshGenerator
    {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C)
    (M : GenLimit.Angluin.SemanticIdentifier ℕ) :
    SupportGenerator where
  support _t xs := C (M (List.ofFn xs)) \ ↑(Generic.sequenceSample xs)
  query t xs x :=
    if x ∈ Generic.sequenceSample xs then false
    else O.query (M (List.ofFn xs)) x
  query_spec := by
    intro t xs x
    by_cases hx : x ∈ Generic.sequenceSample xs
    · simp [hx]
    · simp [hx, O.query_spec]

theorem identifiedFreshGenerator_supportAt
    {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C)
    (M : GenLimit.Angluin.SemanticIdentifier ℕ)
    (stream : Stream ℕ) (t : ℕ) :
    supportAt (identifiedFreshGenerator O M) stream t =
      C (M (GenLimit.textPrefix stream t)) \
        ↑(Generic.sample stream t) := by
  change C (M (List.ofFn (fun i : Fin t => stream i))) \
      ↑(Generic.sequenceSample (fun i : Fin t => stream i)) = _
  rw [← GenLimit.textPrefix_eq_ofFn, Generic.sequenceSample_prefix]

theorem identifiedFreshGenerator_breadth
    {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C)
    {M : GenLimit.Angluin.SemanticIdentifier ℕ}
    (hM : GenLimit.Angluin.SemanticallyIdentifies M C) :
    FreshBreadthInLimit (identifiedFreshGenerator O M) C := by
  intro z stream hP
  obtain ⟨j, hj, T, hT⟩ := hM z stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have hMt : M (GenLimit.textPrefix stream t) = j := by
    simpa only using hT t ht
  rw [identifiedFreshGenerator_supportAt, hMt, hj]

/-- Semantic identification yields exact fresh breadth under a uniform
language-membership oracle. -/
theorem identifiableInLimit_implies_freshBreadthInLimit
    {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C)
    (hID : IdentifiableInLimit C) :
    ∃ G : SupportGenerator, FreshBreadthInLimit G C := by
  obtain ⟨M, hM⟩ := hID
  exact ⟨identifiedFreshGenerator O M,
    identifiedFreshGenerator_breadth O hM⟩

/-- Theorem 3.5 as an exact semantic online biconditional under the paper's
uniform language-membership oracle.  The left-to-right generator has a Boolean
support oracle; the theorem does not claim a code-level computability proof
for an arbitrary semantic identifier. -/
theorem identifiableInLimit_iff_freshBreadthInLimit
    {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) :
    IdentifiableInLimit C ↔
      ∃ G : SupportGenerator, FreshBreadthInLimit G C := by
  constructor
  · exact identifiableInLimit_implies_freshBreadthInLimit O
  · rintro ⟨G, hG⟩
    exact freshBreadthInLimit_implies_identifiableInLimit hG

end GenLimit.HallucinationModeCollapse
