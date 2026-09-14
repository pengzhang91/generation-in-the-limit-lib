import GenLimit.Bridges.Paper12ToPaper15

/-!
# Example: cross a paper boundary through an explicit bridge

Paper #12's infinite-omission enumeration is an injective special case of
Paper #15's infinite partial presentation.  The bridge exposes the named
infinite sublanguage presented by the stream.
-/

namespace GenLimit.Examples

theorem infinite_omission_yields_named_partial_language
    {stream : Generic.Stream ℕ} {K : Generic.Language ℕ}
    (h : NoiseLossFeedback.InfiniteOmissionEnumeration stream K) :
    ∃ E : Generic.Language ℕ,
      Generic.Presents stream E ∧ E.Infinite ∧ E ⊆ K := by
  exact
    (GenLimit.Bridge.Paper12ToPaper15.infiniteOmissionEnumeration_iff_injective_exists_presented_subset
        stream K).mp h |>.2

end GenLimit.Examples
