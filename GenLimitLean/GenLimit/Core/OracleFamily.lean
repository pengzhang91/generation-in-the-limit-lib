import GenLimit.Core.Basic

/-!
# Indexed language families with a membership oracle

This shared record is used by both formalized papers.  The finite-query KM
machine uses all four fields to realize its tests.  The semantic KM generator
and the semantic patient-scope machine use only the indexed languages and
their infinitude, but keeping the common record lets the generators be
compared on exactly the same family.
-/

namespace GenLimit

/-- An indexed infinite language family equipped with a uniform Boolean
membership oracle. -/
structure OracleFamily where
  language : LanguageFamily
  infinite' : ∀ i, (language i).Infinite
  query : ℕ → ℕ → Bool
  query_spec : ∀ i u, query i u = true ↔ u ∈ language i

end GenLimit
