import GenLimit.Core.GenericGeneration

/-!
# Subset queries for an indexed language family

An exact Boolean inclusion oracle is uniform in two language indices.
This is a semantic access interface. Ordinary computability of the oracle
is a separate assumption, as for the existing membership-oracle interface.
-/

namespace GenLimit

structure SubsetOracle {α : Type*} (C : Generic.LanguageFamily α) where
  query : ℕ → ℕ → Bool
  query_spec : ∀ i j, query i j = true ↔ C i ⊆ C j

end GenLimit
