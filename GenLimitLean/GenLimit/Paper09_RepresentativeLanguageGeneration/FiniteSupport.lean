import GenLimit.Paper09_RepresentativeLanguageGeneration.Definitions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Published finite-support condition

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Definitions 4.1--4.2.

This module records the printed condition exactly.  It is kept separate from
both the counterexample showing that the condition is insufficient and the
exact-profile repair used by the corrected theorem.
-/

namespace GenLimit.RepresentativeGeneration

/-- The intersection associated with a subcollection of indexed groups in
published Definition 4.1. -/
def indexedGroupIntersection
    (L : GenLimit.Generic.Language α) (groups : ℕ → Set α)
    (I : Set ℕ) : Set α :=
  L ∩ {x | ∀ i, i ∈ I → x ∈ groups i}

/-- One summand in published Definition 4.1.  Infinite intersections are
omitted, as in the displayed restricted sum in the source. -/
noncomputable def finiteIntersectionContribution
    (L : GenLimit.Generic.Language α) (groups : ℕ → Set α)
    (I : Set ℕ) : ENNReal := by
  classical
  let A := indexedGroupIntersection L groups I
  exact if h : A.Finite then (h.toFinset.card : ENNReal) else 0

/-- Published Definition 4.1, with `∞` available as the value of a
divergent sum. -/
noncomputable def finiteSupportSize
    (L : GenLimit.Generic.Language α) (groups : ℕ → Set α) : ENNReal :=
  ∑' I : Set ℕ, finiteIntersectionContribution L groups I

/-- Published Definition 4.2. -/
def HasFiniteSupport
    (H : GenLimit.Generic.LanguageClass α) (groups : ℕ → Set α) : Prop :=
  ∀ L, L ∈ H → finiteSupportSize L groups < ⊤

/-- The paper's standing assumption that the indexed groups cover the
example universe. -/
def GroupsCover (groups : ℕ → Set α) : Prop :=
  (⋃ i, groups i) = Set.univ

end GenLimit.RepresentativeGeneration
