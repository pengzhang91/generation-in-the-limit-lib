import GenLimit.Paper14_ListLanguageIdentification.Stratification

/-!
# Paper 14: main-results overview

This module is the public results facade for Charikar--Pabbaraju--Tewari,
*A Characterization of List Language Identification in the Limit*
(arXiv:2511.04103v1).  Its declarations are thin wrappers around the
canonical proof modules and do not duplicate their proofs.

## Coverage boundary

The deterministic Theorems 1 and 2 are formalized at the paper's semantic
interface.  An indexed collection is represented by
`F : ℕ → GenLimit.Generic.Language α`; exact positive presentations are made
explicit because they are the only part of the paper's countable, nonempty
universe assumptions needed by the proof.  Correctness is behavioral: every
eventual output list contains an index denoting the target language, while
the chosen correct index may vary.

Theorem 3 and Sections 8--10, concerning i.i.d. inputs, randomized
identifiers, and statistical rates, are not formalized.  The development is
classical and semantic; it makes no computability or running-time claim.
-/

namespace GenLimit.ListIdentification.Results

open GenLimit.ListIdentification

/-- Overview Theorem 1: a presentable indexed family is `k`-list
identifiable exactly when it satisfies the recursive `k`-Angluin condition.
The canonical proof combines the detailed upper and lower bounds, Theorems 6
and 7. -/
theorem theorem_1
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i))
    (k : ℕ) :
    ListIdentifiable F k ↔ KAngluinCondition F k :=
  listIdentifiable_iff_kAngluin hPresentable k

/-- Overview Theorem 2: `k`-list identifiability is equivalent to the
paper's `k`-layer stratification into relative Angluin-identifiable
subcollections. -/
theorem theorem_2
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i))
    (k : ℕ) :
    ListIdentifiable F k ↔ HasAngluinStratification F k :=
  listIdentifiable_iff_stratification hPresentable k

end GenLimit.ListIdentification.Results
