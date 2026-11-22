import GenLimit.Paper14_ListLanguageIdentification.InfiniteDrawEquivalence
import GenLimit.Paper14_ListLanguageIdentification.StatisticalRates

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

Theorem 3 gives the instance-dependent exponential rate, its optimality on
nontrivial families, and the failure of vanishing rates otherwise. The
statistical proof uses full-support laws and allows randomized output lists.
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

open Statistical Filter

/-- Theorem 3, with the nontriviality qualification for the optimality bound. -/
theorem theorem_3 [Countable α] [DecidableEq α] (F : Generic.LanguageFamily α) (k : ℕ)
    (hne : ∀ i, (F i).Nonempty) :
    (ListIdentifiable F k → ∃ A : Kernel α k, Exponential F A) ∧
    (NontrivialFor F k → ∀ A : Kernel α k, ∃ (i : ℕ) (p : PMF α), p.support = F i ∧
      ∃ᶠ n : ℕ in atTop, Real.exp (-2*(n : ℝ)) ≤ error F A p (F i) n) ∧
    (¬ ListIdentifiable F k → ∀ A : Kernel α k, ∃ (i : ℕ) (p : PMF α), p.support = F i ∧
      ∃ᶠ n : ℕ in atTop, 1 / ((k : ℝ)+2) < error F A p (F i) n) :=
  Statistical.theorem_3 F k hne

/-- Theorem 9 on a fair infinite bit tape, with one bit per input symbol. -/
theorem theorem_9 (F : Generic.LanguageFamily α) (k : ℕ) (p : ℝ) (hp : p ≤ 1) :
    (ListIdentifiable F k → Probabilistic.Identifies F k p) ∧
      ((k : ℝ)/(k+1) < p → Probabilistic.Identifies F k p → ListIdentifiable F k) :=
  Probabilistic.theorem_9 F k p hp

/-- Theorem 10 compares eventual success probabilities on genuine IID draws
and on each exact presentation with a fair bit tape. -/
theorem theorem_10 [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (F : Generic.LanguageFamily α) (k : ℕ) (p : ℝ) (hp : p ≤ 1) :
    InfiniteDraws.Identifies F k p ↔ Probabilistic.Identifies F k p :=
  InfiniteDraws.theorem_10 F k p hp

end GenLimit.ListIdentification.Results
