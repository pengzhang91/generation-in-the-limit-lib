import Mathlib.Data.Set.Basic

/-!
# Pareto-optimal generation-time vectors

Paper-facing order definitions for Charikar--Pabbaraju,
*Pareto-optimal Non-uniform Language Generation*, arXiv:2510.02795v1.
Indices are shifted from the paper's `1,2,...` convention to Lean's
`0,1,...`; generation times remain positive naturals in source-facing uses.
-/

namespace GenLimit.ParetoGeneration

/-- One non-uniform generation-time assignment. -/
abbrev TimeVector := ℕ → ℕ

/-- `s` improves `t` at at least one language. -/
def ImprovesSomewhere (s t : TimeVector) : Prop :=
  ∃ i, s i < t i

/-- `s` is worse than `t` at at least one language. -/
def WorseSomewhere (s t : TimeVector) : Prop :=
  ∃ i, t i < s i

/-- Definition 3: no achievable vector can improve one coordinate without
worsening another. -/
def ParetoOptimal (Achievable : Set TimeVector) (t : TimeVector) : Prop :=
  ∀ s ∈ Achievable, ImprovesSomewhere s t → WorseSomewhere s t

/-- The stronger, index-local conclusion proved in Claim 3.1. -/
def EarlierTradeoff (benchmark : TimeVector) (Achievable : Set TimeVector) :
    Prop :=
  ∀ s ∈ Achievable, ∀ i, s i < benchmark i →
    ∃ j < i, benchmark j < s j

/-- The order-theoretic last step used after Claim 3.1: an earlier-index
tradeoff puts the benchmark on the Pareto lower frontier.  The difficult
language-intersection argument establishing `EarlierTradeoff` is not part of
this lemma. -/
theorem earlierTradeoff_implies_paretoOptimal
    {benchmark : TimeVector} {Achievable : Set TimeVector}
    (htrade : EarlierTradeoff benchmark Achievable) :
    ParetoOptimal Achievable benchmark := by
  intro s hs himprove
  obtain ⟨i, hi⟩ := himprove
  obtain ⟨j, -, hj⟩ := htrade s hs i hi
  exact ⟨j, hj⟩

/-- Agreement on the first `n` languages, used in overview Theorem 1. -/
def MatchesPrefix (n : ℕ) (s t : TimeVector) : Prop :=
  ∀ i, i < n → s i = t i

theorem matchesPrefix_mono
    {m n : ℕ} (hmn : m ≤ n) {s t : TimeVector}
    (h : MatchesPrefix n s t) :
    MatchesPrefix m s t := by
  intro i hi
  exact h i (lt_of_lt_of_le hi hmn)

theorem matchesPrefix_refl (n : ℕ) (t : TimeVector) :
    MatchesPrefix n t t := by
  intro i hi
  rfl

end GenLimit.ParetoGeneration
