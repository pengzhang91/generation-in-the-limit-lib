import GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Diagnostic for the printed Theorem 6.4 construction

The source fixes a base `n` and sets
`m(L_i)=sum_{j<i} n^j`.  Its alleged late distinguishing round is exactly the
next geometric-prefix value plus one.  Thus, for a fixed class/base, that
round remains on the same linear scale; it cannot by itself contradict a
big-O guarantee with an arbitrary hidden constant.
-/

namespace GenLimit.MistakeBounded

open scoped BigOperators

def geometricPrefix (base i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, if 0 < j then base ^ j else 0

@[simp] theorem geometricPrefix_zero (base : ℕ) :
    geometricPrefix base 0 = 0 := by
  simp [geometricPrefix]

theorem geometricPrefix_succ (base i : ℕ) (hi : 0 < i) :
    geometricPrefix base (i + 1) =
      geometricPrefix base i + base ^ i := by
  simp [geometricPrefix, Finset.sum_range_succ, hi]

/-- Exact arithmetic identity behind the quantifier-order problem in the
proof of Theorem 6.4. -/
theorem theorem_6_4_fixed_base_diagnostic
    (base i : ℕ) (hi : 0 < i) :
    geometricPrefix base i + base ^ i + 1 =
      geometricPrefix base (i + 1) + 1 := by
  rw [geometricPrefix_succ base i hi]

end GenLimit.MistakeBounded
