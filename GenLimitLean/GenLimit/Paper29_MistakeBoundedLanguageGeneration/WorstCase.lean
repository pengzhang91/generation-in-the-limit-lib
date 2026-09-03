import GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# The worst-case supremum in Definition 3

The source defines a language-indexed mistake bound as a supremum over every
admissible adversarial stream and over the infinite play.  Using `WithTop ℕ`
makes the possible value `∞` explicit.  The finite-prefix formulation is
equivalent to a uniform natural bound and is the form consumed by the later
potential arguments.
-/

namespace GenLimit.MistakeBounded

/-- Literal extended-natural supremum of all finite-prefix mistake counts. -/
noncomputable def worstCaseMistakes {Run : Type*}
    (trace : Run → MistakeTrace) : WithTop ℕ :=
  ⨆ run, ⨆ t, (mistakeCount (trace run) t : WithTop ℕ)

theorem prefixMistakes_le_worstCase
    {Run : Type*} (trace : Run → MistakeTrace) (run : Run) (t : ℕ) :
    (mistakeCount (trace run) t : WithTop ℕ) ≤
      worstCaseMistakes trace := by
  exact le_iSup_of_le run (le_iSup_of_le t le_rfl)

/-- A natural upper bound on every finite play prefix is exactly an upper
bound on Definition 3's extended supremum. -/
theorem worstCaseMistakes_le_iff
    {Run : Type*} (trace : Run → MistakeTrace) (bound : ℕ) :
    worstCaseMistakes trace ≤ bound ↔
      ∀ run t, mistakeCount (trace run) t ≤ bound := by
  constructor
  · intro h run t
    have hprefix :
        (mistakeCount (trace run) t : WithTop ℕ) ≤
          (bound : WithTop ℕ) :=
      (prefixMistakes_le_worstCase trace run t).trans h
    exact WithTop.coe_le_coe.mp hprefix
  · intro h
    apply iSup_le
    intro run
    apply iSup_le
    intro t
    exact WithTop.coe_le_coe.mpr (h run t)

/-- Pointwise `TotalMistakesAtMost` is the same finite-bound statement. -/
theorem worstCaseMistakes_le_iff_totalMistakesAtMost
    {Run : Type*} (trace : Run → MistakeTrace) (bound : ℕ) :
    worstCaseMistakes trace ≤ bound ↔
      ∀ run, TotalMistakesAtMost (trace run) bound := by
  rw [worstCaseMistakes_le_iff]
  rfl

end GenLimit.MistakeBounded
