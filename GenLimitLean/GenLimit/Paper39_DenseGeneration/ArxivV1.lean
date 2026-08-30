import GenLimit.Paper01_LanguageGeneration.Critical
import Mathlib.Data.Set.Finite.Basic

/-!
# #39 Dense Generation: arXiv-v1 criticality

The public arXiv-v1 Definition 3.2 is exactly `GenLimit.Critical`: a critical
language is consistent and is contained in every earlier consistent language.
This file reuses that definition and its existing theory instead of duplicating
it.  In particular, Remark 3.3 and Lemma 3.4 use
`critical_subset_of_le` and `target_eventually_critical` directly.

The small example below records an important difference from the earlier
manuscript's `RecursiveCritical`.  A higher-indexed arXiv-critical language can
appear after an observation while the old focus remains consistent.  Hence the
fixed-scope stability invariant used by the earlier-manuscript patient machine
cannot be transferred to arXiv v1 by replacing one predicate with the other.
-/

namespace GenLimit
namespace Paper39ArxivV1

/-- ArXiv-v1 Definitions 3.5--3.6: `f` is the highest critical index in the
first `scope` entries.  Criticality itself is the shared #01 definition. -/
def IsFocus
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope f : ℕ) : Prop :=
  f < scope ∧ Critical C stream t f ∧
    ∀ j, j < scope → Critical C stream t j → j ≤ f

/-- When a critical target is in scope, the arXiv-v1 focus language is
contained in it.  This is the set-theoretic step in the validity argument. -/
theorem focus_subset_of_critical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope f z : ℕ}
    (hf : IsFocus C stream t scope f)
    (hzScope : z < scope) (hz : Critical C stream t z) :
    C f ⊆ C z := by
  exact critical_subset_of_le (hf.2.2 z hzScope hz) hz hf.2.1

namespace FocusRefreshExample

/-- Three infinite languages suffice to expose the focus-refresh issue:
`L₀ = ℕ \\ {1}`, `L₁ = ℕ \\ {0}`, and `L₂ = L₀`. -/
def family : LanguageFamily
  | 0 => Set.univ \ {1}
  | 1 => Set.univ \ {0}
  | _ => Set.univ \ {1}

/-- The first observation is `0`. -/
def stream : ℕ → ℕ := fun _ => 0

theorem family_infinite (i : ℕ) : (family i).Infinite := by
  rcases i with _ | _ | i
  · exact Set.infinite_univ.diff (Set.finite_singleton 1)
  · exact Set.infinite_univ.diff (Set.finite_singleton 0)
  · exact Set.infinite_univ.diff (Set.finite_singleton 1)

theorem focus_before : IsFocus family stream 0 3 0 := by
  constructor
  · omega
  constructor
  · refine ⟨by simp [Consistent, sample], ?_⟩
    intro i hi _
    have : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    exact Set.Subset.rfl
  · intro j hj hjCritical
    have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjCases with rfl | rfl | rfl
    · exact Nat.le_refl 0
    · have hsubset := hjCritical.2 0 (by omega)
          (by simp [Consistent, sample])
      exact False.elim (by
        simpa [family] using hsubset (show 1 ∈ family 1 by simp [family]))
    · have hsubset := hjCritical.2 1 (by omega)
          (by simp [Consistent, sample])
      exact False.elim (by
        simpa [family] using hsubset (show 0 ∈ family 2 by simp [family]))

theorem old_focus_survives : Consistent family stream 1 0 := by
  simp [Consistent, sample, stream, family]

theorem focus_after : IsFocus family stream 1 3 2 := by
  constructor
  · omega
  constructor
  · refine ⟨by simp [Consistent, sample, stream, family], ?_⟩
    intro i hi hiConsistent
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hiCases with rfl | rfl | rfl
    · simp [family]
    · simp [Consistent, sample, stream, family] at hiConsistent
    · exact Set.Subset.rfl
  · intro j hj _
    omega

/-- The highest arXiv-critical focus changes from `0` to `2` after one
observation although focus `0` remains consistent and the scope stays `3`. -/
theorem focus_changes_while_old_focus_survives :
    IsFocus family stream 0 3 0 ∧
      Consistent family stream 1 0 ∧
      IsFocus family stream 1 3 2 :=
  ⟨focus_before, old_focus_survives, focus_after⟩

/-- Consequently, direct criticality is not stable throughout an unchanged
scope merely because the old focus survives. -/
theorem criticality_not_fixed_below_surviving_focus :
    ¬ (∀ i, i < 3 →
      (Critical family stream 0 i ↔ Critical family stream 1 i)) := by
  intro hstable
  have hnew : Critical family stream 1 2 := focus_after.2.1
  have hold : Critical family stream 0 2 := (hstable 2 (by omega)).2 hnew
  exact (Nat.not_succ_le_zero 1) (focus_before.2.2 2 (by omega) hold)

end FocusRefreshExample
end Paper39ArxivV1
end GenLimit
