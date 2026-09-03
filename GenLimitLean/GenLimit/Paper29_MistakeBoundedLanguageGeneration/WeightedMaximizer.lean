import GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedStep
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

/-!
# Weighted maximizers on an arbitrary universe

Algorithm 1 of Kleinberg--Peale--Reingold asks for an unseen point maximizing
the total weight of the languages that contain it.  The point universe need
not be finite: for a fixed finite active class, the score depends only on the
finite membership pattern of a point across that class.  Consequently only
finitely many score values are realizable.

This module packages that observation.  Whenever at least one fresh point
exists, a fresh score maximizer exists.  In particular, this holds on every
infinite universe after excluding an arbitrary finite sample.  The selector
is intentionally noncomputable; this is the semantic argmax required by the
paper, not a claim about runtime or effective search.
-/

namespace GenLimit.MistakeBounded

open scoped BigOperators

/-- The active-language membership pattern realized by a point. -/
noncomputable def weightedMembershipPattern
    (active : Finset ι) (language : ι → Set α) (x : α) :
    Finset ι := by
  classical
  exact active.filter fun i => x ∈ language i

/-- The score attached to a membership pattern. -/
noncomputable def weightedPatternScore
    (weight : ι → ℝ) (pattern : Finset ι) : ℝ :=
  ∑ i ∈ pattern, weight i

/-- A weighted score is exactly the score of the point's finite membership
pattern. -/
theorem weightedScore_eq_patternScore
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (x : α) :
    weightedScore active weight language x =
      weightedPatternScore weight
        (weightedMembershipPattern active language x) := by
  classical
  simp only [weightedScore, weightedPatternScore,
    weightedMembershipPattern]
  rw [Finset.sum_filter]

/-- Membership patterns realized by points outside a finite forbidden set. -/
noncomputable def freshMembershipPatterns
    (active : Finset ι) (language : ι → Set α)
    (seen : Finset α) : Finset (Finset ι) := by
  classical
  exact active.powerset.filter fun pattern =>
    ∃ x, x ∉ seen ∧
      weightedMembershipPattern active language x = pattern

theorem mem_freshMembershipPatterns_iff
    (active : Finset ι) (language : ι → Set α)
    (seen : Finset α) (pattern : Finset ι) :
    pattern ∈ freshMembershipPatterns active language seen ↔
      pattern ⊆ active ∧
        ∃ x, x ∉ seen ∧
          weightedMembershipPattern active language x = pattern := by
  classical
  simp [freshMembershipPatterns]

theorem weightedMembershipPattern_mem_fresh
    (active : Finset ι) (language : ι → Set α)
    (seen : Finset α) {x : α} (hx : x ∉ seen) :
    weightedMembershipPattern active language x ∈
      freshMembershipPatterns active language seen := by
  classical
  rw [mem_freshMembershipPatterns_iff]
  refine ⟨?_, ⟨x, hx, rfl⟩⟩
  intro i hi
  exact (Finset.mem_filter.mp
    (show i ∈ active.filter (fun j => x ∈ language j) by
      simpa [weightedMembershipPattern] using hi)).1

theorem freshMembershipPatterns_nonempty
    (active : Finset ι) (language : ι → Set α)
    (seen : Finset α) (hfresh : ∃ x, x ∉ seen) :
    (freshMembershipPatterns active language seen).Nonempty := by
  obtain ⟨x, hx⟩ := hfresh
  exact ⟨weightedMembershipPattern active language x,
    weightedMembershipPattern_mem_fresh active language seen hx⟩

/-- Although the point universe can be infinite, a maximum fresh weighted
score exists because only finitely many active-language patterns occur. -/
theorem exists_fresh_weightedScore_maximizer
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (seen : Finset α)
    (hfresh : ∃ x, x ∉ seen) :
    ∃ y, y ∉ seen ∧
      ∀ x, x ∉ seen →
        weightedScore active weight language x ≤
          weightedScore active weight language y := by
  classical
  let patterns := freshMembershipPatterns active language seen
  have hpatterns : patterns.Nonempty :=
    freshMembershipPatterns_nonempty active language seen hfresh
  obtain ⟨best, hbest, hmax⟩ :=
    patterns.exists_max_image (weightedPatternScore weight) hpatterns
  have hrealized :
      ∃ y, y ∉ seen ∧
        weightedMembershipPattern active language y = best :=
    ((mem_freshMembershipPatterns_iff
      active language seen best).mp hbest).2
  obtain ⟨y, hy, hyPattern⟩ := hrealized
  refine ⟨y, hy, ?_⟩
  intro x hx
  have hxPattern :
      weightedMembershipPattern active language x ∈ patterns :=
    weightedMembershipPattern_mem_fresh active language seen hx
  have hle := hmax
    (weightedMembershipPattern active language x) hxPattern
  rw [weightedScore_eq_patternScore,
    weightedScore_eq_patternScore, hyPattern]
  exact hle

/-- A noncomputable semantic implementation of the paper's unseen argmax,
assuming that a fresh point exists. -/
noncomputable def freshWeightedMaximizer
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (seen : Finset α)
    (hfresh : ∃ x, x ∉ seen) : α :=
  Classical.choose
    (exists_fresh_weightedScore_maximizer
      active weight language seen hfresh)

theorem freshWeightedMaximizer_not_mem
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (seen : Finset α)
    (hfresh : ∃ x, x ∉ seen) :
    freshWeightedMaximizer active weight language seen hfresh ∉ seen :=
  (Classical.choose_spec
    (exists_fresh_weightedScore_maximizer
      active weight language seen hfresh)).1

theorem freshWeightedMaximizer_spec
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (seen : Finset α)
    (hfresh : ∃ x, x ∉ seen) :
    ∀ x, x ∉ seen →
      weightedScore active weight language x ≤
        weightedScore active weight language
          (freshWeightedMaximizer
            active weight language seen hfresh) :=
  (Classical.choose_spec
    (exists_fresh_weightedScore_maximizer
      active weight language seen hfresh)).2

/-- Every finite forbidden set in an infinite universe has a point outside
it, in the precise form needed by `freshWeightedMaximizer`. -/
theorem exists_fresh_of_infinite
    [Infinite α] (seen : Finset α) :
    ∃ x, x ∉ seen := by
  obtain ⟨x, _hxUniv, hx⟩ :=
    (Set.infinite_univ : (Set.univ : Set α).Infinite).exists_notMem_finset
      seen
  exact ⟨x, hx⟩

/-- The semantic weighted argmax is total on every infinite point universe. -/
noncomputable def infiniteFreshWeightedMaximizer
    [Infinite α]
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (seen : Finset α) : α :=
  freshWeightedMaximizer active weight language seen
    (exists_fresh_of_infinite seen)

theorem infiniteFreshWeightedMaximizer_not_mem
    [Infinite α]
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (seen : Finset α) :
    infiniteFreshWeightedMaximizer active weight language seen ∉ seen :=
  freshWeightedMaximizer_not_mem active weight language seen
    (exists_fresh_of_infinite seen)

theorem infiniteFreshWeightedMaximizer_spec
    [Infinite α]
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (seen : Finset α) :
    ∀ x, x ∉ seen →
      weightedScore active weight language x ≤
        weightedScore active weight language
          (infiniteFreshWeightedMaximizer
            active weight language seen) :=
  freshWeightedMaximizer_spec active weight language seen
    (exists_fresh_of_infinite seen)

end GenLimit.MistakeBounded
