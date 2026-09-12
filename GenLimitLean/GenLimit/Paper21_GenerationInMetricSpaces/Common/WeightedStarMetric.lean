import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import Mathlib.Topology.MetricSpace.Basic

/-!
# Weighted-star metrics

Several Paper21 diagnostics use the same elementary geometry: every point is
assigned a nonnegative arm length, and the distance between two distinct
points is the sum of their arm lengths.  This module contains the shared
metric verification; individual diagnostics retain their own point types and
weight functions.
-/

namespace GenLimit.MetricSpaces.WeightedStar

/-- Distinct points are joined through the omitted or explicit star hub. -/
def distance [DecidableEq α] (weight : α → ℝ) : Distance α :=
  fun x y => if x = y then 0 else weight x + weight y

@[simp] theorem distance_self [DecidableEq α]
    (weight : α → ℝ) (x : α) :
    distance weight x x = 0 := by
  simp [distance]

theorem distance_nonneg [DecidableEq α]
    (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (x y : α) :
    0 ≤ distance weight x y := by
  by_cases hxy : x = y
  · simp [distance, hxy]
  · rw [distance, if_neg hxy]
    exact add_nonneg (hweight x) (hweight y)

theorem distance_comm [DecidableEq α]
    (weight : α → ℝ) (x y : α) :
    distance weight x y = distance weight y x := by
  by_cases hxy : x = y
  · subst y
    simp
  · have hyx : y ≠ x := Ne.symm hxy
    simp [distance, hxy, hyx, add_comm]

theorem distance_triangle [DecidableEq α]
    (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (x y z : α) :
    distance weight x z ≤
      distance weight x y + distance weight y z := by
  by_cases hxz : x = z
  · subst z
    rw [distance_self]
    exact add_nonneg
      (distance_nonneg weight hweight x y)
      (distance_nonneg weight hweight y x)
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hyz : y = z
  · subst z
    simp
  rw [distance, if_neg hxz,
    distance, if_neg hxy,
    distance, if_neg hyz]
  have hy := hweight y
  linarith

theorem eq_of_distance_eq_zero [DecidableEq α]
    (weight : α → ℝ)
    (hpair : ∀ {x y}, x ≠ y → 0 < weight x + weight y)
    {x y : α} (hzero : distance weight x y = 0) :
    x = y := by
  by_contra hxy
  rw [distance, if_neg hxy] at hzero
  have hpos := hpair hxy
  linarith

/-- Construct the genuine metric induced by nonnegative arm lengths, provided
the two arm lengths of every distinct pair have positive sum. -/
def metricSpace [DecidableEq α]
    (weight : α → ℝ)
    (hweight : ∀ x, 0 ≤ weight x)
    (hpair : ∀ {x y}, x ≠ y → 0 < weight x + weight y) :
    MetricSpace α where
  dist := distance weight
  dist_self := distance_self weight
  dist_comm := distance_comm weight
  dist_triangle := distance_triangle weight hweight
  eq_of_dist_eq_zero := eq_of_distance_eq_zero weight hpair

end GenLimit.MetricSpaces.WeightedStar
