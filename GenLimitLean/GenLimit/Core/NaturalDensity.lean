import GenLimit.Core.OrderedDensity
import Mathlib.Data.Nat.Nth

/-!
# Ordered density in the natural ordering

Every infinite language has a canonical increasing enumeration. Its ordered
lower density agrees with the ratio of counts in ambient natural-number
prefixes. This lets clients use the shared ordered-density definition while
proving estimates in ambient prefixes.
-/

namespace GenLimit.KleinbergWei.OrderedLanguage

open Filter
open scoped Classical

/-- An infinite language, enumerated in increasing numerical order. -/
noncomputable def increasing (K : Language) (hK : K.Infinite) : OrderedLanguage where
  carrier := K
  enumeration := Nat.nth (· ∈ K)
  enumeration_injective := Nat.nth_injective hK
  range_enumeration := Nat.range_nth_of_infinite hK

/-- The canonical enumeration respects the usual order on natural numbers. -/
theorem increasing_strictMono (K : Language) (hK : K.Infinite) :
    StrictMono (increasing K hK).enumeration :=
  Nat.nth_strictMono hK

/-- Counting the first `|K ∩ [0,n)|` target elements is the same as counting
inside the ambient prefix `[0,n)`. -/
theorem increasing_prefixCount (K : Language) (hK : K.Infinite)
    (A : Language) (n : ℕ) :
    (increasing K hK).prefixCount A (Nat.count (· ∈ K) n) =
      Nat.count (· ∈ A ∩ K) n := by
  unfold prefixCount
  rw [Nat.count_eq_card_filter_range (p := (· ∈ A ∩ K))]
  apply Finset.card_bij (fun i _ => Nat.nth (· ∈ K) i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨Nat.nth_lt_of_lt_count hi.1, hi.2, Nat.nth_mem_of_infinite hK i⟩
  · intro i _ j _ hij
    exact Nat.nth_injective hK hij
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff] at hx
    refine ⟨Nat.count (· ∈ K) x, ?_, Nat.nth_count hx.2.2⟩
    simp only [Finset.mem_filter, Finset.mem_range, increasing, Nat.nth_count hx.2.2]
    exact ⟨Nat.count_strict_mono hx.2.2 hx.1, hx.2.1⟩

/-- Ambient target counts visit every rank and tend to infinity, so replacing
the prefix index by that count preserves the `atTop` filter. -/
theorem map_count_atTop (K : Language) (hK : K.Infinite) :
    map (Nat.count (· ∈ K)) atTop = atTop := by
  apply map_atTop_eq_of_gc (Nat.nth (· ∈ K)) 0 (Nat.count_monotone _)
  · intro a c _
    exact Nat.count_le_iff_le_nth hK
  · intro c _
    exact (Nat.count_nth_of_infinite hK c).ge

/-- Ordered lower density in the increasing target ordering is the ambient
prefix ratio. Intersecting with `K` makes this valid for every measured set. -/
theorem increasing_lowerDensity_eq_liminf (K : Language) (hK : K.Infinite)
    (A : Language) :
    (increasing K hK).lowerDensity A =
      liminf (fun n : ℕ =>
        (Nat.count (· ∈ A ∩ K) n : ℝ) / (Nat.count (· ∈ K) n : ℝ)) atTop := by
  have hratio : ∀ n,
      (increasing K hK).prefixRatio A (Nat.count (· ∈ K) n) =
        (Nat.count (· ∈ A ∩ K) n : ℝ) / (Nat.count (· ∈ K) n : ℝ) := by
    intro n
    by_cases hn : Nat.count (· ∈ K) n = 0
    · simp [hn]
    · simp only [prefixRatio, hn, if_false, increasing_prefixCount]
  calc
    (increasing K hK).lowerDensity A =
        liminf ((increasing K hK).prefixRatio A ∘ Nat.count (· ∈ K)) atTop := by
      rw [liminf_comp, map_count_atTop K hK]
      rfl
    _ = _ := congrArg (fun f : ℕ → ℝ => liminf f atTop) (funext hratio)

end GenLimit.KleinbergWei.OrderedLanguage
