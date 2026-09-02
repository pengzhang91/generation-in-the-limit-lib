import GenLimit.Support.FiniteContamination
import GenLimit.Support.EnumerationProgress
import GenLimit.Support.Presentations
import GenLimit.Support.ClassIntersection
import GenLimit.Core.ClassGeneration

/-!
# Noise, Loss, and Feedback: shared semantic utilities

Paper-local time conventions and the ordered-prefix completion used by the
noise and omission arguments.  The generic finite-contamination predicates
live in `GenLimit.Core.FiniteContamination`; the imported Support module
preserves its former compatibility names.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-- The examples observed through paper time `t`, including `x_t`. -/
noncomputable abbrev observedThrough
    (stream : Stream α) (t : ℕ) : Finset α :=
  sample stream (t + 1)

/-- Run a prefix generator after observations `x₀,...,xₜ`. -/
abbrev outputAt
    (gen : Generator α) (stream : Stream α) (t : ℕ) : α :=
  GenLimit.Generic.output gen stream (t + 1)

/-- Validity and freshness in the inclusive-time convention of the paper. -/
def CorrectAt
    (gen : Generator α) (L : Language α)
    (stream : Stream α) (t : ℕ) : Prop :=
  outputAt gen stream t ∈ L ∧
    outputAt gen stream t ∉ observedThrough stream t

/-- The paper's inclusive time `t` is Core's exclusive-prefix time `t+1`. -/
theorem correctAt_iff_generic_succ
    (gen : Generator α) (L : Language α)
    (stream : Stream α) (t : ℕ) :
    CorrectAt gen L stream t ↔
      GenLimit.Generic.CorrectAt gen L stream (t + 1) :=
  Iff.rfl

/-- Keep an ordered finite prefix, then enumerate the remaining infinite
part of the target without repetition. -/
noncomputable def prefixThenTarget
    [Countable α]
    {n : ℕ} (xs : Fin n → α) (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    Stream α :=
  fun k =>
    if hk : k < n then
      xs ⟨k, hk⟩
    else
      GenLimit.Support.infiniteEnumeration
        (L \ (sequenceSample xs : Set α)) hrest (k - n)

theorem prefixThenTarget_prefix
    [Countable α]
    {n : ℕ} (xs : Fin n → α) (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite)
    (k : Fin n) :
    prefixThenTarget xs L hrest k = xs k := by
  simp [prefixThenTarget, k.isLt]

theorem prefixThenTarget_injective
    [Countable α]
    {n : ℕ} {xs : Fin n → α} (hxs : Function.Injective xs)
    (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    Function.Injective (prefixThenTarget xs L hrest) := by
  classical
  intro i j hij
  by_cases hi : i < n
  · by_cases hj : j < n
    · rw [prefixThenTarget, dif_pos hi,
        prefixThenTarget, dif_pos hj] at hij
      exact congrArg Fin.val (hxs hij)
    · have hleft :
          prefixThenTarget xs L hrest i ∈ sequenceSample xs := by
        rw [prefixThenTarget, dif_pos hi]
        exact mem_sequenceSample_iff.mpr ⟨⟨i, hi⟩, rfl⟩
      have hright :
          prefixThenTarget xs L hrest j ∉ (sequenceSample xs : Set α) := by
        rw [prefixThenTarget, dif_neg hj]
        exact
          (GenLimit.Support.infiniteEnumeration_mem
            (L \ (sequenceSample xs : Set α)) hrest (j - n)).2
      exact (hright (hij ▸ hleft)).elim
  · by_cases hj : j < n
    · have hleft :
          prefixThenTarget xs L hrest i ∉ (sequenceSample xs : Set α) := by
        rw [prefixThenTarget, dif_neg hi]
        exact
          (GenLimit.Support.infiniteEnumeration_mem
            (L \ (sequenceSample xs : Set α)) hrest (i - n)).2
      have hright :
          prefixThenTarget xs L hrest j ∈ sequenceSample xs := by
        rw [prefixThenTarget, dif_pos hj]
        exact mem_sequenceSample_iff.mpr ⟨⟨j, hj⟩, rfl⟩
      exact (hleft (hij ▸ hright)).elim
    · rw [prefixThenTarget, dif_neg hi,
        prefixThenTarget, dif_neg hj] at hij
      have hsub : i - n = j - n :=
        GenLimit.Support.infiniteEnumeration_injective
          (L \ (sequenceSample xs : Set α)) hrest hij
      omega

theorem range_prefixThenTarget_eq_prefix_union
    [Countable α]
    {n : ℕ} (xs : Fin n → α) (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    Set.range (prefixThenTarget xs L hrest) =
      (sequenceSample xs : Set α) ∪ L := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨k, rfl⟩
    by_cases hk : k < n
    · left
      rw [prefixThenTarget, dif_pos hk]
      exact mem_sequenceSample_iff.mpr ⟨⟨k, hk⟩, rfl⟩
    · right
      rw [prefixThenTarget, dif_neg hk]
      exact
        (GenLimit.Support.infiniteEnumeration_mem
          (L \ (sequenceSample xs : Set α)) hrest (k - n)).1
  · intro x hx
    rcases hx with hxPrefix | hxL
    · obtain ⟨i, hi⟩ := mem_sequenceSample_iff.mp hxPrefix
      refine ⟨i, ?_⟩
      rw [prefixThenTarget_prefix xs L hrest i]
      exact hi
    · by_cases hxPrefix : x ∈ sequenceSample xs
      · obtain ⟨i, hi⟩ := mem_sequenceSample_iff.mp hxPrefix
        refine ⟨i, ?_⟩
        rw [prefixThenTarget_prefix xs L hrest i]
        exact hi
      · obtain ⟨k, hk⟩ :=
          GenLimit.Support.infiniteEnumeration_surjective
            (L \ (sequenceSample xs : Set α)) hrest
            ⟨hxL, hxPrefix⟩
        refine ⟨n + k, ?_⟩
        have hnot : ¬n + k < n :=
          Nat.not_lt_of_ge (Nat.le_add_right n k)
        simp [prefixThenTarget, hnot, hk]

theorem prefixThenTarget_range
    [Countable α]
    {n : ℕ} {xs : Fin n → α}
    (L : Set α) (hxsL : ∀ i, xs i ∈ L)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    Set.range (prefixThenTarget xs L hrest) = L := by
  rw [range_prefixThenTarget_eq_prefix_union]
  exact Set.union_eq_right.mpr fun x hx => by
    obtain ⟨i, rfl⟩ := mem_sequenceSample_iff.mp hx
    exact hxsL i

theorem prefixThenTarget_sample
    [Countable α]
    {n : ℕ} (xs : Fin n → α) (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    sample (prefixThenTarget xs L hrest) n = sequenceSample xs := by
  classical
  ext x
  simp only [mem_sample_iff, mem_sequenceSample_iff]
  constructor
  · rintro ⟨k, hk, hvalue⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [prefixThenTarget, dif_pos hk] at hvalue
    exact hvalue
  · rintro ⟨k, hk⟩
    refine ⟨k, k.isLt, ?_⟩
    rw [prefixThenTarget_prefix xs L hrest k]
    exact hk

end GenLimit.NoiseLossFeedback
