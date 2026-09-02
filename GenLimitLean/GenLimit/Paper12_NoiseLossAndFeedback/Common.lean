import GenLimit.Support.FiniteContamination
import GenLimit.Support.PrefixCompletion
import GenLimit.Support.Presentations
import GenLimit.Support.ClassIntersection
import GenLimit.Core.ClassGeneration

/-!
# Noise, Loss, and Feedback: shared semantic utilities

Paper-local time conventions and compatibility names for the neutral prefix
completion API.  Generic finite-contamination predicates live in
`GenLimit.Core.FiniteContamination`, while ordered prefix completion lives in
`GenLimit.Support.PrefixCompletion`.
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

/-! ## Compatibility names for the neutral prefix-completion API -/

noncomputable abbrev prefixThenTarget
    [Countable α]
    {n : ℕ} (xs : Fin n → α) (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    Stream α :=
  GenLimit.Support.prefixThenTarget xs L hrest

theorem prefixThenTarget_prefix
    [Countable α]
    {n : ℕ} (xs : Fin n → α) (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite)
    (k : Fin n) :
    prefixThenTarget xs L hrest k = xs k :=
  GenLimit.Support.prefixThenTarget_prefix xs L hrest k

theorem prefixThenTarget_injective
    [Countable α]
    {n : ℕ} {xs : Fin n → α} (hxs : Function.Injective xs)
    (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    Function.Injective (prefixThenTarget xs L hrest) :=
  GenLimit.Support.prefixThenTarget_injective hxs L hrest

theorem range_prefixThenTarget_eq_prefix_union
    [Countable α]
    {n : ℕ} (xs : Fin n → α) (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    Set.range (prefixThenTarget xs L hrest) =
      (sequenceSample xs : Set α) ∪ L :=
  GenLimit.Support.range_prefixThenTarget_eq_prefix_union xs L hrest

theorem prefixThenTarget_range
    [Countable α]
    {n : ℕ} {xs : Fin n → α}
    (L : Set α) (hxsL : ∀ i, xs i ∈ L)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    Set.range (prefixThenTarget xs L hrest) = L :=
  GenLimit.Support.prefixThenTarget_range L hxsL hrest

theorem prefixThenTarget_sample
    [Countable α]
    {n : ℕ} (xs : Fin n → α) (L : Set α)
    (hrest : (L \ (sequenceSample xs : Set α)).Infinite) :
    sample (prefixThenTarget xs L hrest) n = sequenceSample xs :=
  GenLimit.Support.prefixThenTarget_sample xs L hrest

end GenLimit.NoiseLossFeedback
