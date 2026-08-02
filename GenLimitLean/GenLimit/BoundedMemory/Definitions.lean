import GenLimit.Core.GenericGeneration
import Mathlib.Data.Set.Countable

/-!
# Bounded-memory language generation: the memoryless set model

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1.

This file formalizes the set-based, fully memoryless model used in
Definitions 3--4 and Section 3 of the pinned source.  On round `t`, the
generator sees only the current example `stream t` and returns an infinite
set.  The set output is valid when it is contained in the target language.
-/

namespace GenLimit.BoundedMemory

/-- A set-based memoryless generator.  The source's codomain consists only
of infinite sets; we keep the raw function type and put infinitude in the
round-validity predicate.  This avoids an irrelevant choice of an infinite
set at points that occur in no language of the collection. -/
abbrev MemorylessSetGenerator (α : Type*) := α → Set α

/-- Validity of the set output after seeing the current example. -/
def ValidSetOutput
    (G : MemorylessSetGenerator α) (K : Set α) (x : α) : Prop :=
  (G x).Infinite ∧ G x ⊆ K

/-- Exact Section 3 success criterion under arbitrary exact presentations.

The output at round `t` is based on `stream t`, rather than on the prefix
strictly before `t`; this is the paper's memoryless timing convention. -/
def IsArbitraryPresentationMemorylessGenerator
    (G : MemorylessSetGenerator α) (H : Set (Set α)) : Prop :=
  ∀ K, K ∈ H → ∀ stream : ℕ → α,
    GenLimit.Generic.Presents stream K →
      ∃ T, ∀ t, T ≤ t → ValidSetOutput G K (stream t)

/-- Memoryless set-based generatability under arbitrary repetitions. -/
def ArbitraryPresentationMemorylessGeneratable
    (H : Set (Set α)) : Prop :=
  ∃ G : MemorylessSetGenerator α,
    IsArbitraryPresentationMemorylessGenerator G H

/-- Definition 4: each point occurs only finitely often. -/
def FinitelyRepeating (stream : ℕ → α) : Prop :=
  ∀ x, {t : ℕ | stream t = x}.Finite

/-- Success of a memoryless set generator when the adversary is restricted
to finitely repeating exact presentations. -/
def IsFinitelyRepeatingMemorylessGenerator
    (G : MemorylessSetGenerator α) (H : Set (Set α)) : Prop :=
  ∀ K, K ∈ H → ∀ stream : ℕ → α,
    GenLimit.Generic.Presents stream K →
      FinitelyRepeating stream →
        ∃ T, ∀ t, T ≤ t → ValidSetOutput G K (stream t)

/-- Memoryless set-based generatability under finitely repeating exact
presentations. -/
def FinitelyRepeatingMemorylessGeneratable
    (H : Set (Set α)) : Prop :=
  ∃ G : MemorylessSetGenerator α,
    IsFinitelyRepeatingMemorylessGenerator G H

/-- The intersection of all members of `H` containing the single observed
example `x`.  This is the source's `I_x`. -/
def singletonCore (H : Set (Set α)) (x : α) : Set α :=
  {y | ∀ K, K ∈ H → x ∈ K → y ∈ K}

theorem singletonCore_subset
    {H : Set (Set α)} {x : α} {K : Set α}
    (hK : K ∈ H) (hx : x ∈ K) :
    singletonCore H x ⊆ K := by
  intro y hy
  exact hy K hK hx

/-- The source condition in Theorem 3.1: every example that occurs in some
language certifies an infinite common intersection. -/
def InfiniteSingletonCores (H : Set (Set α)) : Prop :=
  ∀ x, x ∈ ⋃₀ H → (singletonCore H x).Infinite

end GenLimit.BoundedMemory
