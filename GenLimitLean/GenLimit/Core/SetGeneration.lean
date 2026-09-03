import GenLimit.Core.ClassGeneration

/-!
# Generic set-valued generation

Paper-independent semantic vocabulary for generators which return an infinite
set after each finite positive history.  This is the set-valued analogue of
`Generator`, `CorrectAt`, and `GeneratableInLimit` from the element-valued
Core API.

The definitions are extensional and may be used by noncomputable generators.
They make no machine-level, running-time, or effective-enumerability claim.
-/

namespace GenLimit.Generic

/-- A set-valued generator is a function from each finite positive history to
a set of proposed fresh examples. -/
abbrev SetGenerator (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → Set α

/-- Run a set-valued generator on the prefix strictly before time `t`. -/
def setOutput
    (gen : SetGenerator α) (stream : Stream α) (t : ℕ) : Set α :=
  gen t (fun i => stream i)

/-- The source-level codomain condition used by set-based generation: every
output is infinite, including outputs on histories which do not occur along a
particular run. -/
def IsInfiniteSetGenerator (gen : SetGenerator α) : Prop :=
  ∀ t samples, (gen t samples).Infinite

/-- Pointwise correctness for a set output: it is contained in the target and
disjoint from every positive example observed so far. -/
def SetCorrectAt
    (gen : SetGenerator α) (L : Language α)
    (stream : Stream α) (t : ℕ) : Prop :=
  setOutput gen stream t ⊆ L ∧
    Disjoint (setOutput gen stream t) (↑(sample stream t) : Set α)

/-- Pointwise correctness together with infinitude of the current output. -/
def InfiniteSetCorrectAt
    (gen : SetGenerator α) (L : Language α)
    (stream : Stream α) (t : ℕ) : Prop :=
  SetCorrectAt gen L stream t ∧ (setOutput gen stream t).Infinite

/-- Eventual set generation on one fixed target and presentation. -/
def GeneratesSetInLimitOn
    (gen : SetGenerator α) (L : Language α) (stream : Stream α) : Prop :=
  ∃ T, ∀ t, T ≤ t → SetCorrectAt gen L stream t

/-- Eventual set generation with the global infinite-output requirement. -/
def GeneratesInfiniteSetInLimitOn
    (gen : SetGenerator α) (L : Language α) (stream : Stream α) : Prop :=
  IsInfiniteSetGenerator gen ∧ GeneratesSetInLimitOn gen L stream

theorem InfiniteSetCorrectAt.setCorrectAt
    {gen : SetGenerator α} {L : Language α}
    {stream : Stream α} {t : ℕ}
    (h : InfiniteSetCorrectAt gen L stream t) :
    SetCorrectAt gen L stream t :=
  h.1

theorem InfiniteSetCorrectAt.output_infinite
    {gen : SetGenerator α} {L : Language α}
    {stream : Stream α} {t : ℕ}
    (h : InfiniteSetCorrectAt gen L stream t) :
    (setOutput gen stream t).Infinite :=
  h.2

theorem GeneratesInfiniteSetInLimitOn.generatesSetInLimitOn
    {gen : SetGenerator α} {L : Language α} {stream : Stream α}
    (h : GeneratesInfiniteSetInLimitOn gen L stream) :
    GeneratesSetInLimitOn gen L stream :=
  h.2

theorem GeneratesInfiniteSetInLimitOn.output_infinite
    {gen : SetGenerator α} {L : Language α} {stream : Stream α}
    (h : GeneratesInfiniteSetInLimitOn gen L stream) (t : ℕ) :
    (setOutput gen stream t).Infinite :=
  h.1 t (fun i => stream i)

/-- A set-valued generator succeeds on every exact presentation of every
target in `H`. -/
def IsSetLimitGenerator
    (gen : SetGenerator α) (H : LanguageClass α) : Prop :=
  IsInfiniteSetGenerator gen ∧
    ∀ L, L ∈ H → ∀ stream : Stream α, Presents stream L →
      GeneratesSetInLimitOn gen L stream

/-- Set-valued generation in the limit from positive presentations. -/
def SetGeneratableInLimit (H : LanguageClass α) : Prop :=
  ∃ gen : SetGenerator α, IsSetLimitGenerator gen H

/-! ## Projecting a set generator to one element -/

/-- Choose one member of each globally infinite set output. -/
noncomputable def elementGeneratorOfSet
    (gen : SetGenerator α) (hinfinite : IsInfiniteSetGenerator gen) :
    Generator α :=
  fun t samples => Classical.choose (hinfinite t samples).nonempty

theorem elementGeneratorOfSet_mem
    (gen : SetGenerator α) (hinfinite : IsInfiniteSetGenerator gen)
    (t : ℕ) (samples : Fin t → α) :
    elementGeneratorOfSet gen hinfinite t samples ∈ gen t samples :=
  Classical.choose_spec (hinfinite t samples).nonempty

/-- Set-valued generation always implies ordinary element-valued generation.
This is the easy direction of P27 Theorem 3.9, stated in the generic Core API. -/
theorem setGeneratableInLimit_implies_generatableInLimit
    {H : LanguageClass α} (hset : SetGeneratableInLimit H) :
    GeneratableInLimit H := by
  obtain ⟨gen, hinfinite, hgen⟩ := hset
  refine ⟨elementGeneratorOfSet gen hinfinite, ?_⟩
  intro L hL stream hpresents
  obtain ⟨T, hT⟩ := hgen L hL stream hpresents
  refine ⟨T, ?_⟩
  intro t ht
  have hcorrect := hT t ht
  have hmem :
      output (elementGeneratorOfSet gen hinfinite) stream t ∈
        setOutput gen stream t :=
    elementGeneratorOfSet_mem gen hinfinite t (fun i => stream i)
  refine ⟨hcorrect.1 hmem, ?_⟩
  exact fun hsample => Set.disjoint_left.mp hcorrect.2 hmem hsample

end GenLimit.Generic
