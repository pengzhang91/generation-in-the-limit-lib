import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Nonuniform
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.NoFeedbackDimension
import GenLimit.Dependency_Angluin1980.Definitions

/-!
# Charikar--Pabbaraju: preliminary generation definitions

This file packages Definitions 1--4 in the paper's namespace. Definitions 2
and 3 use an indexed family because the source fixes a countable enumeration
of the collection. Definition 4 is represented level by level, consistently
with Proposition 7.1. For Definition 1 on the encoded universe `ℕ`, the
effective list-machine interface records the source's computability
requirement instead of silently replacing it by an arbitrary Lean function.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## Definition 1: generation in the limit via a computable function -/

/-- A source-level generating machine on finite encoded histories. -/
abbrev EffectiveLimitGenerator := List ℕ → ℕ

def effectiveLimitOutput
    (G : EffectiveLimitGenerator)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) : ℕ :=
  G (GenLimit.Angluin.streamPrefix stream t)

/-- Definition 1 on the encoded word universe. The machine is one fixed
computable function and must eventually output a fresh target word on every
exact presentation of every indexed target. -/
def IsEffectiveLimitGenerator
    (G : EffectiveLimitGenerator)
    (C : GenLimit.Generic.LanguageFamily ℕ) : Prop :=
  Computable G ∧
    ∀ i, ∀ stream : GenLimit.Generic.Stream ℕ,
      GenLimit.Generic.Presents stream (C i) →
      ∃ T, ∀ t, T ≤ t →
        effectiveLimitOutput G stream t ∈
          C i \ (↑(GenLimit.Generic.sample stream t) : Set ℕ)

def EffectivelyGeneratableInLimit
    (C : GenLimit.Generic.LanguageFamily ℕ) : Prop :=
  ∃ G : EffectiveLimitGenerator, IsEffectiveLimitGenerator G C

/-- Forget the computability certificate and view a list machine through the
repository's dependent finite-history generator API. -/
def effectiveLimitGeneratorAsGeneric
    (G : EffectiveLimitGenerator) : Generator ℕ :=
  fun _t xs => G (List.ofFn xs)

theorem effectiveLimitGeneratorAsGeneric_output
    (G : EffectiveLimitGenerator)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    Generic.output (effectiveLimitGeneratorAsGeneric G) stream t =
      effectiveLimitOutput G stream t :=
  rfl

theorem effectiveLimitGenerator_semantic_bridge
    {G : EffectiveLimitGenerator}
    {C : GenLimit.Generic.LanguageFamily ℕ}
    (hG : IsEffectiveLimitGenerator G C) :
    GenLimit.LiRamanTewari.IsLimitGenerator
      (effectiveLimitGeneratorAsGeneric G) (Set.range C) := by
  rintro L ⟨i, rfl⟩ stream hP
  obtain ⟨T, hT⟩ := hG.2 i stream hP
  refine ⟨T, ?_⟩
  intro t ht
  simpa [Generic.CorrectAt, effectiveLimitGeneratorAsGeneric_output] using
    hT t ht

/-! ## Definitions 2--3: non-uniform and uniform generation -/

/-- Definition 2 as a class property. The paper-facing algorithm predicate
`IsNonuniformGenerator` is defined in `Nonuniform.lean`. -/
def NonuniformlyGeneratable {α : Type*}
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, IsNonuniformGenerator gen C

/-- Definition 3's uniform algorithm predicate, with one threshold shared by
all indexed targets and all their exact presentations. -/
def IsUniformGenerator {α : Type*}
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ d : ℕ, ∀ i, ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream (C i) →
    ∀ t, d ≤ (GenLimit.Generic.sample stream t).card →
      GenLimit.Generic.CorrectAt gen (C i) stream t

def UniformlyGeneratable {α : Type*}
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, IsUniformGenerator gen C

/-! ## Definition 4: closure dimension -/

/-- Definition 4 for an indexed collection, at finite level `d`. The
underlying `ClosureDimensionAtLeast` predicate is also used in Proposition
7.1 and says that some consistent finite sample of size at least `d` has a
finite common intersection. -/
def IndexedClosureDimensionAtLeast {α : Type*}
    (C : GenLimit.Generic.LanguageFamily α) (d : ℕ) : Prop :=
  ClosureDimensionAtLeast (Set.range C) d

def HasInfiniteIndexedClosureDimension {α : Type*}
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ d, IndexedClosureDimensionAtLeast C d

theorem indexedClosureDimensionAtLeast_iff
    {α : Type*} (C : GenLimit.Generic.LanguageFamily α) (d : ℕ) :
    IndexedClosureDimensionAtLeast C d ↔
      ∃ S : Finset α, d ≤ S.card ∧
        GenLimit.LiRamanTewari.IsClosureWitness (Set.range C) S :=
  Iff.rfl

end GenLimit.CharikarPabbaraju
