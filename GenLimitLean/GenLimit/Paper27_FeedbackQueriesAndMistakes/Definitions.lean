import GenLimit.Core.GenericGeneration
import GenLimit.Core.Text
import Mathlib.Data.Countable.Defs

/-!
# Language generation with feedback: countable inner covers

Source pin:

* Hanneke--Karbasi--Mehrotra--Velegkas,
  *Language Generation with Feedback: Queries and Mistakes*,
  OpenReview forum `jvfXyIcQ8a`, ICML 2026.

This file isolates Definition 4: a countable list of infinite sets such that
every target language contains one member of the list.  No claim about the
paper's machine-level or running-time model is made here.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-- Source-facing name for Core's ordered finite positive history. -/
abbrev streamPrefix (stream : GenLimit.Generic.Stream α) (t : ℕ) : List α :=
  GenLimit.textPrefix stream t

/-- Definition 4 (indexed form): `cover` is a countable inner
cover of `class` when every entry is infinite and every target contains at
least one entry.  Repetitions in the countable list are harmless. -/
structure CountableInnerCover
    (targets : GenLimit.Generic.LanguageClass α) where
  cover : ℕ → Set α
  infinite_cover : ∀ i, (cover i).Infinite
  contained : ∀ L, L ∈ targets → ∃ i, cover i ⊆ L

/-- The paper's countable-inner-cover property. -/
def HasCountableInnerCover
    (targets : GenLimit.Generic.LanguageClass α) : Prop :=
  Nonempty (CountableInnerCover targets)

/-- The class represented by an indexed family. -/
def indexedClass
    (family : GenLimit.Generic.LanguageFamily α) :
    GenLimit.Generic.LanguageClass α :=
  Set.range family

/-- An indexed family of infinite languages is itself a countable inner
cover of its range. -/
def CountableInnerCover.ofIndexedFamily
    (family : GenLimit.Generic.LanguageFamily α)
    (hinfinite : ∀ i, (family i).Infinite) :
    CountableInnerCover (indexedClass family) where
  cover := family
  infinite_cover := hinfinite
  contained := by
    intro L hL
    obtain ⟨i, rfl⟩ := hL
    exact ⟨i, Set.Subset.rfl⟩

/-- Turn any nonempty countable family of infinite sets into the `ℕ`-indexed
form used by `CountableInnerCover`.  This is the common countability step
behind the finite-transcript necessity proofs in this paper. -/
noncomputable def CountableInnerCover.ofCountableFamily
    [Countable ι] [Nonempty ι]
    {targets : GenLimit.Generic.LanguageClass α}
    (family : ι → Set α)
    (hinfinite : ∀ i, (family i).Infinite)
    (hcontained : ∀ L, L ∈ targets → ∃ i, family i ⊆ L) :
    CountableInnerCover targets := by
  classical
  let enumeration : ℕ → ι :=
    Classical.choose (exists_surjective_nat ι)
  have henumeration : Function.Surjective enumeration :=
    Classical.choose_spec (exists_surjective_nat ι)
  exact
    { cover := fun n => family (enumeration n)
      infinite_cover := fun n => hinfinite (enumeration n)
      contained := by
        intro L hL
        obtain ⟨i, hi⟩ := hcontained L hL
        obtain ⟨n, rfl⟩ := henumeration i
        exact ⟨n, hi⟩ }

/-- Countably many possible outputs yield an inner cover whenever every
target has at least one infinite output contained in it.  Non-infinite
outputs are harmlessly totalized to `univ` before applying
`ofCountableFamily`. -/
noncomputable def CountableInnerCover.ofCountableOutputs
    [Countable ι] [Nonempty ι] [Infinite α]
    {targets : GenLimit.Generic.LanguageClass α}
    (output : ι → Set α)
    (hsuccess :
      ∀ L, L ∈ targets →
        ∃ i, (output i).Infinite ∧ output i ⊆ L) :
    CountableInnerCover targets := by
  classical
  let family : ι → Set α := fun i =>
    if (output i).Infinite then output i else Set.univ
  apply CountableInnerCover.ofCountableFamily family
  · intro i
    simp only [family]
    split_ifs with hi
    · exact hi
    · exact Set.infinite_univ
  · intro L hL
    obtain ⟨i, hinfinite, hsubset⟩ := hsuccess L hL
    refine ⟨i, ?_⟩
    simp [family, hinfinite, hsubset]

theorem indexedClass_hasCountableInnerCover
    (family : GenLimit.Generic.LanguageFamily α)
    (hinfinite : ∀ i, (family i).Infinite) :
    HasCountableInnerCover (indexedClass family) :=
  ⟨CountableInnerCover.ofIndexedFamily family hinfinite⟩

/-- Inner-cover existence is downward monotone in the target class. -/
def CountableInnerCover.mono
    {small large : GenLimit.Generic.LanguageClass α}
    (inner : CountableInnerCover large)
    (hsub : small ⊆ large) :
    CountableInnerCover small where
  cover := inner.cover
  infinite_cover := inner.infinite_cover
  contained := by
    intro L hL
    exact inner.contained L (hsub hL)

theorem hasCountableInnerCover_mono
    {small large : GenLimit.Generic.LanguageClass α}
    (hinner : HasCountableInnerCover large)
    (hsub : small ⊆ large) :
    HasCountableInnerCover small :=
  ⟨Nonempty.some hinner |>.mono hsub⟩

/-- A singleton class has a countable inner cover exactly when its language
is infinite (the forward implication is recorded separately below). -/
def singletonCountableInnerCover
    {L : Set α} (hL : L.Infinite) :
    CountableInnerCover ({L} : GenLimit.Generic.LanguageClass α) where
  cover := fun _ => L
  infinite_cover := fun _ => hL
  contained := by
    intro K hK
    have hKL : K = L := Set.mem_singleton_iff.mp hK
    subst K
    exact ⟨0, Set.Subset.rfl⟩

theorem singleton_hasCountableInnerCover
    {L : Set α} (hL : L.Infinite) :
    HasCountableInnerCover ({L} : GenLimit.Generic.LanguageClass α) :=
  ⟨singletonCountableInnerCover hL⟩

theorem infinite_of_singleton_hasCountableInnerCover
    {L : Set α}
    (hinner : HasCountableInnerCover
      ({L} : GenLimit.Generic.LanguageClass α)) :
    L.Infinite := by
  let inner := Nonempty.some hinner
  obtain ⟨i, hi⟩ := inner.contained L (Set.mem_singleton L)
  exact (inner.infinite_cover i).mono hi

theorem singleton_hasCountableInnerCover_iff
    {L : Set α} :
    HasCountableInnerCover
      ({L} : GenLimit.Generic.LanguageClass α) ↔ L.Infinite :=
  ⟨infinite_of_singleton_hasCountableInnerCover,
    singleton_hasCountableInnerCover⟩

end GenLimit.FeedbackQueries
