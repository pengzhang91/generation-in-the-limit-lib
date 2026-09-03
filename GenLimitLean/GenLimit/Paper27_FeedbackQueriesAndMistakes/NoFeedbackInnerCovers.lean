import GenLimit.Paper02_LearningTheory.FiniteConeCover
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization
import GenLimit.Paper27_FeedbackQueriesAndMistakes.Definitions
import GenLimit.Support.Fresh

/-!
# P27 Theorem 3.10: independent inner-cover results

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*Language Generation with Feedback: Queries and Mistakes*, ICML 2026,
Theorem 3.10 and Appendix Theorems A.9, A.12, and A.13.

This module formalizes the three parts of Theorem 3.10 which do not depend on
the unrestricted element-to-set direction of Theorem 3.9:

* a finite inner cover suffices for generation in the limit (A.9);
* a generatable class with a countable inner cover exists (A.12);
* a generatable class with no finite inner cover exists (A.13).

Theorem A.10 and the source proof of Theorem A.11 remain outside this module:
they use the unrestricted Theorem 3.9 conversion, whose Appendix Lemma A.8
step is deliberately deferred in this development.

The A.9 proof reuses P02's finite union of infinite upward cones.  The A.12
proof reuses P02's theorem that countable UUS classes are nonuniformly
generatable, followed by Core's nonuniform-to-limit implication.  A.13 keeps
the source's explicit vertical-fiber family on `ℕ × ℕ`.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-! ## Finite inner covers -/

/-- Source-facing finite analogue of `CountableInnerCover`: finitely many
infinite sets, one of which is contained in every target language. -/
structure FiniteInnerCover
    (targets : GenLimit.Generic.LanguageClass α) where
  size : ℕ
  cover : Fin size → Set α
  infinite_cover : ∀ i, (cover i).Infinite
  contained : ∀ L, L ∈ targets → ∃ i, cover i ⊆ L

/-- A language class has an inner cover of finite size. -/
def HasFiniteInnerCover
    (targets : GenLimit.Generic.LanguageClass α) : Prop :=
  Nonempty (FiniteInnerCover targets)

/-- Appendix Theorem A.9: a finite inner cover suffices for no-feedback
generation in the limit.

Each target containing `cover i` belongs to the upward cone over that cover
member.  P02's finite-cone result generates the union of those cones, and the
same generator works on the original subclass. -/
theorem theorem_A_9
    [Nonempty α] [Countable α]
    {targets : GenLimit.Generic.LanguageClass α}
    (hinner : HasFiniteInnerCover targets) :
    GeneratableInLimit targets := by
  let inner := Nonempty.some hinner
  obtain ⟨gen, hgen⟩ :=
    GenLimit.LiRamanTewari.finite_union_of_infinite_upwardCones_generatable_in_limit
      inner.cover inner.infinite_cover
  refine ⟨gen, ?_⟩
  intro L hL stream hpresents
  apply hgen L
  · apply Set.mem_iUnion.mpr
    obtain ⟨i, hi⟩ := inner.contained L hL
    exact ⟨i, hi⟩
  · exact hpresents

/-! ## Countable classes: the reusable A.12 argument -/

/-- Every countable class of infinite languages over a countably infinite
universe is both generatable in the limit and equipped with a countable inner
cover.

This strengthens the existential statement of Appendix Theorem A.12 while
following its proof: countable-class generation is reused from P02, and an
enumeration of the class supplies the inner cover. -/
theorem countableClass_generatable_and_hasCountableInnerCover
    [Infinite α] [Countable α]
    {targets : GenLimit.Generic.LanguageClass α}
    (hUUS : UUS targets) (hcountable : targets.Countable) :
    GeneratableInLimit targets ∧ HasCountableInnerCover targets := by
  constructor
  · exact nonuniform_implies_limit hUUS
      (GenLimit.LiRamanTewari.countable_classes_are_nonuniformly_generatable
        hUUS hcountable)
  · obtain ⟨enumerate, henumerate⟩ :=
      Set.countable_iff_exists_subset_range.mp hcountable
    refine ⟨CountableInnerCover.ofCountableOutputs enumerate ?_⟩
    intro L hL
    obtain ⟨i, rfl⟩ := henumerate hL
    exact ⟨i, hUUS _ hL, Set.Subset.rfl⟩

/-- Appendix Theorem A.12: there exists a no-feedback-generatable class with
a countable inner cover. -/
theorem theorem_A_12 :
    ∃ targets : GenLimit.Generic.LanguageClass ℕ,
      UUS targets ∧ GeneratableInLimit targets ∧
        HasCountableInnerCover targets := by
  let targets : GenLimit.Generic.LanguageClass ℕ := {Set.univ}
  have hUUS : UUS targets := by
    intro L hL
    have hLuniv : L = Set.univ := Set.mem_singleton_iff.mp hL
    subst L
    exact Set.infinite_univ
  have hcountable : targets.Countable := Set.countable_singleton Set.univ
  obtain ⟨hgen, hinner⟩ :=
    countableClass_generatable_and_hasCountableInnerCover
      hUUS hcountable
  exact ⟨targets, hUUS, hgen, hinner⟩

/-! ## Appendix Theorem A.13: disjoint vertical fibers -/

/-- The source's `i`-th vertical fiber in `ℕ × ℕ`. -/
def verticalLanguage (i : ℕ) : GenLimit.Generic.Language (ℕ × ℕ) :=
  {x | x.1 = i}

/-- The countable collection of all vertical fibers. -/
def verticalLanguageClass :
    GenLimit.Generic.LanguageClass (ℕ × ℕ) :=
  Set.range verticalLanguage

@[simp] theorem mem_verticalLanguage_iff
    {i : ℕ} {x : ℕ × ℕ} :
    x ∈ verticalLanguage i ↔ x.1 = i :=
  Iff.rfl

theorem verticalLanguage_infinite (i : ℕ) :
    (verticalLanguage i).Infinite := by
  let embed : ℕ → ℕ × ℕ := fun j => (i, j)
  have hinjective : Function.Injective embed := by
    intro a b hab
    exact congrArg Prod.snd hab
  apply (Set.infinite_range_of_injective hinjective).mono
  rintro _ ⟨j, rfl⟩
  rfl

theorem verticalLanguageClass_uus : UUS verticalLanguageClass := by
  intro L hL
  obtain ⟨i, rfl⟩ := hL
  exact verticalLanguage_infinite i

/-- The A.13 generator reads the first observed pair to identify its vertical
fiber, then chooses a fresh point in that fiber.  Its value on the empty
history is irrelevant to eventual correctness. -/
noncomputable def verticalFiberGenerator : Generator (ℕ × ℕ) := by
  classical
  intro t samples
  cases t with
  | zero => exact (0, 0)
  | succ t =>
      exact GenLimit.Support.freshFromInfinite
        (verticalLanguage (samples 0).1)
        (verticalLanguage_infinite (samples 0).1)
        (sequenceSample samples)

theorem verticalFiberGenerator_succ
    (t : ℕ) (samples : Fin (t + 1) → ℕ × ℕ) :
    verticalFiberGenerator (t + 1) samples =
      GenLimit.Support.freshFromInfinite
        (verticalLanguage (samples 0).1)
        (verticalLanguage_infinite (samples 0).1)
        (sequenceSample samples) := by
  simp [verticalFiberGenerator]

theorem verticalLanguageClass_generatableInLimit :
    GeneratableInLimit verticalLanguageClass := by
  refine ⟨verticalFiberGenerator, ?_⟩
  intro L hL stream hpresents
  obtain ⟨i, rfl⟩ := hL
  have hstream : StreamIn stream (verticalLanguage i) :=
    streamIn_of_presents hpresents
  have hfirst : stream 0 ∈ verticalLanguage i :=
    hstream ⟨0, rfl⟩
  have hfirstCoordinate : (stream 0).1 = i := hfirst
  refine ⟨1, ?_⟩
  intro t ht
  cases t with
  | zero => omega
  | succ t =>
      constructor
      · change verticalFiberGenerator (t + 1) (fun j => stream j) ∈
          verticalLanguage i
        rw [verticalFiberGenerator_succ]
        have hmem := GenLimit.Support.freshFromInfinite_mem
          (verticalLanguage (stream 0).1)
          (verticalLanguage_infinite (stream 0).1)
          (sequenceSample (fun j : Fin (t + 1) => stream j))
        simpa [verticalLanguage, hfirstCoordinate] using hmem
      · change verticalFiberGenerator (t + 1) (fun j => stream j) ∉
          GenLimit.Generic.sample (α := ℕ × ℕ) stream (t + 1)
        rw [verticalFiberGenerator_succ,
          ← GenLimit.Generic.sequenceSample_prefix stream (t + 1)]
        exact GenLimit.Support.freshFromInfinite_not_mem
          (verticalLanguage (stream 0).1)
          (verticalLanguage_infinite (stream 0).1)
          (sequenceSample (fun j : Fin (t + 1) => stream j))

/-- No finite family of infinite sets can be an inner cover of all pairwise
disjoint vertical fibers. -/
theorem verticalLanguageClass_hasNoFiniteInnerCover :
    ¬HasFiniteInnerCover verticalLanguageClass := by
  classical
  rintro ⟨inner⟩
  let representative : Fin inner.size → ℕ × ℕ := fun k =>
    Classical.choose (inner.infinite_cover k).nonempty
  have representative_mem (k : Fin inner.size) :
      representative k ∈ inner.cover k :=
    Classical.choose_spec (inner.infinite_cover k).nonempty
  let representedCoordinates : Finset ℕ :=
    Finset.univ.image (fun k => (representative k).1)
  let missingCoordinate : ℕ :=
    GenLimit.Support.freshFromInfinite Set.univ Set.infinite_univ
      representedCoordinates
  have hmissing : missingCoordinate ∉ representedCoordinates :=
    GenLimit.Support.freshFromInfinite_not_mem
      Set.univ Set.infinite_univ representedCoordinates
  have htarget : verticalLanguage missingCoordinate ∈ verticalLanguageClass :=
    ⟨missingCoordinate, rfl⟩
  obtain ⟨k, hk⟩ := inner.contained _ htarget
  have hcoordinate : (representative k).1 = missingCoordinate :=
    hk (representative_mem k)
  have hrepresented : (representative k).1 ∈ representedCoordinates := by
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  rw [hcoordinate] at hrepresented
  exact hmissing hrepresented

/-- Appendix Theorem A.13: some no-feedback-generatable language class has
no finite inner cover. -/
theorem theorem_A_13 :
    ∃ targets : GenLimit.Generic.LanguageClass (ℕ × ℕ),
      UUS targets ∧ GeneratableInLimit targets ∧
        ¬HasFiniteInnerCover targets :=
  ⟨verticalLanguageClass, verticalLanguageClass_uus,
    verticalLanguageClass_generatableInLimit,
    verticalLanguageClass_hasNoFiniteInnerCover⟩

end GenLimit.FeedbackQueries
