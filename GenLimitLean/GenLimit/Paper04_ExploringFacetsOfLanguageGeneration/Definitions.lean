import GenLimit.Core.ClassGeneration
import GenLimit.Core.ClosureDimension
import GenLimit.Support.Presentations

/-!
# Charikar--Pabbaraju: source-facing generation definitions

Definitions 2 and 3 quantify over exact presentations and require correctness
whenever the current sample has at least the stated size.  These are kept
distinct from the standard `GenLimit.Generic` predicates, which quantify over
all positive streams and use an exact-size crossing followed by persistence.
The equivalences below make the relationship explicit instead of identifying
the two definitions by abbreviation.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-- Definition 2's algorithm predicate for an indexed collection. -/
def IsNonuniformGenerator
    (gen : Generator α) (C : LanguageFamily α) : Prop :=
  ∀ i, ∃ d : ℕ, ∀ stream : Stream α,
    Presents stream (C i) →
    ∀ t, d ≤ (sample stream t).card → CorrectAt gen (C i) stream t

def NonuniformlyGeneratable (C : LanguageFamily α) : Prop :=
  ∃ gen : Generator α, IsNonuniformGenerator gen C

/-- Definition 3's algorithm predicate for an indexed collection. -/
def IsUniformGenerator
    (gen : Generator α) (C : LanguageFamily α) : Prop :=
  ∃ d : ℕ, ∀ i, ∀ stream : Stream α,
    Presents stream (C i) →
    ∀ t, d ≤ (sample stream t).card → CorrectAt gen (C i) stream t

def UniformlyGeneratable (C : LanguageFamily α) : Prop :=
  ∃ gen : Generator α, IsUniformGenerator gen C

/-- Definition 4 at finite level `d`, reusing Core's closure witness. -/
abbrev ClosureDimensionAtLeast
    (C : LanguageClass α) (d : ℕ) : Prop :=
  ∃ S : Finset α, d ≤ S.card ∧ IsClosureWitness C S

abbrev IndexedClosureDimensionAtLeast
    (C : LanguageFamily α) (d : ℕ) : Prop :=
  ClosureDimensionAtLeast (Set.range C) d

abbrev HasInfiniteIndexedClosureDimension
    (C : LanguageFamily α) : Prop :=
  ∀ d, IndexedClosureDimensionAtLeast C d

theorem generic_nonuniform_implies_source
    {gen : Generator α} {C : LanguageFamily α}
    (h : GenLimit.Generic.IsNonuniformGenerator gen (Set.range C)) :
    IsNonuniformGenerator gen C := by
  intro i
  obtain ⟨d, hd⟩ := h (C i) ⟨i, rfl⟩
  refine ⟨d, ?_⟩
  intro stream hP t hdt
  obtain ⟨r, hrt, hr⟩ := exists_sample_card_eq_of_le hdt
  exact hd stream (streamIn_of_presents hP) r hr t hrt

theorem source_nonuniform_implies_generic [Countable α]
    {gen : Generator α} {C : LanguageFamily α}
    (hNonempty : ∀ i, (C i).Nonempty)
    (h : IsNonuniformGenerator gen C) :
    GenLimit.Generic.IsNonuniformGenerator gen (Set.range C) := by
  rintro L ⟨i, rfl⟩
  obtain ⟨d, hd⟩ := h i
  refine ⟨d, ?_⟩
  intro stream hstream t ht s hts
  let xs : Fin s → α := fun j ↦ stream j
  have hxs : ∀ j, xs j ∈ C i := fun j ↦ hstream ⟨j, rfl⟩
  let completed := GenLimit.Support.prefixThenPresentation xs (C i) hxs (hNonempty i)
  have hP : Presents completed (C i) :=
    GenLimit.Support.prefixThenPresentation_presents xs (C i) hxs (hNonempty i)
  have hsamples : sample completed s = sample stream s := by
    apply sample_eq_of_eq_on_prefix
    intro n hn
    exact GenLimit.Support.prefixThenPresentation_apply_of_lt
      xs (C i) hxs (hNonempty i) hn
  have hcard : d ≤ (sample completed s).card := by
    rw [hsamples]
    rw [← ht]
    exact Finset.card_le_card (sample_mono hts)
  have hcorrect := hd completed hP s hcard
  have hprefix : (fun j : Fin s ↦ completed j) =
      (fun j : Fin s ↦ stream j) := by
    funext j
    exact GenLimit.Support.prefixThenPresentation_apply_of_lt
      xs (C i) hxs (hNonempty i) j.isLt
  simpa only [CorrectAt, output, hsamples, hprefix] using hcorrect

theorem nonuniformlyGeneratable_iff_generic [Countable α]
    {C : LanguageFamily α} (hNonempty : ∀ i, (C i).Nonempty) :
    NonuniformlyGeneratable C ↔
      GenLimit.Generic.NonuniformlyGeneratable (Set.range C) := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact ⟨gen, source_nonuniform_implies_generic hNonempty hgen⟩
  · rintro ⟨gen, hgen⟩
    exact ⟨gen, generic_nonuniform_implies_source hgen⟩

theorem generic_uniform_implies_source
    {gen : Generator α} {C : LanguageFamily α} {d : ℕ}
    (h : GenLimit.Generic.IsUniformGeneratorAt gen (Set.range C) d) :
    IsUniformGenerator gen C := by
  refine ⟨d, ?_⟩
  intro i stream hP t hdt
  obtain ⟨r, hrt, hr⟩ := exists_sample_card_eq_of_le hdt
  exact h (C i) ⟨i, rfl⟩ stream (streamIn_of_presents hP) r hr t hrt

theorem source_uniform_implies_generic [Countable α]
    {gen : Generator α} {C : LanguageFamily α}
    (hNonempty : ∀ i, (C i).Nonempty)
    (h : IsUniformGenerator gen C) :
    ∃ d, GenLimit.Generic.IsUniformGeneratorAt gen (Set.range C) d := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, ?_⟩
  rintro L ⟨i, rfl⟩ stream hstream t ht s hts
  let xs : Fin s → α := fun j ↦ stream j
  have hxs : ∀ j, xs j ∈ C i := fun j ↦ hstream ⟨j, rfl⟩
  let completed := GenLimit.Support.prefixThenPresentation xs (C i) hxs (hNonempty i)
  have hP : Presents completed (C i) :=
    GenLimit.Support.prefixThenPresentation_presents xs (C i) hxs (hNonempty i)
  have hsamples : sample completed s = sample stream s := by
    apply sample_eq_of_eq_on_prefix
    intro n hn
    exact GenLimit.Support.prefixThenPresentation_apply_of_lt
      xs (C i) hxs (hNonempty i) hn
  have hcard : d ≤ (sample completed s).card := by
    rw [hsamples, ← ht]
    exact Finset.card_le_card (sample_mono hts)
  have hcorrect := hd i completed hP s hcard
  have hprefix : (fun j : Fin s ↦ completed j) =
      (fun j : Fin s ↦ stream j) := by
    funext j
    exact GenLimit.Support.prefixThenPresentation_apply_of_lt
      xs (C i) hxs (hNonempty i) j.isLt
  simpa only [CorrectAt, output, hsamples, hprefix] using hcorrect

theorem uniformlyGeneratable_iff_generic [Countable α]
    {C : LanguageFamily α} (hNonempty : ∀ i, (C i).Nonempty) :
    UniformlyGeneratable C ↔
      GenLimit.Generic.UniformlyGeneratable (Set.range C) := by
  constructor
  · rintro ⟨gen, hgen⟩
    obtain ⟨d, hd⟩ := source_uniform_implies_generic hNonempty hgen
    exact ⟨gen, d, hd⟩
  · rintro ⟨gen, d, hgen⟩
    exact ⟨gen, generic_uniform_implies_source hgen⟩

end GenLimit.CharikarPabbaraju
