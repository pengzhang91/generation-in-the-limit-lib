import GenLimit.Core.ClassGeneration
import GenLimit.Support.Presentations

/-!
# Renaming an example universe

Paper witnesses are often presented over different countably infinite
universes.  These elementary constructions transport languages, streams, and
generators along an equivalence without changing their semantic behavior.
-/

namespace GenLimit.Support

open GenLimit.Generic

def renameLanguage (e : α ≃ β) (L : Language α) : Language β :=
  e '' L

def renameLanguageClass
    (e : α ≃ β) (C : LanguageClass α) : LanguageClass β :=
  renameLanguage e '' C

def renameStream (e : α ≃ β) (stream : Stream α) : Stream β :=
  fun n => e (stream n)

def renameGenerator (e : α ≃ β) (gen : Generator α) : Generator β :=
  fun t xs => e (gen t (fun i => e.symm (xs i)))

@[simp] theorem mem_renameLanguage_iff
    (e : α ≃ β) (L : Language α) (x : α) :
    e x ∈ renameLanguage e L ↔ x ∈ L := by
  simp [renameLanguage]

@[simp] theorem renameLanguage_symm
    (e : α ≃ β) (L : Language α) :
    renameLanguage e.symm (renameLanguage e L) = L := by
  ext x
  simp [renameLanguage]

@[simp] theorem renameLanguage_apply_symm
    (e : α ≃ β) (L : Language β) :
    renameLanguage e (renameLanguage e.symm L) = L := by
  simpa using renameLanguage_symm e.symm L

@[simp] theorem renameLanguageClass_symm
    (e : α ≃ β) (C : LanguageClass α) :
    renameLanguageClass e.symm (renameLanguageClass e C) = C := by
  ext L
  constructor
  · rintro ⟨K, ⟨J, hJC, rfl⟩, rfl⟩
    simpa using hJC
  · intro hLC
    refine ⟨renameLanguage e L, ⟨L, hLC, rfl⟩, ?_⟩
    simp

@[simp] theorem renameLanguageClass_apply_symm
    (e : α ≃ β) (C : LanguageClass β) :
    renameLanguageClass e (renameLanguageClass e.symm C) = C := by
  simpa using renameLanguageClass_symm e.symm C

theorem renameLanguageClass_union
    (e : α ≃ β) (C D : LanguageClass α) :
    renameLanguageClass e (C ∪ D) =
      renameLanguageClass e C ∪ renameLanguageClass e D := by
  ext L
  constructor
  · rintro ⟨K, hK, rfl⟩
    rcases hK with hKC | hKD
    · exact Or.inl ⟨K, hKC, rfl⟩
    · exact Or.inr ⟨K, hKD, rfl⟩
  · rintro (⟨K, hKC, rfl⟩ | ⟨K, hKD, rfl⟩)
    · exact ⟨K, Or.inl hKC, rfl⟩
    · exact ⟨K, Or.inr hKD, rfl⟩

theorem renameLanguageClass_countable_iff
    (e : α ≃ β) (C : LanguageClass α) :
    (renameLanguageClass e C).Countable ↔ C.Countable := by
  constructor
  · intro h
    have himage := h.image (renameLanguage e.symm)
    change
      (renameLanguageClass e.symm
        (renameLanguageClass e C)).Countable at himage
    simpa using himage
  · intro h
    exact h.image (renameLanguage e)

theorem renameLanguageClass_uus_iff
    (e : α ≃ β) (C : LanguageClass α) :
    UUS (renameLanguageClass e C) ↔ UUS C := by
  constructor
  · intro h L hLC
    have hrenamed :
        (renameLanguage e L).Infinite :=
      h (renameLanguage e L) ⟨L, hLC, rfl⟩
    have himage := hrenamed.image
      (Set.injOn_of_injective e.symm.injective)
    change
      (renameLanguage e.symm (renameLanguage e L)).Infinite at himage
    simpa using himage
  · intro h K hKC
    obtain ⟨L, hLC, rfl⟩ := hKC
    exact (h L hLC).image
      (Set.injOn_of_injective e.injective)

theorem renameStream_injective
    (e : α ≃ β) {stream : Stream α}
    (h : Function.Injective stream) :
    Function.Injective (renameStream e stream) :=
  e.injective.comp h

@[simp] theorem renameStream_symm
    (e : α ≃ β) (stream : Stream α) :
    renameStream e.symm (renameStream e stream) = stream := by
  funext n
  simp [renameStream]

@[simp] theorem renameStream_apply_symm
    (e : α ≃ β) (stream : Stream β) :
    renameStream e (renameStream e.symm stream) = stream := by
  funext n
  simp [renameStream]

theorem range_renameStream
    (e : α ≃ β) (stream : Stream α) :
    Set.range (renameStream e stream) =
      renameLanguage e (Set.range stream) := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨stream n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

theorem presents_renameStream
    (e : α ≃ β) {stream : Stream α} {L : Language α}
    (h : Presents stream L) :
    Presents (renameStream e stream) (renameLanguage e L) := by
  rw [Presents, range_renameStream, h]

@[simp] theorem output_rename
    (e : α ≃ β) (gen : Generator α) (stream : Stream α) (t : ℕ) :
    output (renameGenerator e gen) (renameStream e stream) t =
      e (output gen stream t) := by
  simp [output, renameGenerator, renameStream]

theorem correctAt_rename_iff
    (e : α ≃ β) (gen : Generator α) (L : Language α)
    (stream : Stream α) (t : ℕ) :
    CorrectAt (renameGenerator e gen) (renameLanguage e L)
        (renameStream e stream) t ↔
      CorrectAt gen L stream t := by
  constructor
  · rintro ⟨hmem, hfresh⟩
    constructor
    · simpa only [output_rename, mem_renameLanguage_iff] using hmem
    · intro hseen
      apply hfresh
      rw [mem_sample_iff] at hseen ⊢
      obtain ⟨s, hst, hs⟩ := hseen
      exact ⟨s, hst, by simpa [renameStream, output_rename] using congrArg e hs⟩
  · rintro ⟨hmem, hfresh⟩
    constructor
    · simpa only [output_rename, mem_renameLanguage_iff] using hmem
    · intro hseen
      apply hfresh
      rw [mem_sample_iff] at hseen ⊢
      obtain ⟨s, hst, hs⟩ := hseen
      refine ⟨s, hst, ?_⟩
      apply e.injective
      simpa [renameStream, output_rename] using hs

end GenLimit.Support
