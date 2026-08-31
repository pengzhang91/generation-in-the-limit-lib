import GenLimit.Core.Basic
import Mathlib.Data.Nat.Find

/-!
# Canonical late occurrences in an exact presentation

An exact presentation may repeat values, so a value itself does not determine
the round at which it should be charged.  This module assigns every value
which occurs at or after a cutoff its least such occurrence.  Distinct values
receive distinct rounds even when the presentation has arbitrary repetitions.

For a presented language, every target value absent from the sample before the
cutoff has such a late occurrence.  This is the form used when classifying the
post-cutoff inputs in Section 3.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration

/-- A value occurs in the presentation at some round no earlier than the
specified cutoff. -/
def OccursAtOrAfter
    (stream : ℕ → ℕ) (cutoff x : ℕ) : Prop :=
  ∃ t, cutoff ≤ t ∧ stream t = x

/-- The least occurrence of `x` at or after `cutoff` when one exists.

The fallback value in the impossible branch makes the definition total; all
substantive lemmas below assume `OccursAtOrAfter`. -/
noncomputable def firstOccurrenceAtOrAfter
    (stream : ℕ → ℕ) (cutoff x : ℕ) : ℕ := by
  classical
  exact if h : OccursAtOrAfter stream cutoff x then Nat.find h else cutoff

theorem firstOccurrenceAtOrAfter_spec
    {stream : ℕ → ℕ} {cutoff x : ℕ}
    (h : OccursAtOrAfter stream cutoff x) :
    cutoff ≤ firstOccurrenceAtOrAfter stream cutoff x ∧
      stream (firstOccurrenceAtOrAfter stream cutoff x) = x := by
  classical
  rw [firstOccurrenceAtOrAfter, dif_pos h]
  exact Nat.find_spec h

theorem firstOccurrenceAtOrAfter_ge
    {stream : ℕ → ℕ} {cutoff x : ℕ}
    (h : OccursAtOrAfter stream cutoff x) :
    cutoff ≤ firstOccurrenceAtOrAfter stream cutoff x :=
  (firstOccurrenceAtOrAfter_spec h).1

theorem stream_firstOccurrenceAtOrAfter
    {stream : ℕ → ℕ} {cutoff x : ℕ}
    (h : OccursAtOrAfter stream cutoff x) :
    stream (firstOccurrenceAtOrAfter stream cutoff x) = x :=
  (firstOccurrenceAtOrAfter_spec h).2

theorem firstOccurrenceAtOrAfter_minimal
    {stream : ℕ → ℕ} {cutoff x t : ℕ}
    (hcutoff : cutoff ≤ t) (hvalue : stream t = x) :
    firstOccurrenceAtOrAfter stream cutoff x ≤ t := by
  classical
  have h : OccursAtOrAfter stream cutoff x :=
    ⟨t, hcutoff, hvalue⟩
  rw [firstOccurrenceAtOrAfter, dif_pos h]
  exact Nat.find_min' h ⟨hcutoff, hvalue⟩

/-- The canonical late-occurrence assignment is injective on the values for
which it is defined.  Repetitions in `stream` do not affect this fact. -/
theorem firstOccurrenceAtOrAfter_injectiveOn
    (stream : ℕ → ℕ) (cutoff : ℕ) :
    Set.InjOn (firstOccurrenceAtOrAfter stream cutoff)
      {x | OccursAtOrAfter stream cutoff x} := by
  intro x hx y hy hxy
  change OccursAtOrAfter stream cutoff x at hx
  change OccursAtOrAfter stream cutoff y at hy
  calc
    x = stream (firstOccurrenceAtOrAfter stream cutoff x) :=
      (stream_firstOccurrenceAtOrAfter hx).symm
    _ = stream (firstOccurrenceAtOrAfter stream cutoff y) :=
      congrArg stream hxy
    _ = y := stream_firstOccurrenceAtOrAfter hy

/-- In an exact presentation, a target value not seen before `cutoff` must
occur at or after `cutoff`. -/
theorem occursAtOrAfter_of_presents_of_not_mem_sample
    {stream : ℕ → ℕ} {L : Language} {cutoff x : ℕ}
    (hP : Presents stream L) (hxL : x ∈ L)
    (hxSample : x ∉ sample stream cutoff) :
    OccursAtOrAfter stream cutoff x := by
  rw [← hP] at hxL
  obtain ⟨t, hvalue⟩ := hxL
  refine ⟨t, ?_, hvalue⟩
  by_contra hcutoff
  exact hxSample (mem_sample_iff.mpr
    ⟨t, Nat.lt_of_not_ge hcutoff, hvalue⟩)

/-- Consequently, canonical late occurrences inject the unseen part of an
exactly presented target into post-cutoff rounds. -/
theorem firstOccurrenceAtOrAfter_injectiveOn_unseen
    {stream : ℕ → ℕ} {L : Language} (hP : Presents stream L)
    (cutoff : ℕ) :
    Set.InjOn (firstOccurrenceAtOrAfter stream cutoff)
      (L \ (sample stream cutoff : Set ℕ)) := by
  apply (firstOccurrenceAtOrAfter_injectiveOn stream cutoff).mono
  intro x hx
  exact occursAtOrAfter_of_presents_of_not_mem_sample
    hP hx.1 hx.2

end PartialEnumeration
end KleinbergWei
end GenLimit
