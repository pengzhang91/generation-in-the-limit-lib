import GenLimit.Core.GenericGeneration

/-!
# Finite prefixes followed by infinite streams

Paper-independent constructions for placing a finite list in front of an
infinite stream.  This module is intentionally independent of locking,
identification, and any particular language-generation model.
-/

namespace GenLimit.Support

/-- Follow the entries of `xs`, then continue with `tail`. -/
def prependStream
    (xs : List α) (tail : GenLimit.Generic.Stream α) :
    GenLimit.Generic.Stream α :=
  fun n => if h : n < xs.length then xs.get ⟨n, h⟩
    else tail (n - xs.length)

theorem prependStream_apply_of_lt
    (xs : List α) (tail : GenLimit.Generic.Stream α)
    {n : ℕ} (hn : n < xs.length) :
    prependStream xs tail n = xs.get ⟨n, hn⟩ := by
  simp [prependStream, hn]

theorem prependStream_apply_of_not_lt
    (xs : List α) (tail : GenLimit.Generic.Stream α)
    {n : ℕ} (hn : ¬ n < xs.length) :
    prependStream xs tail n = tail (n - xs.length) := by
  simp [prependStream, hn]

@[simp] theorem prependStream_add
    (xs : List α) (tail : GenLimit.Generic.Stream α) (n : ℕ) :
    prependStream xs tail (xs.length + n) = tail n := by
  simp [prependStream]

/-- Prepending a finite list adds exactly the values from that list to the
range of the tail. -/
theorem range_prependStream [DecidableEq α]
    (xs : List α) (tail : GenLimit.Generic.Stream α) :
    Set.range (prependStream xs tail) =
      (↑xs.toFinset : Set α) ∪ Set.range tail := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    by_cases hn : n < xs.length
    · apply Set.mem_union_left
      rw [prependStream_apply_of_lt xs tail hn]
      change xs.get ⟨n, hn⟩ ∈ xs.toFinset
      rw [List.mem_toFinset]
      exact List.get_mem xs ⟨n, hn⟩
    · apply Set.mem_union_right
      exact ⟨n - xs.length, by simp [prependStream, hn]⟩
  · rintro x (hx | hx)
    · change x ∈ xs.toFinset at hx
      rw [List.mem_toFinset] at hx
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
      exact ⟨i, by simpa [prependStream, i.isLt] using hi⟩
    · obtain ⟨n, rfl⟩ := hx
      exact ⟨xs.length + n, prependStream_add xs tail n⟩

/-- Prepending values already in an exactly presented language preserves the
exact presentation. -/
theorem prependStream_presents
    {xs : List α} {tail : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hxs : ∀ x, x ∈ xs → x ∈ L)
    (hP : GenLimit.Generic.Presents tail L) :
    GenLimit.Generic.Presents (prependStream xs tail) L := by
  classical
  rw [GenLimit.Generic.Presents, range_prependStream, hP]
  exact Set.union_eq_right.mpr (by
    intro x hx
    exact hxs x (List.mem_toFinset.mp hx))

end GenLimit.Support
