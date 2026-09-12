import GenLimit.Paper18_SafeLanguageGeneration.Definitions
import Mathlib.Data.Set.Finite.Basic

/-!
# Vertical padding for safe generation

These are the set-theoretic identities used by Algorithm 1 and Theorem 5.1 of
arXiv:2601.08648v2.  The full reduction also needs a single
prefix-compatible family of labeled runs; this file deliberately proves only
the exact padding facts and does not claim the source theorem prematurely.
-/

namespace GenLimit.SafeGeneration

open GenLimit.Generic

/-- The paper's vertical padding, using positive natural-number levels. -/
def verticalPad (L : Generic.Language α) : Generic.Language (α × ℕ) :=
  {p | p.1 ∈ L ∧ 0 < p.2}

@[simp] theorem mem_verticalPad
    {L : Generic.Language α} {x : α} {n : ℕ} :
    (x, n) ∈ verticalPad L ↔ x ∈ L ∧ 0 < n :=
  Iff.rfl

theorem verticalPad_mono
    {K H : Generic.Language α} (h : K ⊆ H) :
    verticalPad K ⊆ verticalPad H := by
  rintro ⟨x, n⟩ ⟨hx, hn⟩
  exact ⟨h hx, hn⟩

theorem verticalPad_diff (K H : Generic.Language α) :
    verticalPad K \ verticalPad H = verticalPad (K \ H) := by
  ext p
  rcases p with ⟨x, n⟩
  simp only [Set.mem_diff, mem_verticalPad]
  constructor
  · rintro ⟨⟨hxK, hn⟩, hxH⟩
    exact ⟨⟨hxK, fun h => hxH ⟨h, hn⟩⟩, hn⟩
  · rintro ⟨⟨hxK, hxH⟩, hn⟩
    exact ⟨⟨hxK, hn⟩, fun h => hxH h.1⟩

theorem verticalPad_nonempty_iff (L : Generic.Language α) :
    (verticalPad L).Nonempty ↔ L.Nonempty := by
  constructor
  · rintro ⟨⟨x, n⟩, hx, -⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨(x, 1), hx, by simp⟩

theorem verticalPad_infinite_of_nonempty
    {L : Generic.Language α} (hL : L.Nonempty) :
    (verticalPad L).Infinite := by
  obtain ⟨x, hx⟩ := hL
  let f : ℕ → α × ℕ := fun n => (x, n + 1)
  have hf : Function.Injective f := by
    intro m n h
    exact Nat.add_right_cancel (Prod.mk_inj.mp h).2
  have hrange : Set.range f ⊆ verticalPad L := by
    rintro p ⟨n, rfl⟩
    exact ⟨hx, Nat.zero_lt_succ n⟩
  exact (Set.infinite_range_of_injective hf).mono hrange

theorem verticalPad_diff_infinite_iff_nonempty
    (K H : Generic.Language α) :
    (verticalPad K \ verticalPad H).Infinite ↔ (K \ H).Nonempty := by
  rw [verticalPad_diff]
  constructor
  · intro h
    exact (verticalPad_nonempty_iff (K \ H)).mp h.nonempty
  · intro h
    exact verticalPad_infinite_of_nonempty h

end GenLimit.SafeGeneration
