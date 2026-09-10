import GenLimit.Paper30_TimeSensitiveLanguageGeneration.Definitions

/-!
# Structural cores of the measure-zero-chain examples

Source: Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2, Appendix B,
Examples 1--2.

This module checks the literal nesting, coverage, complete-block/marker, and
infinitude properties of both examples.  The separate
`MeasureZeroDensity` module supplies the logarithmic counting arguments and
completed `MeasureZeroChain` values for both examples.
-/

namespace GenLimit.TimeSensitive

/-- Positive naturals, matching the paper's convention `ℕ = {1,2,...}`. -/
def positiveNaturals : Set ℕ := {n | 0 < n}

/-- Appendix-B Example 1 in closed form.

All dyadic blocks through `j` are retained, and the first point `2^m` of
every later block is retained. -/
def dyadicBlockLanguage (j : ℕ) : Set ℕ :=
  {n | 0 < n ∧ (n < 2 ^ (j + 1) ∨ ∃ m, n = 2 ^ m)}

theorem dyadicBlockLanguage_nested :
    Monotone dyadicBlockLanguage := by
  intro j k hjk n hn
  rcases hn with ⟨hnpos, hnsmall | hnpow⟩
  · refine ⟨hnpos, Or.inl ?_⟩
    exact hnsmall.trans_le
      (Nat.pow_le_pow_right (by decide)
        (Nat.add_le_add_right hjk 1))
  · exact ⟨hnpos, Or.inr hnpow⟩

theorem dyadic_complete_block_mem
    {j m n : ℕ} (hmj : m ≤ j)
    (hlower : 2 ^ m ≤ n) (hupper : n < 2 ^ (m + 1)) :
    n ∈ dyadicBlockLanguage j := by
  have hnpos : 0 < n :=
    (pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hlower
  refine ⟨hnpos, Or.inl ?_⟩
  exact hupper.trans_le
    (Nat.pow_le_pow_right (by decide)
      (Nat.add_le_add_right hmj 1))

theorem dyadic_distinguished_mem (j m : ℕ) :
    2 ^ m ∈ dyadicBlockLanguage j := by
  exact ⟨pow_pos (by decide) _, Or.inr ⟨m, rfl⟩⟩

theorem iUnion_dyadicBlockLanguage :
    (⋃ j, dyadicBlockLanguage j) = positiveNaturals := by
  ext n
  constructor
  · intro hn
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hn
    exact hj.1
  · intro hn
    have hpow : n < 2 ^ (n + 1) :=
      n.lt_two_pow_self.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
    exact Set.mem_iUnion.mpr
      ⟨n, hn, Or.inl hpow⟩

theorem dyadicBlockLanguage_infinite (j : ℕ) :
    (dyadicBlockLanguage j).Infinite := by
  have hrange :
      (Set.range fun m : ℕ => 2 ^ m).Infinite :=
    Set.infinite_range_of_injective
      (Nat.pow_right_injective (by decide))
  exact hrange.mono (show
    Set.range (fun m : ℕ => 2 ^ m) ⊆ dyadicBlockLanguage j by
      rintro _ ⟨m, rfl⟩
      exact dyadic_distinguished_mem j m)

/-- Marker locations in Appendix-B Example 2. -/
def marker (i : ℕ) : ℕ :=
  if i = 0 then 0 else 3 ^ i

/-- The union of the length-`j` intervals attached to all markers. -/
def markerIntervalLanguage (j : ℕ) : Set ℕ :=
  {n | ∃ i, marker i ≤ n ∧ n ≤ marker i + j}

theorem markerIntervalLanguage_nested :
    Monotone markerIntervalLanguage := by
  intro j k hjk n
  rintro ⟨i, hil, hiu⟩
  exact ⟨i, hil, hiu.trans (Nat.add_le_add_left hjk _)⟩

theorem marker_mem_markerIntervalLanguage (j i : ℕ) :
    marker i ∈ markerIntervalLanguage j := by
  exact ⟨i, le_rfl, Nat.le_add_right _ _⟩

theorem iUnion_markerIntervalLanguage :
    (⋃ j, markerIntervalLanguage j) = Set.univ := by
  ext n
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨n, 0, ?_⟩
  simp [marker]

theorem markerIntervalLanguage_infinite (j : ℕ) :
    (markerIntervalLanguage j).Infinite := by
  let f : ℕ → ℕ := fun k => 3 ^ (k + 1)
  have hf : Function.Injective f := by
    intro a b hab
    have hp :=
      Nat.pow_right_injective (by decide : 2 ≤ (3 : ℕ)) hab
    omega
  have hrange : (Set.range f).Infinite :=
    Set.infinite_range_of_injective hf
  exact hrange.mono (show Set.range f ⊆ markerIntervalLanguage j by
    rintro _ ⟨k, rfl⟩
    have hne : k + 1 ≠ 0 := by omega
    simpa [f, marker, hne] using
      marker_mem_markerIntervalLanguage j (k + 1))

end GenLimit.TimeSensitive
