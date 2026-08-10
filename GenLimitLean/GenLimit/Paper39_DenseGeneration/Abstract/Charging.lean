import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat

/-!
# Abstract charging bound for switch losses

This module isolates the finite combinatorial core of Lemma 3.13.  A finite set
of losses is assigned distinct positive focus-change counts `τ`.  Loss `ℓ` has
a finite charge set containing at least `2 ^ τ ℓ` points, all lying in the
prefix `Finset.range n`.

The paper also states that charge sets belonging to different losses are
disjoint.  That fact is not needed for the logarithmic conclusion: among `w`
distinct positive counts, one is at least `w`, and its charge set alone has at
least `2 ^ w` elements.  Thus the results below use strictly weaker hypotheses
than the paper's charging argument.
-/

namespace GenLimit

/-- A finite injective family of positive natural-number labels contains a
label at least as large as the cardinality of the family. -/
theorem exists_card_le_of_injOn_pos
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (τ : α → ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < τ ℓ)
    (hinj : Set.InjOn τ losses)
    (hne : losses.Nonempty) :
    ∃ ℓ ∈ losses, losses.card ≤ τ ℓ := by
  classical
  let values : Finset ℕ := losses.image τ
  have hvalues : values.Nonempty := hne.image τ
  let M := values.max' hvalues
  have hMmem : M ∈ values := values.max'_mem hvalues
  obtain ⟨ℓ, hℓ, hτℓ⟩ := Finset.mem_image.mp hMmem
  refine ⟨ℓ, hℓ, ?_⟩
  have hsubset : values ⊆ Finset.Icc 1 M := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr
      ⟨hpos a ha, Finset.le_max' values (τ a) hx⟩
  have hcard : values.card = losses.card :=
    Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card hsubset
  rw [Nat.card_Icc] at hle
  have hcardM : values.card ≤ M := by
    simpa using hle
  rw [← hcard, hτℓ]
  exact hcardM

/-- The exponential form of the charging lemma.  Pairwise disjointness of the
charge sets is not required. -/
theorem charging_pow_le_prefix
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (τ : α → ℕ) (charge : α → Finset ℕ) (n : ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < τ ℓ)
    (hinj : Set.InjOn τ losses)
    (hsize : ∀ ℓ ∈ losses, 2 ^ τ ℓ ≤ (charge ℓ).card)
    (hprefix : ∀ ℓ ∈ losses, charge ℓ ⊆ Finset.range n)
    (hn : 0 < n) :
    2 ^ losses.card ≤ n := by
  classical
  by_cases hne : losses.Nonempty
  · obtain ⟨ℓ, hℓ, hcardτ⟩ :=
      exists_card_le_of_injOn_pos losses τ hpos hinj hne
    calc
      2 ^ losses.card ≤ 2 ^ τ ℓ :=
        Nat.pow_le_pow_right (by omega) hcardτ
      _ ≤ (charge ℓ).card := hsize ℓ hℓ
      _ ≤ (Finset.range n).card :=
        Finset.card_le_card (hprefix ℓ hℓ)
      _ = n := Finset.card_range n
  · have hempty : losses = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa [hempty] using hn

/-- Lemma 3.13 in integer form: the number of certified losses in a prefix of
size `n` is at most the base-two natural logarithm of `n`. -/
theorem charging_card_le_log_two
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (τ : α → ℕ) (charge : α → Finset ℕ) (n : ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < τ ℓ)
    (hinj : Set.InjOn τ losses)
    (hsize : ∀ ℓ ∈ losses, 2 ^ τ ℓ ≤ (charge ℓ).card)
    (hprefix : ∀ ℓ ∈ losses, charge ℓ ⊆ Finset.range n)
    (hn : 0 < n) :
    losses.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  exact charging_pow_le_prefix losses τ charge n hpos hinj hsize hprefix hn

/-- The same result using Lean's specialized `Nat.log2`. -/
theorem charging_card_le_log2
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (τ : α → ℕ) (charge : α → Finset ℕ) (n : ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < τ ℓ)
    (hinj : Set.InjOn τ losses)
    (hsize : ∀ ℓ ∈ losses, 2 ^ τ ℓ ≤ (charge ℓ).card)
    (hprefix : ∀ ℓ ∈ losses, charge ℓ ⊆ Finset.range n)
    (hn : 0 < n) :
    losses.card ≤ Nat.log2 n := by
  rw [Nat.log2_eq_log_two]
  exact charging_card_le_log_two losses τ charge n hpos hinj hsize hprefix hn

end GenLimit
