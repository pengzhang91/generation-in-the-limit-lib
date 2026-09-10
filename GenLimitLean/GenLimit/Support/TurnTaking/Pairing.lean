import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite turn-taking pairing

This module isolates the paper-independent combinatorial core of the
Kleinberg--Wei turn-taking argument.  Ordinary credited elements have
injective, disjoint partners in the same finite prefix; a separate exceptional
set accounts for sparse catch-up rounds.
-/

namespace GenLimit.TurnTaking

/-- If every ordinary credit has a distinct non-credit partner in the same
prefix and there are at most `e` exceptional credits, then credits occupy at
most half the prefix up to the exceptional budget. -/
theorem finite_upper_bound
    [DecidableEq α]
    {prefixSet credited paired exceptions : Finset α}
    (partner : α → α) {i e : ℕ}
    (hprefix : prefixSet.card = i)
    (hcreditedPrefix : credited ⊆ prefixSet)
    (hcreditCover : credited ⊆ paired ∪ exceptions)
    (hpairedCredit : paired ⊆ credited)
    (hexceptions : exceptions.card ≤ e)
    (hpartnerPrefix : ∀ x ∈ paired, partner x ∈ prefixSet)
    (hpartnerOutside : ∀ x ∈ paired, partner x ∉ credited)
    (hpartnerInj : Set.InjOn partner paired) :
    2 * credited.card ≤ i + 2 * e := by
  let partners := paired.image partner
  have hpartnersCard : partners.card = paired.card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact hpartnerInj hx hy hxy
  have hdisjoint : Disjoint paired partners := by
    rw [Finset.disjoint_left]
    intro x hxPaired hxPartner
    obtain ⟨y, hyPaired, hyx⟩ := Finset.mem_image.mp hxPartner
    have hxCredit : x ∈ credited := hpairedCredit hxPaired
    exact hpartnerOutside y hyPaired (hyx ▸ hxCredit)
  have hunionSubset : paired ∪ partners ⊆ prefixSet := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxPaired | hxPartner
    · exact hcreditedPrefix (hpairedCredit hxPaired)
    · obtain ⟨y, hyPaired, hyx⟩ := Finset.mem_image.mp hxPartner
      exact hyx ▸ hpartnerPrefix y hyPaired
  have hpairedTwice : 2 * paired.card ≤ i := by
    have hcard := Finset.card_le_card hunionSubset
    rw [Finset.card_union_of_disjoint hdisjoint, hpartnersCard,
      hprefix] at hcard
    omega
  have hcreditCard : credited.card ≤ paired.card + exceptions.card := by
    exact (Finset.card_le_card hcreditCover).trans (Finset.card_union_le _ _)
  omega

end GenLimit.TurnTaking
