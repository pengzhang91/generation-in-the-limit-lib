import GenLimit.Core.OrderedDensity
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Density under finite changes of a canonically ordered target

The natural-number order induces a canonical ordering on every infinite
language. If two reference languages differ by finitely many elements, their
canonical orderings give the same lower and upper densities to every set.
This changes the reference language, unlike the fixed-reference finite-set
perturbation lemmas in `Core.OrderedDensity`.
-/

namespace GenLimit.KleinbergWei.OrderedLanguage

open Filter

/-- The ordering induced by the ambient natural-number order. -/
noncomputable def canonical (L : Language) (hL : L.Infinite) : OrderedLanguage := by
  classical
  exact {
    carrier := L
    enumeration := Nat.nth (fun x => x ∈ L)
    enumeration_injective := Nat.nth_injective hL
    range_enumeration := Nat.range_nth_of_infinite hL }

@[simp] theorem canonical_carrier (L : Language) (hL : L.Infinite) :
    (canonical L hL).carrier = L := rfl

theorem canonical_strictMono (L : Language) (hL : L.Infinite) :
    StrictMono (canonical L hL).enumeration := by
  classical
  exact Nat.nth_strictMono hL

/-- The first `n` elements of a reference ordering, as a finite set. -/
def orderedPrefix (K : OrderedLanguage) (n : ℕ) : Finset ℕ :=
  (Finset.range n).image K.enumeration

@[simp] theorem card_orderedPrefix (K : OrderedLanguage) (n : ℕ) :
    (K.orderedPrefix n).card = n := by
  rw [orderedPrefix, Finset.card_image_of_injective _ K.enumeration_injective,
    Finset.card_range]

theorem mem_orderedPrefix_iff (K : OrderedLanguage)
    (hK : StrictMono K.enumeration) (n x : ℕ) :
    x ∈ K.orderedPrefix n ↔ x ∈ K.carrier ∧ x < K.enumeration n := by
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨K.range_enumeration ▸ Set.mem_range_self i,
      hK (Finset.mem_range.mp hi)⟩
  · rintro ⟨hx, hlt⟩
    rw [← K.range_enumeration] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_range.mpr (hK.lt_iff_lt.mp hlt), rfl⟩

private theorem orderedPrefix_sdiff_card_le_of_cutoff_le
    (K L : OrderedLanguage)
    (hK : StrictMono K.enumeration) (hL : StrictMono L.enumeration)
    (hKL : (K.carrier \ L.carrier).Finite) (n : ℕ)
    (hcut : K.enumeration n ≤ L.enumeration n) :
    (K.orderedPrefix n \ L.orderedPrefix n).card ≤ hKL.toFinset.card := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxK, hxL⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hxK, hlt⟩ := (K.mem_orderedPrefix_iff hK n x).mp hxK
  apply hKL.mem_toFinset.mpr
  refine ⟨hxK, ?_⟩
  intro hx
  exact hxL ((L.mem_orderedPrefix_iff hL n x).mpr
    ⟨hx, hlt.trans_le hcut⟩)

/-- Equal-length canonical prefixes differ in only boundedly many elements. -/
theorem orderedPrefix_sdiff_card_le
    (K L : OrderedLanguage)
    (hK : StrictMono K.enumeration) (hL : StrictMono L.enumeration)
    (hKL : (K.carrier \ L.carrier).Finite)
    (hLK : (L.carrier \ K.carrier).Finite) (n : ℕ) :
    (K.orderedPrefix n \ L.orderedPrefix n).card ≤
      hKL.toFinset.card + hLK.toFinset.card := by
  rcases le_total (K.enumeration n) (L.enumeration n) with hcut | hcut
  · have h := orderedPrefix_sdiff_card_le_of_cutoff_le K L hK hL hKL n hcut
    omega
  · have h := orderedPrefix_sdiff_card_le_of_cutoff_le L K hL hK hLK n hcut
    have heq : (K.orderedPrefix n \ L.orderedPrefix n).card =
        (L.orderedPrefix n \ K.orderedPrefix n).card :=
      Finset.card_sdiff_comm (by simp)
    omega

theorem prefixCount_eq_filter_orderedPrefix
    (K : OrderedLanguage) (A : Language) [DecidablePred (fun x => x ∈ A)] (n : ℕ) :
    K.prefixCount A n = ((K.orderedPrefix n).filter fun x => x ∈ A).card := by
  classical
  rw [orderedPrefix, Finset.filter_image,
    Finset.card_image_of_injective _ K.enumeration_injective]
  unfold prefixCount
  congr 1
  ext i
  simp only [Finset.mem_filter]

/-- Changing the canonical reference language by finitely many points changes
every prefix count by at most the size of that finite change. -/
theorem prefixCount_le_add_carrier_difference
    (K L : OrderedLanguage)
    (hK : StrictMono K.enumeration) (hL : StrictMono L.enumeration)
    (hKL : (K.carrier \ L.carrier).Finite)
    (hLK : (L.carrier \ K.carrier).Finite) (A : Language) (n : ℕ) :
    K.prefixCount A n ≤ L.prefixCount A n +
      (hKL.toFinset.card + hLK.toFinset.card) := by
  classical
  have hsub : (K.orderedPrefix n).filter (fun x => x ∈ A) ⊆
      (L.orderedPrefix n).filter (fun x => x ∈ A) ∪
        (K.orderedPrefix n \ L.orderedPrefix n) := by
    intro x hx
    obtain ⟨hxK, hxA⟩ := Finset.mem_filter.mp hx
    by_cases hxL : x ∈ L.orderedPrefix n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxL, hxA⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxK, hxL⟩)
  rw [K.prefixCount_eq_filter_orderedPrefix, L.prefixCount_eq_filter_orderedPrefix]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (K.orderedPrefix_sdiff_card_le L hK hL hKL hLK n) _))

private theorem lowerDensity_le_of_finite_carrier_difference
    (K L : OrderedLanguage)
    (hK : StrictMono K.enumeration) (hL : StrictMono L.enumeration)
    (hKL : (K.carrier \ L.carrier).Finite)
    (hLK : (L.carrier \ K.carrier).Finite) (A : Language) :
    K.lowerDensity A ≤ L.lowerDensity A := by
  let M := hKL.toFinset.card + hLK.toFinset.card
  have hprefix (n : ℕ) :
      K.prefixRatio A n ≤ L.prefixRatio A n + (M : ℝ) / n := by
    by_cases hn : n = 0
    · simp [hn]
    · simp only [prefixRatio, hn, if_false]
      rw [← add_div]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast K.prefixCount_le_add_carrier_difference L hK hL hKL hLK A n
      · positivity
  have herror : Tendsto (fun n : ℕ => (M : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  unfold lowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (fun n => L.prefixRatio_le_one A n))
    (isBoundedUnder_of ⟨0, fun n => L.prefixRatio_nonneg A n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hlarge : ∀ᶠ n : ℕ in atTop, r < K.prefixRatio A n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, fun n => K.prefixRatio_nonneg A n⟩)
  have hsmall : ∀ᶠ n : ℕ in atTop, (M : ℝ) / n < r - y :=
    herror.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hlarge, hsmall] with n hn herrorn
  linarith [hprefix n]

/-- Finite changes of a reference language preserve lower density when both
reference orderings inherit the same ambient natural-number order. -/
theorem lowerDensity_eq_of_finite_carrier_difference
    (K L : OrderedLanguage)
    (hK : StrictMono K.enumeration) (hL : StrictMono L.enumeration)
    (hKL : (K.carrier \ L.carrier).Finite)
    (hLK : (L.carrier \ K.carrier).Finite) (A : Language) :
    K.lowerDensity A = L.lowerDensity A :=
  le_antisymm
    (lowerDensity_le_of_finite_carrier_difference K L hK hL hKL hLK A)
    (lowerDensity_le_of_finite_carrier_difference L K hL hK hLK hKL A)

/-- The corresponding upper-density invariance follows by taking complements. -/
theorem upperDensity_eq_of_finite_carrier_difference
    (K L : OrderedLanguage)
    (hK : StrictMono K.enumeration) (hL : StrictMono L.enumeration)
    (hKL : (K.carrier \ L.carrier).Finite)
    (hLK : (L.carrier \ K.carrier).Finite) (A : Language) :
    K.upperDensity A = L.upperDensity A := by
  have hcompl (P : OrderedLanguage) :
      P.lowerDensity Aᶜ = 1 - P.upperDensity A := by
    have h := P.lowerDensity_diff A
    rw [Set.diff_eq, Set.inter_comm, lowerDensity_inter_carrier] at h
    exact h
  have h := lowerDensity_eq_of_finite_carrier_difference K L hK hL hKL hLK Aᶜ
  rw [hcompl K, hcompl L] at h
  linarith

end GenLimit.KleinbergWei.OrderedLanguage
