import GenLimit.Paper17_InfiniteContamination.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Vanishing-noise counting lemmas

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Theorem 5.1 and its proof.

This file proves two exact analytic ingredients used by the paper:

* finite additive noise implies vanishing empirical noise;
* a finite family of languages whose noise rates all vanish along one
  injective stream has an infinite common intersection.

The second statement is the union-bound core of the proof of Theorem 5.1.
The remaining priority-based online selection argument is deliberately not
hidden in this module.
-/

namespace GenLimit.InfiniteContamination

open Filter
open scoped Topology

/-! ## Finite noise is vanishing noise -/

theorem noiseCount_le_finiteNoise_card
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hfinite : FiniteNoise stream L) (n : ℕ) :
    noiseCount stream L n ≤ hfinite.toFinset.card := by
  classical
  unfold noiseCount
  apply Finset.card_le_card
  intro t ht
  have htbad : stream t ∉ L := (Finset.mem_filter.mp ht).2
  exact (Set.Finite.mem_toFinset hfinite).2 htbad

/-- Every fixed finite amount of noise has empirical rate tending to zero. -/
theorem finiteNoise_implies_vanishingNoise
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hfinite : FiniteNoise stream L) :
    VanishingNoise stream L := by
  let B : ℕ := hfinite.toFinset.card
  have hB :
      Tendsto (fun n : ℕ => (B : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero
    (f := empiricalNoiseRate stream L)
    (g := fun n : ℕ => (B : ℝ) / (n : ℝ)) ?_ ?_ hB
  · exact fun n => empiricalNoiseRate_nonneg stream L n
  · intro n
    by_cases hn : n = 0
    · simp [empiricalNoiseRate, hn]
    · simp only [empiricalNoiseRate, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast
          (show noiseCount stream L n ≤ B by
            simpa [B] using noiseCount_le_finiteNoise_card hfinite n)
      · exact Nat.cast_nonneg n

/-- Definition 7's paper-level implication, retaining injectivity and full
coverage unchanged. -/
theorem finiteNoiseEnumeration_implies_vanishingNoiseEnumeration
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (h : FiniteNoiseEnumeration stream L) :
    VanishingNoiseEnumeration stream L :=
  ⟨h.1, h.2.1, finiteNoise_implies_vanishingNoise h.2.2⟩

/-! ## Finite-union bound for noisy positions -/

/-- Common intersection of a finite family.  For the empty family this is
the whole universe. -/
def finiteCommonCore
    (S : Finset (GenLimit.Generic.Language α)) :
    GenLimit.Generic.Language α :=
  {x | ∀ L, L ∈ S → x ∈ L}

@[simp] theorem finiteCommonCore_empty :
    finiteCommonCore (∅ : Finset (GenLimit.Generic.Language α)) =
      Set.univ := by
  ext x
  simp [finiteCommonCore]

@[simp] theorem finiteCommonCore_insert
    [DecidableEq (GenLimit.Generic.Language α)]
    (L : GenLimit.Generic.Language α)
    (S : Finset (GenLimit.Generic.Language α)) :
    finiteCommonCore (insert L S : Finset (GenLimit.Generic.Language α)) =
      L ∩ finiteCommonCore S := by
  ext x
  simp [finiteCommonCore]

theorem finiteCommonCore_subset_of_mem
    {S : Finset (GenLimit.Generic.Language α)}
    {L : GenLimit.Generic.Language α} (hL : L ∈ S) :
    finiteCommonCore S ⊆ L := by
  intro x hx
  exact hx L hL

/-- The two-language family used to expose the reversed containment in the
printed proof of Theorem 5.1. -/
noncomputable def containmentDiagnosticFamily :
    Finset (GenLimit.Generic.Language ℕ) := by
  classical
  exact {Set.univ, {n : ℕ | n ≠ 0}}

/-- Source diagnostic for the proof text following Theorem 5.1.

That proof writes `Cl(𝓛(p)) ⊇ K` after noting that the target `K` belongs
to `𝓛(p)`.  The containment is reversed: an intersection is contained in
each member.  The co-singleton example below shows that the printed
containment can be strict and false. -/
theorem theorem_5_1_printed_containment_is_reversed :
    finiteCommonCore containmentDiagnosticFamily ⊆ Set.univ ∧
      ¬(Set.univ ⊆
        finiteCommonCore containmentDiagnosticFamily) := by
  classical
  constructor
  · exact Set.subset_univ _
  · intro h
    have hzero := h (show 0 ∈ (Set.univ : Set ℕ) by simp)
    simp [finiteCommonCore, containmentDiagnosticFamily] at hzero

theorem noiseCount_inter_le_add
    (stream : GenLimit.Generic.Stream α)
    (A B : GenLimit.Generic.Language α) (n : ℕ) :
    noiseCount stream (A ∩ B) n ≤
      noiseCount stream A n + noiseCount stream B n := by
  classical
  let badA := (Finset.range n).filter fun t => stream t ∉ A
  let badB := (Finset.range n).filter fun t => stream t ∉ B
  have hsub :
      (Finset.range n).filter (fun t => stream t ∉ A ∩ B) ⊆
        badA ∪ badB := by
    intro t ht
    simp only [Finset.mem_filter, Set.mem_inter_iff, not_and_or] at ht
    rcases ht.2 with htA | htB
    · exact Finset.mem_union_left _ (by
        exact Finset.mem_filter.mpr ⟨ht.1, htA⟩)
    · exact Finset.mem_union_right _ (by
        exact Finset.mem_filter.mpr ⟨ht.1, htB⟩)
  calc
    noiseCount stream (A ∩ B) n
        ≤ (badA ∪ badB).card := by
          simpa [noiseCount] using Finset.card_le_card hsub
    _ ≤ badA.card + badB.card := Finset.card_union_le _ _
    _ = noiseCount stream A n + noiseCount stream B n := by
      rfl

theorem empiricalNoiseRate_inter_le_add
    (stream : GenLimit.Generic.Stream α)
    (A B : GenLimit.Generic.Language α) (n : ℕ) :
    empiricalNoiseRate stream (A ∩ B) n ≤
      empiricalNoiseRate stream A n +
        empiricalNoiseRate stream B n := by
  by_cases hn : n = 0
  · simp [empiricalNoiseRate, hn]
  · simp only [empiricalNoiseRate, hn, if_false]
    rw [← add_div]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast noiseCount_inter_le_add stream A B n
    · exact Nat.cast_nonneg n

theorem vanishingNoise_inter
    {stream : GenLimit.Generic.Stream α}
    {A B : GenLimit.Generic.Language α}
    (hA : VanishingNoise stream A)
    (hB : VanishingNoise stream B) :
    VanishingNoise stream (A ∩ B) := by
  have hsum :
      Tendsto
        (fun n =>
          empiricalNoiseRate stream A n +
            empiricalNoiseRate stream B n)
        atTop (𝓝 0) := by
    simpa only [zero_add] using hA.add hB
  apply squeeze_zero
  · exact fun n => empiricalNoiseRate_nonneg stream (A ∩ B) n
  · exact empiricalNoiseRate_inter_le_add stream A B
  · exact hsum

theorem vanishingNoise_univ
    (stream : GenLimit.Generic.Stream α) :
    VanishingNoise stream (Set.univ : GenLimit.Generic.Language α) := by
  have hzero :
      empiricalNoiseRate stream
        (Set.univ : GenLimit.Generic.Language α) = fun _ => 0 := by
    funext n
    simp [empiricalNoiseRate, noiseCount]
  unfold VanishingNoise
  rw [hzero]
  exact tendsto_const_nhds

/-- Finite union bound in asymptotic form: if one stream has vanishing noise
relative to every member of a finite family, it also has vanishing noise
relative to their common intersection. -/
theorem vanishingNoise_finiteCommonCore
    {stream : GenLimit.Generic.Stream α}
    (S : Finset (GenLimit.Generic.Language α))
    (hS : ∀ L, L ∈ S → VanishingNoise stream L) :
    VanishingNoise stream (finiteCommonCore S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using vanishingNoise_univ stream
  | @insert L S hLS ih =>
      rw [finiteCommonCore_insert]
      apply vanishingNoise_inter
      · exact hS L (Finset.mem_insert_self L S)
      · apply ih
        intro K hKS
        exact hS K (Finset.mem_insert_of_mem hKS)

/-! ## The common intersection is infinite -/

/-- Number of true examples in the first `n` positions. -/
noncomputable def trueCount
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter fun t => stream t ∈ L).card

theorem trueCount_add_noiseCount
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) :
    trueCount stream L n + noiseCount stream L n = n := by
  classical
  simpa [trueCount, noiseCount] using
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.range n) (fun t => stream t ∈ L))

theorem trueCount_le_finite_card
    {stream : GenLimit.Generic.Stream α}
    (hinjective : Function.Injective stream)
    {L : GenLimit.Generic.Language α}
    (hfinite : L.Finite) (n : ℕ) :
    trueCount stream L n ≤ hfinite.toFinset.card := by
  classical
  let good := (Finset.range n).filter fun t => stream t ∈ L
  have hstreamInjective :
      ∀ a ∈ good, ∀ b ∈ good, stream a = stream b → a = b := by
    intro a _ b _ hab
    exact hinjective hab
  have himageSubset : good.image stream ⊆ hfinite.toFinset := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have htL : stream t ∈ L := (Finset.mem_filter.mp ht).2
    exact (Set.Finite.mem_toFinset hfinite).2 htL
  calc
    trueCount stream L n = good.card := rfl
    _ = (good.image stream).card := by
      symm
      exact Finset.card_image_iff.mpr hstreamInjective
    _ ≤ hfinite.toFinset.card := Finset.card_le_card himageSubset

/-- An injective stream cannot have vanishing noise relative to a finite
language: asymptotically almost all positions would have to lie in the
finite language, contradicting repetition-freeness. -/
theorem infinite_of_injective_vanishingNoise
    {stream : GenLimit.Generic.Stream α}
    (hinjective : Function.Injective stream)
    {L : GenLimit.Generic.Language α}
    (hvanishing : VanishingNoise stream L) :
    L.Infinite := by
  classical
  by_contra hnot
  have hfinite : L.Finite := Set.not_infinite.mp hnot
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        empiricalNoiseRate stream L n < (1 / 2 : ℝ) := by
    unfold VanishingNoise at hvanishing
    exact (tendsto_order.1 hvanishing).2 _ (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  let B := hfinite.toFinset.card
  let n := max N (2 * B + 2)
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hnB : 2 * B + 2 ≤ n := Nat.le_max_right _ _
  have hnpos : 0 < n := by omega
  have hrate := hN n hnN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnoiseR :
      2 * (noiseCount stream L n : ℝ) < (n : ℝ) := by
    simp only [empiricalNoiseRate, Nat.ne_of_gt hnpos, if_false] at hrate
    rw [div_lt_iff₀ hnR] at hrate
    nlinarith
  have hpartitionR :
      (trueCount stream L n : ℝ) +
        (noiseCount stream L n : ℝ) = (n : ℝ) := by
    exact_mod_cast trueCount_add_noiseCount stream L n
  have htrueB : B < trueCount stream L n := by
    have hnBR : (2 * B + 2 : ℕ) ≤ n := hnB
    have hnBR' : (2 * (B : ℝ) + 2 : ℝ) ≤ n := by
      exact_mod_cast hnBR
    have : (B : ℝ) < trueCount stream L n := by
      nlinarith
    exact_mod_cast this
  exact (Nat.not_lt_of_ge
    (trueCount_le_finite_card hinjective hfinite n)) htrueB

/-- The finite-family intersection fact used in the proof of Theorem 5.1:
the stable finite prefix selected by the priority algorithm has an infinite
common core. -/
theorem theorem_5_1_finite_prefix_core
    {stream : GenLimit.Generic.Stream α}
    (hinjective : Function.Injective stream)
    (S : Finset (GenLimit.Generic.Language α))
    (hS : ∀ L, L ∈ S → VanishingNoise stream L) :
    (finiteCommonCore S).Infinite := by
  apply infinite_of_injective_vanishingNoise hinjective
  exact vanishingNoise_finiteCommonCore S hS

end GenLimit.InfiniteContamination
