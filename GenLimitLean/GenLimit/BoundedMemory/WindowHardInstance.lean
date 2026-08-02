import GenLimit.BoundedMemory.DistinctWindows
import GenLimit.BoundedMemory.MinimaxClosure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Sliding-window Sperner hard instance and minimax closure

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Section 4.2.

This module formalizes Lemma 4.12 with its strong quantifier order: the hard
family, target, and repetition-free exact presentation are fixed before the
window width and successful generator are chosen.  It then proves the exact
outer-`limsup` minimax closure in Theorem 4.10.

The source indexes a width-`W` window by its final position, while
`DistinctWindows` indexes it by its first position.  These formulations differ
by the fixed shift `W - 1`, so they are equivalent for all eventual statements
and for the outer run `limsup`.
-/

namespace GenLimit.BoundedMemory

open Filter
open scoped Topology
open GenLimit.KleinbergWei

/-! ## Sparse square positions and the density-order involution -/

/-- Perfect-square positions, including zero. -/
def WindowSquare (t : ℕ) : Prop :=
  ∃ q, q * q = t

/-- The complementary separator positions. -/
def WindowNonSquare (t : ℕ) : Prop :=
  ¬ WindowSquare t

noncomputable local instance : DecidablePred WindowSquare :=
  Classical.decPred _

noncomputable local instance : DecidablePred WindowNonSquare :=
  Classical.decPred _

theorem windowSquare_iff_sqrt (t : ℕ) :
    WindowSquare t ↔ Nat.sqrt t * Nat.sqrt t = t :=
  Nat.exists_mul_self t

@[simp] theorem windowSquare_mul_self (q : ℕ) :
    WindowSquare (q * q) :=
  ⟨q, rfl⟩

/-- A canonical nonsquare strictly between `(m+1)²` and `(m+2)²`. -/
def betweenWindowSquares (m : ℕ) : ℕ :=
  (m + 1) * (m + 1) + (m + 1)

theorem betweenWindowSquares_nonsquare (m : ℕ) :
    WindowNonSquare (betweenWindowSquares m) := by
  unfold WindowNonSquare WindowSquare betweenWindowSquares
  apply Nat.not_exists_sq (m := m + 1)
  · nlinarith
  · nlinarith

theorem betweenWindowSquares_strictMono :
    StrictMono betweenWindowSquares := by
  apply strictMono_nat_of_lt_succ
  intro m
  simp only [betweenWindowSquares]
  nlinarith

theorem windowNonSquare_infinite :
    {t : ℕ | WindowNonSquare t}.Infinite := by
  have hrange :
      (Set.range betweenWindowSquares).Infinite :=
    Set.infinite_range_of_injective
      betweenWindowSquares_strictMono.injective
  exact hrange.mono (by
    rintro _ ⟨m, rfl⟩
    exact betweenWindowSquares_nonsquare m)

/-- Swap square and nonsquare positions in increasing order.

Squares are sent to the correspondingly ranked nonsquares, while a
nonsquare is sent to the square of its rank among nonsquares. -/
noncomputable def windowDensityOrder (t : ℕ) : ℕ :=
  if WindowSquare t then
    Nat.nth WindowNonSquare (Nat.sqrt t)
  else
    let q := Nat.count WindowNonSquare t
    q * q

theorem windowDensityOrder_involutive (t : ℕ) :
    windowDensityOrder (windowDensityOrder t) = t := by
  classical
  by_cases ht : WindowSquare t
  · rw [show windowDensityOrder t =
        Nat.nth WindowNonSquare (Nat.sqrt t) by
      simp [windowDensityOrder, ht]]
    have hnonsquare :
        WindowNonSquare
          (Nat.nth WindowNonSquare (Nat.sqrt t)) :=
      Nat.nth_mem_of_infinite windowNonSquare_infinite _
    rw [windowDensityOrder, if_neg hnonsquare]
    rw [Nat.count_nth_of_infinite windowNonSquare_infinite]
    exact (windowSquare_iff_sqrt t).mp ht
  · rw [show windowDensityOrder t =
        Nat.count WindowNonSquare t * Nat.count WindowNonSquare t by
      simp [windowDensityOrder, ht]]
    rw [windowDensityOrder, if_pos
      (windowSquare_mul_self (Nat.count WindowNonSquare t))]
    simp only [Nat.sqrt_eq]
    exact Nat.nth_count ht

theorem windowDensityOrder_injective :
    Function.Injective windowDensityOrder :=
  fun a b h => by
    simpa only [windowDensityOrder_involutive] using
      congrArg windowDensityOrder h

theorem windowDensityOrder_surjective :
    Function.Surjective windowDensityOrder :=
  fun t => ⟨windowDensityOrder t, windowDensityOrder_involutive t⟩

/-- Density ordering for the hard target. -/
noncomputable def windowHardTargetOrder : OrderedLanguage where
  carrier := Set.univ
  enumeration := windowDensityOrder
  enumeration_injective := windowDensityOrder_injective
  range_enumeration := by
    exact Set.range_eq_univ.mpr windowDensityOrder_surjective

/-- The common, canonically zero-density separator. -/
def windowSeparator : Set ℕ :=
  {x | WindowNonSquare x}

/-- Positive piece `i`: squares whose square root has residue `i`. -/
def windowPositivePiece {N : ℕ} (i : Fin N) : Set ℕ :=
  {x | WindowSquare x ∧ Nat.sqrt x % N = i.1}

@[simp] theorem windowDensityOrder_mem_separator_iff (t : ℕ) :
    windowDensityOrder t ∈ windowSeparator ↔ WindowSquare t := by
  classical
  by_cases ht : WindowSquare t
  · simp only [windowDensityOrder, ht, if_pos]
    have hnonsquare :
        WindowNonSquare
          (Nat.nth WindowNonSquare (Nat.sqrt t)) :=
      Nat.nth_mem_of_infinite windowNonSquare_infinite _
    have hnotSquare :
        ¬ WindowSquare
          (Nat.nth WindowNonSquare (Nat.sqrt t)) :=
      hnonsquare
    simp [windowSeparator, WindowNonSquare, hnotSquare]
  · simp only [windowDensityOrder, ht]
    simp [windowSeparator, WindowNonSquare, WindowSquare]

@[simp] theorem windowDensityOrder_mem_positivePiece_iff
    {N : ℕ} (i : Fin N) (t : ℕ) :
    windowDensityOrder t ∈ windowPositivePiece i ↔
      WindowNonSquare t ∧
        Nat.count WindowNonSquare t % N = i.1 := by
  classical
  by_cases ht : WindowSquare t
  · simp only [windowDensityOrder, ht, if_pos]
    have hnonsquare :
        WindowNonSquare
          (Nat.nth WindowNonSquare (Nat.sqrt t)) :=
      Nat.nth_mem_of_infinite windowNonSquare_infinite _
    have hnotSquare :
        ¬ WindowSquare
          (Nat.nth WindowNonSquare (Nat.sqrt t)) :=
      hnonsquare
    simp [windowPositivePiece, hnotSquare, ht, WindowNonSquare]
  · simp only [windowDensityOrder, ht]
    simp [windowPositivePiece, ht, WindowNonSquare]

theorem windowHardTarget_prefixCount_separator (n : ℕ) :
    windowHardTargetOrder.prefixCount windowSeparator n =
      Nat.count WindowSquare n := by
  classical
  unfold OrderedLanguage.prefixCount
  rw [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext t
  simp [windowHardTargetOrder]

theorem count_windowSquare_le_sqrt_add_one (n : ℕ) :
    Nat.count WindowSquare n ≤ Nat.sqrt n + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let squares := (Finset.range n).filter WindowSquare
  have hinj :
      Set.InjOn Nat.sqrt (squares : Set ℕ) := by
    intro a ha b hb hab
    have haSq : WindowSquare a := (Finset.mem_filter.mp ha).2
    have hbSq : WindowSquare b := (Finset.mem_filter.mp hb).2
    calc
      a = Nat.sqrt a * Nat.sqrt a :=
        ((windowSquare_iff_sqrt a).mp haSq).symm
      _ = Nat.sqrt b * Nat.sqrt b := by rw [hab]
      _ = b := (windowSquare_iff_sqrt b).mp hbSq
  have hcard :
      squares.card = (squares.image Nat.sqrt).card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hinj ha hb hab
  rw [show ((Finset.range n).filter WindowSquare) = squares by rfl,
    hcard]
  calc
    (squares.image Nat.sqrt).card ≤
        (Finset.range (Nat.sqrt n + 1)).card := by
      apply Finset.card_le_card
      intro q hq
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_range]
      have htn : t < n :=
        Finset.mem_range.mp (Finset.mem_filter.mp ht).1
      exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt htn.le)
    _ = Nat.sqrt n + 1 := Finset.card_range _

theorem tendsto_natSqrtCast_atTop :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨m : ℕ, hm : b ≤ m⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop (m * m)] with n hn
  have hmsqrt : m ≤ Nat.sqrt n := Nat.le_sqrt.mpr hn
  exact hm.trans (by exact_mod_cast hmsqrt)

theorem tendsto_sqrt_add_one_div :
    Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / (n : ℝ))
      atTop (𝓝 0) := by
  have hsqrtInv :
      Tendsto (fun n : ℕ => ((Nat.sqrt n : ℝ))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natSqrtCast_atTop
  have hnInv :
      Tendsto (fun n : ℕ => ((n : ℝ))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inverse_atTop_nhds_zero_nat
  have hnonneg :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ ((Nat.sqrt n : ℝ) + 1) / (n : ℝ) :=
    Filter.Eventually.of_forall fun n => by positivity
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ((Nat.sqrt n : ℝ) + 1) / (n : ℝ) ≤
          ((Nat.sqrt n : ℝ))⁻¹ + ((n : ℝ))⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsqrtPosNat : 0 < Nat.sqrt n := by
      rw [Nat.sqrt_pos]
      omega
    have hsqrtPos : (0 : ℝ) < Nat.sqrt n := by
      exact_mod_cast hsqrtPosNat
    have hsquare :
        (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n := by
      exact_mod_cast Nat.sqrt_le n
    have hmain :
        (Nat.sqrt n : ℝ) / n ≤
          ((Nat.sqrt n : ℝ))⁻¹ := by
      rw [div_le_iff₀ hnpos, inv_mul_eq_div,
        le_div_iff₀ hsqrtPos]
      exact hsquare
    rw [add_div]
    simpa only [one_div] using
      add_le_add hmain
        (le_rfl : (n : ℝ)⁻¹ ≤ (n : ℝ)⁻¹)
  apply squeeze_zero' hnonneg hbound
  simpa using hsqrtInv.add hnInv

theorem windowSeparator_upperDensity :
    windowHardTargetOrder.upperDensity windowSeparator = 0 := by
  have hratio (n : ℕ) :
      windowHardTargetOrder.prefixRatio windowSeparator n ≤
        ((Nat.sqrt n : ℝ) + 1) / n := by
    by_cases hn : n = 0
    · simp [hn]
    · rw [OrderedLanguage.prefixRatio, if_neg hn,
        windowHardTarget_prefixCount_separator]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast count_windowSquare_le_sqrt_add_one n)
        (Nat.cast_nonneg n)
  have htendsto :
      Tendsto
        (windowHardTargetOrder.prefixRatio windowSeparator)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall
        (windowHardTargetOrder.prefixRatio_nonneg windowSeparator)
    · exact Filter.Eventually.of_forall hratio
    · exact tendsto_sqrt_add_one_div
  exact htendsto.limsup_eq

/-! ## Positive-density square pieces -/

theorem windowHardTarget_prefixCount_positivePiece_le
    {N : ℕ} (_hN : 0 < N) (i : Fin N) (n : ℕ) :
    windowHardTargetOrder.prefixCount (windowPositivePiece i) n ≤
      spernerTargetOrder.prefixCount (roundRobinPiece i) n := by
  classical
  let source :=
    (Finset.range n).filter fun t =>
      windowDensityOrder t ∈ windowPositivePiece i
  let target :=
    (Finset.range n).filter fun q => q % N = i.1
  let rank : ℕ → ℕ := fun t => Nat.count WindowNonSquare t
  have hrankInj :
      Set.InjOn rank (source : Set ℕ) := by
    intro a ha b hb hab
    have haInfo :=
      (windowDensityOrder_mem_positivePiece_iff i a).mp
        (Finset.mem_filter.mp ha).2
    have hbInfo :=
      (windowDensityOrder_mem_positivePiece_iff i b).mp
        (Finset.mem_filter.mp hb).2
    exact Nat.count_injective haInfo.1 hbInfo.1 hab
  have hcard :
      source.card = (source.image rank).card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hrankInj ha hb hab
  have hsubset : source.image rank ⊆ target := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    have htRange : t < n :=
      Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have htInfo :=
      (windowDensityOrder_mem_positivePiece_iff i t).mp
        (Finset.mem_filter.mp ht).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, htInfo.2⟩
    exact (Nat.count_le WindowNonSquare).trans_lt htRange
  have hfinal : source.card ≤ target.card := by
    rw [hcard]
    exact Finset.card_le_card hsubset
  have hsourceEq :
      windowHardTargetOrder.prefixCount (windowPositivePiece i) n =
        source.card := by
    unfold OrderedLanguage.prefixCount
    apply congrArg Finset.card
    ext t
    simp [source, windowHardTargetOrder]
  have htargetEq :
      spernerTargetOrder.prefixCount (roundRobinPiece i) n =
        target.card := by
    unfold OrderedLanguage.prefixCount
    apply congrArg Finset.card
    ext q
    simp [target, spernerTargetOrder, roundRobinPiece]
  rw [hsourceEq, htargetEq]
  exact hfinal

theorem windowHardTarget_prefixRatio_positivePiece_le
    {N : ℕ} (hN : 0 < N) (i : Fin N) (n : ℕ) :
    windowHardTargetOrder.prefixRatio (windowPositivePiece i) n ≤
      spernerTargetOrder.prefixRatio (roundRobinPiece i) n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [OrderedLanguage.prefixRatio, hn, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast
        windowHardTarget_prefixCount_positivePiece_le hN i n)
      (Nat.cast_nonneg n)

theorem windowPositivePiece_upperDensity_le
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    windowHardTargetOrder.upperDensity (windowPositivePiece i) ≤
      1 / (N : ℝ) := by
  unfold OrderedLanguage.upperDensity
  apply (Filter.limsup_le_limsup
    (Filter.Eventually.of_forall
      (windowHardTarget_prefixRatio_positivePiece_le hN i))
    (isCoboundedUnder_le_of_le atTop
      (fun n =>
        windowHardTargetOrder.prefixRatio_nonneg
          (windowPositivePiece i) n))
    (isBoundedUnder_of
      ⟨1, fun n =>
        spernerTargetOrder.prefixRatio_le_one
          (roundRobinPiece i) n⟩)).trans_eq
  exact roundRobinPiece_upperDensity hN i

theorem windowSeparator_union_positivePiece_upperDensity_le
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    windowHardTargetOrder.upperDensity
        (windowSeparator ∪ windowPositivePiece i) ≤
      1 / (N : ℝ) := by
  calc
    windowHardTargetOrder.upperDensity
        (windowSeparator ∪ windowPositivePiece i) ≤
        windowHardTargetOrder.upperDensity windowSeparator +
          windowHardTargetOrder.upperDensity
            (windowPositivePiece i) :=
      orderedUpperDensity_union_le windowHardTargetOrder _ _
    _ ≤ 0 + 1 / (N : ℝ) := by
      gcongr
      · exact le_of_eq windowSeparator_upperDensity
      · exact windowPositivePiece_upperDensity_le hN i
    _ = 1 / (N : ℝ) := zero_add _

theorem windowPositivePiece_infinite
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    (windowPositivePiece i).Infinite := by
  let root : ℕ → ℕ := fun q => N * q + i.1
  let squareRoot : ℕ → ℕ := fun q => root q * root q
  have hroot : Function.Injective root := by
    intro q r hqr
    apply Nat.eq_of_mul_eq_mul_left hN
    exact Nat.add_right_cancel hqr
  have hsquareRoot : Function.Injective squareRoot := by
    intro q r hqr
    apply hroot
    dsimp [squareRoot] at hqr
    nlinarith
  apply (Set.infinite_range_of_injective hsquareRoot).mono
  rintro x ⟨q, rfl⟩
  change WindowSquare (root q * root q) ∧
    Nat.sqrt (root q * root q) % N = i.1
  refine ⟨windowSquare_mul_self _, ?_⟩
  rw [Nat.sqrt_eq]
  exact blockNumber_residue N q i

theorem windowPositivePieces_pairwiseDisjoint
    (N : ℕ) :
    ∀ i j : Fin N, i ≠ j →
      Disjoint (windowPositivePiece i) (windowPositivePiece j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  apply hij
  apply Fin.ext
  exact hxi.2.symm.trans hxj.2

theorem windowSeparator_disjoint_positivePiece
    {N : ℕ} (i : Fin N) :
    Disjoint windowSeparator (windowPositivePiece i) := by
  rw [Set.disjoint_left]
  intro x hxZ hxP
  exact hxZ hxP.1

theorem windowSeparator_union_positivePieces
    {N : ℕ} (hN : 0 < N) :
    windowSeparator ∪
        (⋃ i : Fin N, windowPositivePiece i) =
      (Set.univ : Set ℕ) := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : WindowSquare x
  · apply Or.inr
    let i : Fin N :=
      ⟨Nat.sqrt x % N, Nat.mod_lt _ hN⟩
    exact Set.mem_iUnion.mpr ⟨i, hx, rfl⟩
  · exact Or.inl hx

/-! ## The middle-layer side languages -/

/-- Side language `j`: the common separator together with the positive
pieces whose middle-layer signatures contain `j`. -/
def windowHardLanguage (n : ℕ) (j : Fin n) : Set ℕ :=
  windowSeparator ∪
    ⋃ i : Fin (Nat.choose n (n / 2)),
      if j ∈ middleSignature n i then windowPositivePiece i else ∅

theorem mem_windowHardLanguage_iff
    (n : ℕ) (j : Fin n) (x : ℕ) :
    x ∈ windowHardLanguage n j ↔
      x ∈ windowSeparator ∨
        ∃ i : Fin (Nat.choose n (n / 2)),
          x ∈ windowPositivePiece i ∧
            j ∈ middleSignature n i := by
  constructor
  · intro hx
    rcases hx with hxZ | hxSide
    · exact Or.inl hxZ
    · right
      simp only [Set.mem_iUnion] at hxSide
      obtain ⟨i, hi⟩ := hxSide
      by_cases hji : j ∈ middleSignature n i
      · exact ⟨i, by simpa [hji] using hi, hji⟩
      · simp [hji] at hi
  · rintro (hxZ | ⟨i, hxi, hji⟩)
    · exact Or.inl hxZ
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      exact ⟨i, by simpa [hji] using hxi⟩

theorem windowPositivePiece_subset_hardLanguage
    (n : ℕ) (j : Fin n)
    (i : Fin (Nat.choose n (n / 2)))
    (hji : j ∈ middleSignature n i) :
    windowPositivePiece i ⊆ windowHardLanguage n j := by
  intro x hx
  exact (mem_windowHardLanguage_iff n j x).2
    (Or.inr ⟨i, hx, hji⟩)

theorem windowSeparator_subset_hardLanguage
    (n : ℕ) (j : Fin n) :
    windowSeparator ⊆ windowHardLanguage n j := by
  intro x hx
  exact (mem_windowHardLanguage_iff n j x).2 (Or.inl hx)

theorem windowHardLanguage_infinite
    (n : ℕ) (j : Fin n) :
    (windowHardLanguage n j).Infinite :=
  windowNonSquare_infinite.mono
    (windowSeparator_subset_hardLanguage n j)

/-- The unique positive-piece owner of a square. -/
def windowPieceOwner (n : ℕ) (x : ℕ) :
    Fin (Nat.choose n (n / 2)) :=
  ⟨Nat.sqrt x % Nat.choose n (n / 2),
    Nat.mod_lt _ (middleWidth_pos n)⟩

theorem mem_windowPositivePiece_owner
    (n : ℕ) {x : ℕ} (hx : WindowSquare x) :
    x ∈ windowPositivePiece (windowPieceOwner n x) :=
  ⟨hx, rfl⟩

theorem windowPositivePiece_owner_unique
    (n : ℕ) {x : ℕ}
    {i : Fin (Nat.choose n (n / 2))}
    (hxi : x ∈ windowPositivePiece i) :
    windowPieceOwner n x = i := by
  apply Fin.ext
  exact hxi.2

theorem mem_windowHardLanguage_of_not_separator_iff
    (n : ℕ) (j : Fin n) {x : ℕ}
    (hxZ : x ∉ windowSeparator) :
    x ∈ windowHardLanguage n j ↔
      j ∈ middleSignature n (windowPieceOwner n x) := by
  have hxSquare : WindowSquare x := by
    simpa [windowSeparator, WindowNonSquare] using hxZ
  constructor
  · intro hx
    rcases (mem_windowHardLanguage_iff n j x).1 hx with
      hxSep | ⟨i, hxi, hji⟩
    · exact (hxZ hxSep).elim
    · have hi : windowPieceOwner n x = i :=
        windowPositivePiece_owner_unique n hxi
      simpa [hi] using hji
  · intro hj
    exact windowPositivePiece_subset_hardLanguage n j
      (windowPieceOwner n x) hj
      (mem_windowPositivePiece_owner n hxSquare)

theorem windowHardLanguage_ne_univ
    {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    windowHardLanguage n j ≠ (Set.univ : Set ℕ) := by
  obtain ⟨i, hji⟩ := exists_middleSignature_not_mem hn j
  let x := i.1 * i.1
  have hxPiece : x ∈ windowPositivePiece i := by
    refine ⟨windowSquare_mul_self _, ?_⟩
    simp [x, Nat.mod_eq_of_lt i.isLt]
  have hxNotSep : x ∉ windowSeparator :=
    (windowSeparator_disjoint_positivePiece i).notMem_of_mem_right hxPiece
  intro heq
  have hxLang : x ∈ windowHardLanguage n j := by simp [heq]
  have :=
    (mem_windowHardLanguage_of_not_separator_iff
      n j hxNotSep).1 hxLang
  have howner : windowPieceOwner n x = i :=
    windowPositivePiece_owner_unique n hxPiece
  exact hji (howner ▸ this)

theorem windowHardLanguage_injective
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (windowHardLanguage n) := by
  intro j ell heq
  by_contra hjell
  obtain ⟨i, hji, helli⟩ :=
    exists_middleSignature_mem_not_mem hn hjell
  let x := i.1 * i.1
  have hxPiece : x ∈ windowPositivePiece i := by
    refine ⟨windowSquare_mul_self _, ?_⟩
    simp [x, Nat.mod_eq_of_lt i.isLt]
  have hxj : x ∈ windowHardLanguage n j :=
    windowPositivePiece_subset_hardLanguage n j i hji hxPiece
  have hxell : x ∈ windowHardLanguage n ell := heq ▸ hxj
  have hxNotSep : x ∉ windowSeparator :=
    (windowSeparator_disjoint_positivePiece i).notMem_of_mem_right hxPiece
  have howner : windowPieceOwner n x = i :=
    windowPositivePiece_owner_unique n hxPiece
  exact helli (howner ▸
    (mem_windowHardLanguage_of_not_separator_iff
      n ell hxNotSep).1 hxell)

/-- Target first, followed by all side languages. -/
noncomputable def windowHardFamily (n : ℕ) :
    Fin (n + 1) → Set ℕ :=
  Fin.cases Set.univ (windowHardLanguage n)

@[simp] theorem windowHardFamily_zero (n : ℕ) :
    windowHardFamily n 0 = (Set.univ : Set ℕ) := by
  simp [windowHardFamily]

@[simp] theorem windowHardFamily_succ
    (n : ℕ) (j : Fin n) :
    windowHardFamily n j.succ = windowHardLanguage n j := by
  simp [windowHardFamily]

theorem windowHardFamily_injective
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (windowHardFamily n) := by
  intro a
  refine Fin.cases ?_ (fun j => ?_) a
  · intro b
    refine Fin.cases (fun _ => rfl) (fun ell hab => ?_) b
    exfalso
    exact windowHardLanguage_ne_univ hn ell
      (by simpa using hab.symm)
  · intro b
    refine Fin.cases ?_ (fun ell hab => ?_) b
    · intro hab
      exfalso
      exact windowHardLanguage_ne_univ hn j
        (by simpa using hab)
    · apply congrArg Fin.succ
      apply windowHardLanguage_injective hn
      simpa using hab

theorem windowHardFamily_infinite
    (n : ℕ) :
    ∀ a, (windowHardFamily n a).Infinite := by
  intro a
  refine Fin.cases Set.infinite_univ (fun j => ?_) a
  exact windowHardLanguage_infinite n j

/-! ## Consolidating Lemma 4.11 over a finite family -/

theorem finiteFamily_window_exception
    {m W : ℕ} (hW : 0 < W)
    (langs : Fin m → Set ℕ)
    (hInfinite : ∀ a, (langs a).Infinite)
    (G : WindowSetGenerator ℕ W)
    (hG : ∀ a, IsRepetitionFreeWindowGeneratorOn G (langs a)) :
    ∃ B : Finset ℕ,
      ∀ (a : Fin m) (w : DistinctWindow ℕ W),
        (∀ i, w.1 i ∈ langs a ∧ w.1 i ∉ B) →
          G w ⊆ langs a := by
  classical
  let localBad : Fin m → Finset ℕ := fun a =>
    Classical.choose
      (lemma_4_11_finite_exception hW (hInfinite a) (hG a))
  have hlocal (a : Fin m) :
      (localBad a : Set ℕ) ⊆ langs a ∧
        ∀ w : DistinctWindow ℕ W,
          (∀ i, w.1 i ∈ langs a ∧ w.1 i ∉ localBad a) →
            G w ⊆ langs a :=
    Classical.choose_spec
      (lemma_4_11_finite_exception hW (hInfinite a) (hG a))
  let totalBad := Finset.univ.biUnion localBad
  refine ⟨totalBad, ?_⟩
  intro a w hw
  apply (hlocal a).2 w
  intro i
  refine ⟨(hw i).1, ?_⟩
  intro hi
  apply (hw i).2
  exact Finset.mem_biUnion.mpr
    ⟨a, Finset.mem_univ a, hi⟩

/-! ## Intersections forced by a window signature -/

theorem windowHardIntersection_subset_separator_union_piece
    (n : ℕ)
    (i : Fin (Nat.choose n (n / 2))) :
    {x | ∀ j : Fin n, j ∈ middleSignature n i →
        x ∈ windowHardLanguage n j} ⊆
      windowSeparator ∪ windowPositivePiece i := by
  intro x hx
  by_cases hxZ : x ∈ windowSeparator
  · exact Or.inl hxZ
  · apply Or.inr
    have hsubset :
        middleSignature n i ⊆
          middleSignature n (windowPieceOwner n x) := by
      intro j hji
      exact
        (mem_windowHardLanguage_of_not_separator_iff
          n j hxZ).1 (hx j hji)
    have hi : i = windowPieceOwner n x :=
      middleSignature_eq_of_subset n hsubset
    have hxSquare : WindowSquare x := by
      simpa [windowSeparator, WindowNonSquare] using hxZ
    rw [hi]
    exact mem_windowPositivePiece_owner n hxSquare

theorem windowHardIntersection_all_subset_separator
    {n : ℕ} (hn : 2 ≤ n) :
    {x | ∀ j : Fin n, x ∈ windowHardLanguage n j} ⊆
      windowSeparator := by
  intro x hx
  by_contra hxZ
  have hxZ' : x ∉ windowSeparator := hxZ
  let owner := windowPieceOwner n x
  have hcard :
      (middleSignature n owner).card <
        (Finset.univ : Finset (Fin n)).card := by
    rw [middleSignature_card]
    simp
    omega
  obtain ⟨j, _, hj⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  exact hj
    ((mem_windowHardLanguage_of_not_separator_iff
      n j hxZ').1 (hx j))

/-! ## Square-sparse geometry of the fixed identity presentation -/

def identityWindow (start W : ℕ) : DistinctWindow ℕ W :=
  windowAt id (fun _ _ h => h) start W

@[simp] theorem identityWindow_apply
    (start W : ℕ) (i : Fin W) :
    (identityWindow start W).1 i = start + i := rfl

theorem square_window_index_unique
    {start W : ℕ} (hstart : W * W ≤ start)
    {i j : Fin W}
    (hi : WindowSquare (start + i))
    (hj : WindowSquare (start + j)) :
    i = j := by
  have impossible {a b : Fin W}
      (ha : WindowSquare (start + a))
      (hb : WindowSquare (start + b))
      (hab : (a : ℕ) < b) : False := by
    have hpos :
        start + (a : ℕ) < start + (b : ℕ) :=
      Nat.add_lt_add_left hab start
    have haEq :
        Nat.sqrt (start + a) * Nat.sqrt (start + a) =
          start + a :=
      (windowSquare_iff_sqrt _).mp ha
    have hbEq :
        Nat.sqrt (start + b) * Nat.sqrt (start + b) =
          start + b :=
      (windowSquare_iff_sqrt _).mp hb
    have hroot :
        Nat.sqrt (start + a) < Nat.sqrt (start + b) := by
      apply Nat.mul_self_lt_mul_self_iff.mp
      calc
        Nat.sqrt (start + a) * Nat.sqrt (start + a) =
            start + a := haEq
        _ < start + b := hpos
        _ = Nat.sqrt (start + b) * Nat.sqrt (start + b) :=
          hbEq.symm
    have hWroot : W ≤ Nat.sqrt (start + a) := by
      apply Nat.le_sqrt.mpr
      exact hstart.trans (Nat.le_add_right start a)
    have hbBound : (b : ℕ) < W := b.isLt
    have hnext :
        Nat.sqrt (start + a) + 1 ≤ Nat.sqrt (start + b) :=
      Nat.succ_le_iff.mpr hroot
    nlinarith
  apply Fin.ext
  by_contra hij
  rcases lt_or_gt_of_ne hij with hijlt | hijgt
  · exact (impossible hi hj hijlt).elim
  · exact (impossible hj hi hijgt).elim

theorem identityWindow_signature_geometry
    {start W : ℕ} (hstart : W * W ≤ start) :
    (∀ i : Fin W, (identityWindow start W).1 i ∈ windowSeparator) ∨
      ∃ owner : Fin (Nat.choose n (n / 2)),
        ∀ i : Fin W,
          (identityWindow start W).1 i ∈ windowSeparator ∨
            (identityWindow start W).1 i ∈
              windowPositivePiece owner := by
  classical
  by_cases hall :
      ∀ i : Fin W, (identityWindow start W).1 i ∈ windowSeparator
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨pivot, hpivot⟩ := hall
    have hpivotSquare :
        WindowSquare ((identityWindow start W).1 pivot) := by
      simpa [windowSeparator, WindowNonSquare] using hpivot
    let owner :=
      windowPieceOwner n ((identityWindow start W).1 pivot)
    refine ⟨owner, ?_⟩
    intro i
    by_cases hiZ :
        (identityWindow start W).1 i ∈ windowSeparator
    · exact Or.inl hiZ
    · right
      have hiSquare :
          WindowSquare ((identityWindow start W).1 i) := by
        simpa [windowSeparator, WindowNonSquare] using hiZ
      have hipivot : i = pivot := by
        apply square_window_index_unique hstart hiSquare hpivotSquare
      subst i
      exact mem_windowPositivePiece_owner n hpivotSquare

/-! ## Eventual forcing for the fixed presentation -/

/-- Every successful width-`W` generator is eventually forced below the
reciprocal middle-layer width on the fixed identity presentation.

The source indexes a window by its final position.  Here `start` is its first
position; the two eventual formulations differ by the fixed shift `W - 1`. -/
theorem eventually_windowHard_upperDensity_bound
    {n W : ℕ} (hn : 2 ≤ n) (hW : 0 < W)
    (G : WindowSetGenerator ℕ W)
    (hG : ∀ a : Fin (n + 1),
      IsRepetitionFreeWindowGeneratorOn G
        (windowHardFamily n a)) :
    ∃ T, ∀ start, T ≤ start →
      windowHardTargetOrder.upperDensity
          (G (identityWindow start W)) ≤
        1 / (Nat.choose n (n / 2) : ℝ) := by
  classical
  obtain ⟨B, hB⟩ :=
    finiteFamily_window_exception hW
      (windowHardFamily n) (windowHardFamily_infinite n) G hG
  have hid : Function.Injective (id : ℕ → ℕ) :=
    fun _ _ h => h
  obtain ⟨TB, hAvoid⟩ :=
    finitelyRepeating_avoids_finite_set
      (stream := (id : ℕ → ℕ))
      (injective_finitelyRepeating hid) B.finite_toSet
  refine ⟨max TB (W * W), ?_⟩
  intro start hstart
  have hTB : TB ≤ start :=
    (Nat.le_max_left TB (W * W)).trans hstart
  have hgeomStart : W * W ≤ start :=
    (Nat.le_max_right TB (W * W)).trans hstart
  have hnotB (i : Fin W) :
      (identityWindow start W).1 i ∉ B := by
    apply hAvoid (start + i)
    exact hTB.trans (Nat.le_add_right start i)
  rcases identityWindow_signature_geometry
      (n := n) hgeomStart with hall | ⟨owner, howner⟩
  · have hSide (j : Fin n) :
        G (identityWindow start W) ⊆
          windowHardLanguage n j := by
      apply hB j.succ (identityWindow start W)
      intro i
      exact
        ⟨windowSeparator_subset_hardLanguage n j (hall i),
          hnotB i⟩
    have hsubset :
        G (identityWindow start W) ⊆ windowSeparator := by
      intro x hx
      apply windowHardIntersection_all_subset_separator hn
      intro j
      exact hSide j hx
    calc
      windowHardTargetOrder.upperDensity
          (G (identityWindow start W)) ≤
          windowHardTargetOrder.upperDensity windowSeparator :=
        orderedUpperDensity_mono windowHardTargetOrder hsubset
      _ = 0 := windowSeparator_upperDensity
      _ ≤ 1 / (Nat.choose n (n / 2) : ℝ) := by positivity
  · have hSide (j : Fin n)
        (hj : j ∈ middleSignature n owner) :
        G (identityWindow start W) ⊆
          windowHardLanguage n j := by
      apply hB j.succ (identityWindow start W)
      intro i
      refine ⟨?_, hnotB i⟩
      rcases howner i with hiZ | hiPiece
      · exact windowSeparator_subset_hardLanguage n j hiZ
      · exact windowPositivePiece_subset_hardLanguage
          n j owner hj hiPiece
    have hsubset :
        G (identityWindow start W) ⊆
          windowSeparator ∪ windowPositivePiece owner := by
      intro x hx
      apply
        windowHardIntersection_subset_separator_union_piece
          n owner
      intro j hj
      exact hSide j hj hx
    exact
      (orderedUpperDensity_mono
        windowHardTargetOrder hsubset).trans
        (windowSeparator_union_positivePiece_upperDensity_le
          (middleWidth_pos n) owner)

/-! ## Lemma 4.12 -/

/-- Lemma 4.12 with the source's quantifier order.

For each `k`, the family, target, density order, and repetition-free exact
presentation are fixed before the window width and generator are chosen.
The family is represented by an injective `Fin k` indexing, recording that it
has exactly `k` distinct infinite languages. -/
theorem lemma_4_12_single_hard_instance
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (K : OrderedLanguage) (langs : Fin k → Set ℕ)
        (target : Fin k) (stream : ℕ → ℕ)
        (hstream : Function.Injective stream),
      Function.Injective langs ∧
      (∀ a, (langs a).Infinite) ∧
      langs target = K.carrier ∧
      GenLimit.Generic.Presents stream K.carrier ∧
      ∀ (W : ℕ), 0 < W →
        ∀ G : WindowSetGenerator ℕ W,
          (∀ a, IsRepetitionFreeWindowGeneratorOn G (langs a)) →
          ∃ T, ∀ start, T ≤ start →
            K.upperDensity
                (G (windowAt stream hstream start W)) ≤
              1 /
                (Nat.choose (k - 1) ((k - 1) / 2) : ℝ) := by
  cases k with
  | zero => omega
  | succ n =>
      by_cases hn : n = 1
      · subst n
        let hid : Function.Injective (id : ℕ → ℕ) :=
          fun _ _ h => h
        refine
          ⟨spernerTargetOrder, twoHardFamily, 0, id, hid,
            twoHardFamily_injective, twoHardFamily_infinite, rfl, ?_, ?_⟩
        · ext x
          simp [spernerTargetOrder]
        · intro W hW G hG
          refine ⟨0, ?_⟩
          intro start hstart
          simpa using
            orderedUpperDensity_le_one spernerTargetOrder
              (G (windowAt id hid start W))
      · have hn2 : 2 ≤ n := by omega
        let hid : Function.Injective (id : ℕ → ℕ) :=
          fun _ _ h => h
        refine
          ⟨windowHardTargetOrder, windowHardFamily n, 0, id, hid,
            windowHardFamily_injective hn2,
            windowHardFamily_infinite n, rfl, ?_, ?_⟩
        · ext x
          simp [windowHardTargetOrder]
        · intro W hW G hG
          simpa [identityWindow] using
            eventually_windowHard_upperDensity_bound
              hn2 hW G hG

/-! ## The window minimax wrapper -/

/-- The outer `limsup` over start-indexed windows.  This is the paper's run
density after the harmless fixed reindexing from final positions to starts. -/
noncomputable def windowRunUpperDensity
    (K : OrderedLanguage) {W : ℕ}
    (G : WindowSetGenerator ℕ W)
    (stream : ℕ → ℕ) (hstream : Function.Injective stream) : ℝ :=
  limsup
    (fun start =>
      K.upperDensity (G (windowAt stream hstream start W)))
    atTop

/-- The repetition-free, order-robust sliding-window analogue of Definition
9.  A family may tailor its generator; the adversary then chooses its target,
density order, and repetition-free exact presentation. -/
def WindowUpperDensityGuarantee
    (k W : ℕ) (σ : ℝ) : Prop :=
  ∀ (langs : Fin k → Set ℕ),
    Function.Injective langs →
    (∀ a, (langs a).Infinite) →
    ∃ G : WindowSetGenerator ℕ W,
      (∀ a, IsRepetitionFreeWindowGeneratorOn G (langs a)) ∧
      ∀ (target : Fin k) (K : OrderedLanguage),
        K.carrier = langs target →
        ∀ (stream : ℕ → ℕ)
          (hstream : Function.Injective stream),
          GenLimit.Generic.Presents stream K.carrier →
          σ ≤ windowRunUpperDensity K G stream hstream

def windowAdmissibleUpperDensities
    (k W : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩
    {σ | WindowUpperDensityGuarantee k W σ}

noncomputable def windowMinimaxUpperDensity
    (k W : ℕ) : ℝ :=
  sSup (windowAdmissibleUpperDensities k W)

theorem windowRunUpperDensity_le_one
    (K : OrderedLanguage) {W : ℕ}
    (G : WindowSetGenerator ℕ W)
    (stream : ℕ → ℕ) (hstream : Function.Injective stream) :
    windowRunUpperDensity K G stream hstream ≤ 1 := by
  unfold windowRunUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun start =>
        orderedUpperDensity_nonneg' K
          (G (windowAt stream hstream start W)))
  · exact Filter.Eventually.of_forall
      (fun start =>
        orderedUpperDensity_le_one K
          (G (windowAt stream hstream start W)))

theorem windowRunUpperDensity_ge_of_frequently
    (K : OrderedLanguage) {W : ℕ}
    (G : WindowSetGenerator ℕ W)
    (stream : ℕ → ℕ) (hstream : Function.Injective stream)
    {σ : ℝ}
    (hσ : ∃ᶠ start : ℕ in atTop,
      σ ≤ K.upperDensity
        (G (windowAt stream hstream start W))) :
    σ ≤ windowRunUpperDensity K G stream hstream := by
  unfold windowRunUpperDensity
  exact le_limsup_of_frequently_le hσ
    (isBoundedUnder_of
      ⟨1, fun start =>
        orderedUpperDensity_le_one K
          (G (windowAt stream hstream start W))⟩)

theorem windowRunUpperDensity_le_of_eventually
    (K : OrderedLanguage) {W : ℕ}
    (G : WindowSetGenerator ℕ W)
    (stream : ℕ → ℕ) (hstream : Function.Injective stream)
    {σ : ℝ}
    (hσ : ∀ᶠ start : ℕ in atTop,
      K.upperDensity
        (G (windowAt stream hstream start W)) ≤ σ) :
    windowRunUpperDensity K G stream hstream ≤ σ := by
  unfold windowRunUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun start =>
        orderedUpperDensity_nonneg' K
          (G (windowAt stream hstream start W)))
  · exact hσ

/-- Lift the canonical memoryless generator by reading the first entry of
each start-indexed window. -/
noncomputable def canonicalWindowGenerator
    {m W : ℕ} (hW : 0 < W)
    (langs : Fin (m + 1) → Set ℕ) :
    WindowSetGenerator ℕ W where
  output w :=
    canonicalDensityGenerator langs (w.1 ⟨0, hW⟩)
  output_infinite w :=
    canonicalDensityGenerator_infinite langs (w.1 ⟨0, hW⟩)

theorem canonicalWindowGenerator_succeeds
    {m W : ℕ} (hW : 0 < W)
    (langs : Fin (m + 1) → Set ℕ) :
    ∀ a, IsRepetitionFreeWindowGeneratorOn
      (canonicalWindowGenerator hW langs) (langs a) := by
  intro a stream hstream hP
  obtain ⟨T, hT⟩ :=
    canonicalDensityGenerator_succeeds langs
      (langs a) ⟨a, rfl⟩ stream hP
      (injective_finitelyRepeating hstream)
  refine ⟨T, ?_⟩
  intro start hstart
  have hvalid := (hT start hstart).2
  simpa [canonicalWindowGenerator, windowAt] using hvalid

theorem canonicalWindowRunUpperDensity_eq
    {m W : ℕ} (hW : 0 < W)
    (langs : Fin (m + 1) → Set ℕ)
    (K : OrderedLanguage)
    (stream : ℕ → ℕ) (hstream : Function.Injective stream) :
    windowRunUpperDensity K
        (canonicalWindowGenerator hW langs) stream hstream =
      memorylessRunUpperDensity K
        (canonicalDensityGenerator langs) stream := by
  unfold windowRunUpperDensity memorylessRunUpperDensity
  congr 1

theorem windowSpernerValue_guaranteed
    {k W : ℕ} (hk : 1 ≤ k) (hW : 0 < W) :
    WindowUpperDensityGuarantee k W
      (memorylessSpernerValue k) := by
  cases k with
  | zero => omega
  | succ n =>
      intro langs _hInjective hInfinite
      refine
        ⟨canonicalWindowGenerator hW langs,
          canonicalWindowGenerator_succeeds hW langs, ?_⟩
      intro target K hK stream hstream hP
      rw [canonicalWindowRunUpperDensity_eq hW langs]
      apply memorylessRunUpperDensity_ge_of_frequently
      simpa [memorylessSpernerValue] using
        canonicalDensityGenerator_frequently_sperner_dense
          langs target K hK stream hP

theorem windowSpernerValue_admissible
    {k W : ℕ} (hk : 1 ≤ k) (hW : 0 < W) :
    memorylessSpernerValue k ∈
      windowAdmissibleUpperDensities k W :=
  ⟨memorylessSpernerValue_mem_Icc k,
    windowSpernerValue_guaranteed hk hW⟩

theorem windowAdmissibleUpperDensity_le_spernerValue
    {k W : ℕ} (hk : 1 ≤ k) (hW : 0 < W)
    {σ : ℝ}
    (hσ : σ ∈ windowAdmissibleUpperDensities k W) :
    σ ≤ memorylessSpernerValue k := by
  by_cases hkOne : k = 1
  · subst k
    simpa [memorylessSpernerValue] using hσ.1.2
  · have hkTwo : 2 ≤ k := by omega
    obtain
      ⟨K, langs, target, stream, hstream,
        hInjective, hInfinite, hTarget, hP, hHard⟩ :=
      lemma_4_12_single_hard_instance k hkTwo
    obtain ⟨G, hG, hGuarantee⟩ :=
      hσ.2 langs hInjective hInfinite
    obtain ⟨T, hT⟩ := hHard W hW G hG
    have hEventually :
        ∀ᶠ start : ℕ in atTop,
          K.upperDensity
              (G (windowAt stream hstream start W)) ≤
            memorylessSpernerValue k := by
      filter_upwards [eventually_ge_atTop T] with start hstart
      simpa [memorylessSpernerValue] using hT start hstart
    have hRunUpper :
        windowRunUpperDensity K G stream hstream ≤
          memorylessSpernerValue k :=
      windowRunUpperDensity_le_of_eventually
        K G stream hstream hEventually
    have hRunLower :
        σ ≤ windowRunUpperDensity K G stream hstream :=
      hGuarantee target K hTarget.symm stream hstream hP
    exact hRunLower.trans hRunUpper

theorem windowAdmissibleUpperDensities_bddAbove
    (k W : ℕ) :
    BddAbove (windowAdmissibleUpperDensities k W) := by
  refine ⟨1, ?_⟩
  intro σ hσ
  exact hσ.1.2

/-- Theorem 4.10, including the actual supremum and outer run `limsup`, in
the repetition-free start-indexed window model of `DistinctWindows`. -/
theorem theorem_4_10_window_minimax_upper_density
    (k W : ℕ) (hk : 1 ≤ k) (hW : 0 < W) :
    windowMinimaxUpperDensity k W =
      1 /
        (Nat.choose (k - 1) ((k - 1) / 2) : ℝ) := by
  change windowMinimaxUpperDensity k W =
    memorylessSpernerValue k
  unfold windowMinimaxUpperDensity
  apply le_antisymm
  · apply csSup_le
    · exact
        ⟨memorylessSpernerValue k,
          windowSpernerValue_admissible hk hW⟩
    · intro σ hσ
      exact
        windowAdmissibleUpperDensity_le_spernerValue
          hk hW hσ
  · exact le_csSup
      (windowAdmissibleUpperDensities_bddAbove k W)
      (windowSpernerValue_admissible hk hW)

end GenLimit.BoundedMemory
