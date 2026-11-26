import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ChainRows
import Mathlib.Data.Nat.Pairing
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A concrete unbounded collection of chains for P23 Theorem 5.5.
The row heights at least double. Each row has its own arbitrary increasing
sequence of horizontal positions, and each target can omit any of them. -/
namespace GenLimit.KleinbergWei.Banach.LacunaryRows
open Finset Set Filter Real
open scoped Classical ENNReal
noncomputable section

def point (height : ℕ → ℕ) (horizontal : ℕ → ℕ → ℤ) (n : ℕ) : Lattice 2 :=
  ![horizontal (Nat.unpair n).2 (Nat.unpair n).1, (height (Nat.unpair n).2:ℤ)]

private def row (n : ℕ) := (Nat.unpair n).2

private theorem row_order (height : ℕ → ℕ) {horizontal : ℕ → ℕ → ℤ}
    (inc : ∀ k, StrictMono (horizontal k)) : ChainRows.Ordered (point height horizontal) row := by
  intro x y same le
  change (Nat.unpair x).2 = (Nat.unpair y).2 at same
  have first : (Nat.unpair x).1 ≤ (Nat.unpair y).1 := by
    by_contra! reversed
    have bad := Nat.pair_lt_pair_left (Nat.unpair y).2 reversed
    rw [Nat.pair_unpair,←same,Nat.pair_unpair] at bad
    omega
  intro i; fin_cases i
  · change horizontal (Nat.unpair x).2 _ ≤ horizontal (Nat.unpair y).2 _
    rw [same]
    exact (inc _).monotone first
  · change (height (Nat.unpair x).2:ℤ) ≤ height (Nat.unpair y).2
    rw [same]

private theorem injective {height : ℕ → ℕ} (strict : StrictMono height)
    {horizontal : ℕ → ℕ → ℤ} (inc : ∀ k, StrictMono (horizontal k)) :
    Function.Injective (point height horizontal) := by
  intro x y eq
  have coord : (height (Nat.unpair x).2:ℤ) = height (Nat.unpair y).2 := congrFun eq 1
  have second : height (Nat.unpair x).2 = height (Nat.unpair y).2 := by exact_mod_cast coord
  have same := strict.injective second
  have first : horizontal (Nat.unpair x).2 (Nat.unpair x).1 =
      horizontal (Nat.unpair y).2 (Nat.unpair y).1 := congrFun eq 0
  rw [same] at first
  have ord := (inc _).injective first
  rw [←Nat.pair_unpair x,←Nat.pair_unpair y,ord,same]

private theorem few_rows (height : ℕ → ℕ) (pos : ∀ k, 0 < height k)
    (doubles : ∀ k, 2 * height k ≤ height (k+1)) (horizontal : ℕ → ℕ → ℤ) :
    ChainRows.LogarithmicallyManyRows (point height horizontal) row := by
  refine ⟨3,by norm_num,fun D l u wide => ?_⟩
  let J := (D.filter (fun x => point height horizontal x ∈ Finset.Icc l u)).image row
  let V := geometricVolume l u
  have width : (u 1-l 1).toNat ≤ V := by
    simp only [V,geometricVolume,Fin.prod_univ_two]
    exact Nat.le_mul_of_pos_left _ (by have := wide 0; omega)
  have vp : 0 < V := by have := wide 1; omega
  have vp' : (1:ℝ) ≤ V := by exact_mod_cast vp
  have ln := Real.log_nonneg vp'
  change (J.card:ℝ) ≤ 3*(1+log (V:ℝ))
  by_cases ne : J.Nonempty
  · let a := J.min' ne
    let b := J.max' ne
    have ab : a ≤ b := J.min'_le _ (J.max'_mem ne)
    have inside {k} (mem : k ∈ J) : l 1 ≤ (height k:ℤ) ∧ (height k:ℤ) ≤ u 1 := by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp mem
      obtain ⟨lo,up⟩ := mem_Icc.mp (mem_filter.mp hx).2
      exact ⟨lo 1,up 1⟩
    have scaled (t : ℕ) : 2^t + height a ≤ height (a+t) + 1 := by
      induction t with
      | zero => simp [Nat.add_comm]
      | succ t ih =>
        rw [pow_succ,←Nat.add_assoc a t 1]
        have := doubles (a+t)
        have := pos a
        omega
    have grow := scaled (b-a)
    rw [Nat.add_sub_of_le ab] at grow
    have gap : (2:ℝ)^(b-a) ≤ V+1 := by
      have cx : (2:ℤ)^(b-a) + height a ≤ height b + 1 := by exact_mod_cast grow
      have lo := (inside (J.min'_mem ne)).1
      have hi := (inside (J.max'_mem ne)).2
      change l 1 ≤ (height a:ℤ) at lo
      change (height b:ℤ) ≤ u 1 at hi
      have side : (u 1-l 1:ℤ) ≤ (V:ℤ) := by omega
      exact_mod_cast (show (2:ℤ)^(b-a) ≤ V+1 by omega)
    have logGap := Real.log_le_log (by positivity) gap
    rw [Real.log_pow] at logGap
    have vol := Real.log_le_log (by positivity : 0 < (V:ℝ)+1) (show (V:ℝ)+1 ≤ 2*V by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at vol
    have span : J ⊆ Finset.Icc a b := fun x hx => mem_Icc.mpr ⟨J.min'_le _ hx,J.le_max' _ hx⟩
    have size : J.card ≤ (b-a)+1 := by
      have diff := card_le_card span
      rw [Nat.card_Icc] at diff
      omega
    have bound : (J.card:ℝ) ≤ (b-a:ℕ)+1 := by exact_mod_cast size
    have half : (1/2:ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
    have one : log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith [mul_le_mul_of_nonneg_left half (Nat.cast_nonneg (α:=ℝ) (b-a))]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp ne,Finset.card_empty,Nat.cast_zero]; linarith

/-- Exact half on every target of a finite-rank family on lacunary rows,
even when both its physical and its within-grid occupancy tend to zero. -/
theorem exact_half (height : ℕ → ℕ) (positive : 0 < height 0)
    (doubles : ∀ k, 2 * height k ≤ height (k+1)) (horizontal : ℕ → ℕ → ℤ)
    (inc : ∀ k, StrictMono (horizontal k)) (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) (f : ℕ → ℝ)
    (grows : Tendsto f atTop atTop) :
    let e := point height horizontal
    ∃ A : List (Lattice 2) → Lattice 2, ∀ z (s : ℕ → Lattice 2), range s = e '' C z →
      cubeValid A s (e '' C z) ∧
      ENNReal.ofReal (1/2) ≤ filteredRectangularDensity f (range (cubePlay A s)) (e '' C z) := by
  have pos (k) : 0 < height k := by
    induction k with
    | zero => exact positive
    | succ k ih => have := doubles k; omega
  have strict : StrictMono height := strictMono_nat_of_lt_succ fun k => by
    have := pos k; have := doubles k; omega
  exact ChainRows.exact_half _ (injective strict inc) row (row_order height inc)
    (few_rows height pos doubles horizontal) C inf rank f grows

end
end GenLimit.KleinbergWei.Banach.LacunaryRows
