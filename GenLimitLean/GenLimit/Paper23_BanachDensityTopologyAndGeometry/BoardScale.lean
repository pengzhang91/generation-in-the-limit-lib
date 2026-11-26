import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredDensity

/-! Choose a single slowly increasing volume filter for a sequence of finite
games. A large deficit in board j forces a rectangle in the j-th filter test.
The function depends on the sizes of the boards alone. -/
namespace GenLimit.KleinbergWei.Banach.BoardScale
open Set Filter Finset Real
open scoped Classical ENNReal
noncomputable section

def cap (size : ℕ → ℕ) (j : ℕ) := ⌈exp (size j)⌉₊
private def height (size : ℕ → ℕ) (j : ℕ) :=
  j + (Finset.range (j+1)).sup (cap size)

private theorem high (size : ℕ → ℕ) (V : ℕ) : ∃ j, V ≤ height size j :=
  ⟨V,Nat.le_add_right ..⟩

def scale (size : ℕ → ℕ) (V : ℕ) : ℝ := (Nat.find (high size V) : ℝ) + 1

theorem positive (size : ℕ → ℕ) (V : ℕ) : 0 < scale size V := by unfold scale; positivity

theorem monotone (size : ℕ → ℕ) : Monotone (scale size) := by
  intro a b ab
  have le := Nat.find_min' (high size a) (ab.trans (Nat.find_spec (high size b)))
  unfold scale; exact_mod_cast Nat.add_le_add_right le 1

theorem grows (size : ℕ → ℕ) : Tendsto (scale size) atTop atTop := by
  apply tendsto_atTop.mpr
  intro a
  obtain ⟨k,large⟩ := exists_nat_gt a
  let M := (Finset.range (k+1)).sup (height size)
  apply eventually_atTop.mpr
  refine ⟨M+1,fun v hv => ?_⟩
  have beyond : k ≤ Nat.find (high size v) := by
    by_contra! small
    have le : height size (Nat.find (high size v)) ≤ M := Finset.le_sup
      (Finset.mem_range.mpr (show Nat.find (high size v) < k+1 by omega))
    have := Nat.find_spec (high size v); omega
  have bd : (k:ℝ) ≤ Nat.find (high size v) := by exact_mod_cast beyond
  unfold scale; linarith

theorem small (size : ℕ → ℕ) (j V : ℕ) (bounded : log (V:ℝ) ≤ size j) (pos : 0 < V) :
    scale size V ≤ (j:ℝ)+1 := by
  have le : (V:ℝ) ≤ exp (size j) := (Real.log_le_iff_le_exp (by exact_mod_cast pos)).mp bounded
  have lc : V ≤ cap size j := by exact_mod_cast le.trans (Nat.le_ceil _)
  have top : cap size j ≤ (Finset.range (j+1)).sup (cap size) :=
    Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self j))
  have bound : V ≤ height size j := lc.trans (top.trans (Nat.le_add_left ..))
  unfold scale
  exact add_le_add_right (by exact_mod_cast Nat.find_min' (high size V) bound) _

/-- A deficit of (j+1)²(1+log V) forces both a high filter score and a
strictly subcritical output ratio. All rectangles use the same filter. -/
theorem admissible_of_loss {d} (P : Set (Lattice d)) (size : ℕ → ℕ) (n j : ℕ)
    (large : n + 2^d ≤ j) (l u : Lattice d) (widths : ∀ i, l i < u i)
    {a : ℝ} (upper : a ≤ 1) (m : (Rectangles.box P l u).card ≤ size j) {hits : ℕ}
    (loss : (hits:ℝ) < a*((Rectangles.box P l u).card:ℝ) -
        ((j:ℝ)+1)^2*(1+log (geometricVolume l u))) :
    admissibleBox (scale size) P n (l,u) ∧
      (hits:ℝ) < a*(Rectangles.box P l u).card := by
  let V := geometricVolume l u
  let mass := (Rectangles.box P l u).card
  have vp : 0 < V := Finset.prod_pos (fun i _ => by
    have h := widths i; change 0 < (u i-l i).toNat; omega)
  have ln : 0 ≤ log V := Real.log_nonneg (by exact_mod_cast vp)
  have J : 1 ≤ (j:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) j]
  have sq : (j:ℝ)+1 ≤ ((j:ℝ)+1)^2 := by nlinarith
  have coef : a*(mass:ℝ) ≤ mass := by
    simpa using mul_le_mul_of_nonneg_right upper (Nat.cast_nonneg (α:=ℝ) mass)
  change (hits:ℝ) < a*(mass:ℝ)-((j:ℝ)+1)^2*(1+log V) at loss
  have paid : ((j:ℝ)+1)^2*(1+log V) < (mass:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) hits]
  have more : (j:ℝ)+1 < mass := by nlinarith only [paid,sq,mul_nonneg (sq_nonneg ((j:ℝ)+1)) ln]
  have two : 2 ≤ V := by
    have card := card_le_geometricVolume P widths
    change mass ≤ 2^d * V at card
    have jm : j+1 < mass := by exact_mod_cast more
    by_contra! h
    rw [show V=1 by omega,Nat.mul_one] at card; omega
  have lp : 0 < log V := Real.log_pos (by exact_mod_cast (show 1 < V by omega))
  have log_le : log V ≤ size j := by
    have le : (mass:ℝ) ≤ size j := by exact_mod_cast m
    have oneSq : 1 ≤ ((j:ℝ)+1)^2 := J.trans sq
    nlinarith only [le,paid,mul_le_mul_of_nonneg_right oneSq ln,oneSq]
  have scale_le := small size j V log_le vp
  have score : (n:ℝ)*scale size V ≤ ((j:ℝ)+1)^2 := by
    rw [pow_two]
    apply mul_le_mul _ scale_le (positive ..).le (by positivity)
    exact_mod_cast (show n ≤ j+1 from ((Nat.le_add_right n (2^d)).trans large).trans (Nat.le_succ j))
  refine ⟨⟨widths,two,positive ..,(le_div_iff₀ (mul_pos (positive ..) lp)).mpr ?_⟩,?_⟩
  · change (n:ℝ)*(scale size V*log V) ≤ mass
    nlinarith only [paid,mul_le_mul_of_nonneg_right score ln,sq_nonneg ((j:ℝ)+1)]
  · linarith only [loss,mul_nonneg (sq_nonneg ((j:ℝ)+1)) (show 0 ≤ 1+log V by linarith)]

end
end GenLimit.KleinbergWei.Banach.BoardScale
