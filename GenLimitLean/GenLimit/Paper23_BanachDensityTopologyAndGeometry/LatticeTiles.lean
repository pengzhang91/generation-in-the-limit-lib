import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredBoxes

/-! Fixed-scale integer cubes and the number met by an arbitrary rectangle.
All estimates are independent of its location and aspect ratio. -/
namespace GenLimit.KleinbergWei.Banach.LatticeTiles
open Finset
open scoped Classical
noncomputable section

def number {d} (L : ℕ) (x : Lattice d) : Lattice d := fun j => x j / L
def lower {d} (L : ℕ) (k : Lattice d) : Lattice d := fun j => k j * L
def upper {d} (L : ℕ) (k : Lattice d) : Lattice d := fun j => k j * L + L - 1
def cell {d} (L : ℕ) (k : Lattice d) := Finset.Icc (lower L k) (upper L k)
def indices {d} (L : ℕ) (l u : Lattice d) := Finset.Icc (number L l) (number L u)

theorem in_cell {d L} (pos : 0 < L) (x : Lattice d) : x ∈ cell L (number L x) := by
  have hp : (0:ℤ) < L := by exact_mod_cast pos
  exact Finset.mem_Icc.mpr ⟨fun j => Int.ediv_mul_le _ hp.ne',fun j => by
    have h := Int.lt_ediv_add_one_mul_self (x j) hp
    dsimp [upper,number]; linarith⟩

theorem cell_iff {d L} (pos : 0 < L) (x k : Lattice d) : x ∈ cell L k ↔ number L x = k := by
  constructor
  · intro mem
    have hp : (0:ℤ) < L := by exact_mod_cast pos
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp mem
    funext j
    apply le_antisymm
    · apply Int.le_of_lt_add_one
      apply (Int.ediv_lt_iff_lt_mul hp).2
      have h := hi j; dsimp [upper] at h; linarith
    · exact (Int.le_ediv_iff_mul_le hp).2 (lo j)
  · rintro rfl; exact in_cell pos x

theorem number_mem {d L} (pos : 0 < L) {l u x : Lattice d} (hx : x ∈ Finset.Icc l u) :
    number L x ∈ indices L l u := by
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨fun j => Int.ediv_le_ediv (by positivity) (lo j),
    fun j => Int.ediv_le_ediv (by positivity) (hi j)⟩

private theorem width_card {L : ℕ} (hp : 0 < L) {l u : ℤ} (hu : l ≤ u) :
    L * (Finset.Icc (l / L) (u / L)).card ≤ (u-l).toNat+2*L := by
  have pos : (0:ℤ) < L := by exact_mod_cast hp
  have ub := Int.ediv_mul_le u pos.ne'
  have lb := Int.lt_ediv_add_one_mul_self l pos
  have hq : l/(L:ℤ) ≤ u/L := Int.ediv_le_ediv pos hu
  rw [Int.card_Icc]
  have h : (L:ℤ)*(u/L+1-l/L) ≤ u-l+2*L := by linarith
  exact_mod_cast (show (L:ℤ)*(((u/L+1-l/L).toNat:ℕ):ℤ) ≤ (((u-l).toNat:ℕ):ℤ)+2*L by
    rwa [Int.toNat_of_nonneg (by omega),Int.toNat_of_nonneg (by omega)])

/-- The geometric volume with every singleton side given width one. -/
def unitVolume {d} (l u : Lattice d) := ∏ j, max 1 (u j-l j).toNat

theorem unitVolume_eq {d} {l u : Lattice d} (widths : ∀ j, l j < u j) :
    unitVolume l u = geometricVolume l u := by
  unfold unitVolume geometricVolume
  apply Finset.prod_congr rfl
  intro j _
  exact max_eq_right (by have h := widths j; omega)

theorem unitVolume_le_card {d} {l u : Lattice d} (widths : l ≤ u) :
    unitVolume l u ≤ (Finset.Icc l u).card := by
  rw [Pi.card_Icc]
  apply Finset.prod_le_prod'
  intro j _
  rw [Int.card_Icc]
  have h : l j ≤ u j := widths j
  omega

/-- Coordinate tile count, including nonempty rectangles of zero geometric volume. -/
theorem card_indices {d L} (pos : 0 < L) {l u : Lattice d} (widths : l ≤ u) :
    L*(indices L l u).card ≤ 3^d*(L+unitVolume l u) := by
  let w (j : Fin d) := max 1 (u j-l j).toNat
  let n (j : Fin d) := (Finset.Icc (l j/L) (u j/L)).card
  have bound (j) : L*n j ≤ w j+2*L := (width_card pos (widths j)).trans (Nat.add_le_add_right (le_max_right ..) _)
  have one (j) : 1 ≤ w j := le_max_left ..
  change L*(Finset.Icc (number L l) (number L u)).card ≤ _
  rw [Pi.card_Icc]
  change L*(∏ j, n j) ≤ 3^d*(L+∏ j, w j)
  by_cases long : ∃ i, L ≤ w i
  · obtain ⟨i,wi⟩ := long
    have each (j) : n j ≤ 3*w j := by
      apply Nat.le_of_mul_le_mul_left _ pos
      have h := Nat.mul_le_mul_left L (one j)
      have h' := Nat.mul_le_mul_right (w j) (Nat.succ_le_iff.mpr pos)
      nlinarith only [bound j,h,h',Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt pos)]
    have est : L*(∏ j, n j) ≤ ∏ j, 3*w j := by
      rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i),←Finset.mul_prod_erase _ (fun j => 3*w j) (Finset.mem_univ i)]
      rw [←mul_assoc]
      have h := bound i
      exact Nat.mul_le_mul (by omega : L*n i ≤ 3*w i)
        (Finset.prod_le_prod' (fun j _ => each j))
    rw [Finset.prod_mul_distrib] at est
    simpa using est.trans (Nat.mul_le_mul_left (∏ _ : Fin d, 3) (Nat.le_add_left _ L))
  · push_neg at long
    have each (j) : n j ≤ 3 := by
      apply Nat.le_of_mul_le_mul_left _ pos
      have := bound j; have := long j; omega
    have b := Finset.prod_le_prod' (s := Finset.univ) (fun j _ => each j)
    simp at b
    exact (Nat.mul_le_mul_left L b).trans (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (Nat.le_add_right ..))

end
end GenLimit.KleinbergWei.Banach.LatticeTiles
