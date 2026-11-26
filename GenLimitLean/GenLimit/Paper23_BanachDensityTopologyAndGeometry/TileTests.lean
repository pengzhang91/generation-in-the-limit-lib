import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LatticeTiles
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardCoverage

/-! Rectangle queries in any finite board contained in one lattice tile
have L^(2d) endpoint tests, independently of the tile's address. -/
namespace GenLimit.KleinbergWei.Banach.LatticeTiles
open Finset Real Set
open scoped Classical
noncomputable section

abbrev Test (d L : ℕ) := (Fin d → Fin L) × (Fin d → Fin L)

def tests {V : Type*} {d L} (e : V → Lattice d) (k : Lattice d) (D : Finset V)
    (i : Test d L) := D.filter (fun v => ∀ j,
      lower L k j + i.1 j ≤ e v j ∧ e v j ≤ lower L k j + i.2 j)

def loss (d L : ℕ) (q : ℝ) := (log (1+q)+2*d*log L)/(2*q)

theorem loss_nonneg (d : ℕ) {L : ℕ} (pos : 0 < L) {q : ℝ} (hq : 0 < q) :
    0 ≤ loss d L q := by
  have lq := Real.log_nonneg (show 1 ≤ 1+q by linarith)
  have lL := Real.log_nonneg (show 1 ≤ (L:ℝ) by exact_mod_cast pos)
  unfold loss; positivity

private def offset {L : ℕ} (pos : 0 < L) (x : ℤ) : Fin L :=
  ⟨min x.toNat (L-1),by omega⟩

private theorem offset_eq {L : ℕ} (pos : 0 < L) {x : ℤ} (lo : 0 ≤ x) (hi : x < L) :
    ((offset pos x).val:ℤ) = x := by
  dsimp [offset]; omega

theorem tests_complete {V : Type*} {d L} (pos : 0 < L) (e : V → Lattice d)
    {k l u : Lattice d} (meet : k ∈ indices L l u) (D : Finset V)
    (inside : ∀ x ∈ D, e x ∈ cell L k) :
    ∃ i : Test d L, tests e k D i = D.filter (fun v => e v ∈ Finset.Icc l u) := by
  have hp : (0:ℤ)<L := by exact_mod_cast pos
  obtain ⟨left,right⟩ := Finset.mem_Icc.mp meet
  have bounds (j) : l j ≤ upper L k j ∧ lower L k j ≤ u j := by
    have a := Int.lt_ediv_add_one_mul_self (l j) hp
    have b := Int.ediv_mul_le (u j) hp.ne'
    have c := mul_le_mul_of_nonneg_right (left j) hp.le
    have f := mul_le_mul_of_nonneg_right (right j) hp.le
    dsimp only [number] at c f; dsimp [lower,upper]; constructor <;> linarith
  let a (j : Fin d) := max (l j) (lower L k j)
  let b (j : Fin d) := min (u j) (upper L k j)
  have endpoints (j) : lower L k j ≤ a j ∧ a j ≤ upper L k j ∧
      lower L k j ≤ b j ∧ b j ≤ upper L k j := by
    have le : lower L k j ≤ upper L k j := by dsimp [lower,upper]; omega
    exact ⟨le_max_right ..,max_le (bounds j).1 le,le_min (bounds j).2 le,min_le_right ..⟩
  let i : Test d L := (fun j => offset pos (a j-lower L k j), fun j => offset pos (b j-lower L k j))
  have ae j : lower L k j + (i.1 j:ℤ)=a j := by
    obtain ⟨lo,hi,_⟩ := endpoints j
    have ub : upper L k j = lower L k j+L-1 := rfl
    change _ + ((offset pos _).val:ℤ) = _
    rw [offset_eq pos (by omega) (by omega)]; omega
  have be j : lower L k j + (i.2 j:ℤ)=b j := by
    obtain ⟨_,_,lo,hi⟩ := endpoints j
    have ub : upper L k j = lower L k j+L-1 := rfl
    change _ + ((offset pos _).val:ℤ) = _
    rw [offset_eq pos (by omega) (by omega)]; omega
  refine ⟨i,Finset.ext fun x => ?_⟩
  simp only [tests,Finset.mem_filter,ae,be,Finset.mem_Icc]
  apply and_congr_right; intro hx
  obtain ⟨low,high⟩ := Finset.mem_Icc.mp (inside _ hx)
  constructor
  · intro both
    exact ⟨fun j => (le_max_left ..).trans (both j).1,fun j => (both j).2.trans (min_le_left ..)⟩
  · rintro ⟨left,right⟩; exact fun j => ⟨max_le (left j) (low j),le_min (right j) (high j)⟩

theorem test_loss {d L : ℕ} (pos : 0 < L) {q : ℝ} (hq : 0 < q) :
    log ((1+q)*(∑ _ : Test d L, (1:ℝ))/1)/(2*q) = loss d L q := by
  have npos : (0:ℝ) < L := by exact_mod_cast pos
  have hp : 0 < 1+q := by linarith
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_pi,
    Fintype.card_fin,Finset.prod_const,nsmul_eq_mul,mul_one,div_one,Nat.cast_mul,
    Nat.cast_pow,Test]
  rw [Real.log_mul hp.ne' (by positivity),Real.log_mul (by positivity) (by positivity),Real.log_pow]
  unfold loss
  ring

theorem local_bound {V : Type*} [DecidableEq V] [Inhabited V] {d L} (pos : 0 < L)
    (e : V → Lattice d) {k l u : Lattice d} (meet : k ∈ indices L l u)
    (D : Finset V) (inside : ∀ x ∈ D, e x ∈ cell L k)
    {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2) (s : ℕ → V) (cover : ∀ x ∈ D, x ∈ range s)
    (plan : List V → V → Option V) (backup : List V → Set V) (inf : ∀ h, (backup h).Infinite)
    (routes : ∀ t y, FiniteGame.recommend (tests (L:=L) e k D) (fun _ => 1) q
      (FiniteGame.run (tests (L:=L) e k D) (fun _ => 1) q D (textPrefix s t)) (s t) = some y →
      plan (textPrefix s t) (s t) = some y) :
    let T := D.filter (fun x => e x ∈ Finset.Icc l u)
    (1/2-q)*(T.card:ℝ)-loss d L q ≤ (T.filter (· ∈ range (LocalReplies.play plan backup inf s))).card := by
  obtain ⟨i,eq⟩ := tests_complete pos e meet D inside
  have h := FiniteGame.realized_bound (tests e k D) (fun _ => 1) (fun _ => zero_lt_one)
    hq h1 D s cover plan backup inf routes i
  have sub : tests e k D i ⊆ D := Finset.filter_subset ..
  rw [Finset.inter_eq_right.mpr sub,eq] at h
  rw [test_loss pos hq] at h
  exact h

end
end GenLimit.KleinbergWei.Banach.LatticeTiles
