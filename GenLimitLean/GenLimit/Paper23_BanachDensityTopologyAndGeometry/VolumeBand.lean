import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardPermutations

/-! On one prescribed range of volumes the finite rectangle game has its
required local bound on arbitrary sparse boards, independently of location
and total board size. One strategy handles the entire range simultaneously. -/
namespace GenLimit.KleinbergWei.Banach.VolumeBand
open Finset Set Real LatticeTiles BoardPermutations
open scoped Classical
noncomputable section
variable {d L : ℕ} (e : ℕ → Lattice d) (D : Finset ℕ)

private def part (k : Lattice d) := D.filter (fun x => number L (e x)=k)

private def play (q : ℝ) : Move := fun h x =>
  let k := number L (e x)
  (TileGenerator.game (L:=L) e q).move k (part (L:=L) e D k) h x

private theorem safe (q : ℝ) : Legal D (play (L:=L) e D q) := by
  intro h x y hit
  obtain ⟨hx,hy,fresh⟩ := (TileGenerator.game (L:=L) e q).legal hit
  exact ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hy).1,fresh⟩

private theorem piece (pos : 0 < L) {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2) (h : List ℕ)
    (all : D ⊆ h.toFinset) {k l u : Lattice d} (meet : k ∈ indices L l u) :
    let X := (part (L:=L) e D k).filter (fun x => e x ∈ Finset.Icc l u)
    (1/2-q)*(X.card:ℝ) - loss d L q ≤ (X.filter (· ∈ earned (play (L:=L) e D q) h)).card := by
  let B := part (L:=L) e D k
  let E := tests (L:=L) e k B
  obtain ⟨i,eq⟩ := tests_complete pos e meet B (fun x hx => (cell_iff pos _ _).2 (Finset.mem_filter.mp hx).2)
  have bound := FiniteGame.covering_bound E (fun _ => 1) q (fun _ => zero_lt_one) hq h1 h
    (show B ⊆ h.toFinset from fun x hx => all (Finset.mem_filter.mp hx).1) i
  have sub : E i ⊆ B := Finset.filter_subset ..
  change E i = _ at eq
  rw [Finset.inter_eq_right.mpr sub,test_loss pos hq,eq] at bound
  refine bound.trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
  intro y hy
  obtain ⟨out,inside⟩ := Finset.mem_inter.mp hy
  obtain ⟨p,x,t,split,hit⟩ := FiniteGame.output_source E (fun _ => 1) q (List.mem_toFinset.mp out)
  have xIn : x ∈ B := FiniteGame.active_input _ _ _ hit
  have address := (Finset.mem_filter.mp xIn).2
  refine Finset.mem_filter.mpr ⟨inside,p,x,⟨t,split.symm⟩,?_⟩
  dsimp only [play]
  rw [address]
  exact hit

private theorem combined (pos : 0 < L) {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2) (h : List ℕ)
    (all : D ⊆ h.toFinset) (l u : Lattice d) :
    let T := D.filter (fun x => e x ∈ Finset.Icc l u)
    (1/2-q)*(T.card:ℝ) ≤ (T.filter (· ∈ earned (play (L:=L) e D q) h)).card +
      (indices L l u).card*loss d L q := by
  let T := D.filter (fun x => e x ∈ Finset.Icc l u)
  let O := earned (play (L:=L) e D q) h
  let J := indices L l u
  let X k := T.filter (fun x => number L (e x)=k)
  let G := T.filter (· ∈ O)
  have cover (x) (hx : x ∈ T) : number L (e x) ∈ J := number_mem pos (Finset.mem_filter.mp hx).2
  have total := Finset.card_eq_sum_card_fiberwise cover
  have hits := Finset.card_eq_sum_card_fiberwise (fun x (hx : x ∈ G) => cover x (Finset.mem_filter.mp hx).1)
  have localCount (k) (mem : k ∈ J) : (1/2-q)*((X k).card:ℝ) ≤
      ((G.filter (fun x => number L (e x)=k)).card:ℝ) + loss d L q := by
    have prev := piece e D pos hq h1 h all mem
    have eq : (part (L:=L) e D k).filter (fun x => e x ∈ Finset.Icc l u) = X k := by
      ext x; simp [part,X,T]; tauto
    have eq' : (X k).filter (· ∈ O) = G.filter (fun x => number L (e x)=k) := by
      ext x; simp [X,G]; tauto
    change (1/2-q)*(_ :ℝ) - loss d L q ≤ (_ : ℝ) at prev
    rw [eq,show earned (play (L:=L) e D q) h = O from rfl,eq'] at prev
    linarith
  have sum := Finset.sum_le_sum localCount
  change (1/2-q)*(T.card:ℝ) ≤ (G.card:ℝ) + J.card*loss d L q
  rw [total,hits,Nat.cast_sum,Nat.cast_sum]
  simpa only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] using sum

/-- Choose a polynomial width c for the volume range. For every tile size L
one causal strategy protects all positive-width rectangles with V ≤ L ≤ V^c.
The logarithmic coefficient is independent of L and of the finite board. -/
theorem local_logarithmic_bound {d} (e : ℕ → Lattice d) {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2)
    (c : ℕ) : ∃ b : ℝ, 0 ≤ b ∧ ∀ L : ℕ, 0 < L → ∀ D : Finset ℕ,
    ∃ move : Move, Legal D move ∧ ∀ h : List ℕ, D ⊆ h.toFinset → ∀ l u : Lattice d,
      (∀ i, l i < u i) → geometricVolume l u ≤ L → L ≤ (geometricVolume l u)^c →
      let X := D.filter (fun x => e x ∈ Finset.Icc l u)
      (1/2-q)*(X.card:ℝ) - b*(1+log (geometricVolume l u)) ≤ (X.filter (· ∈ earned move h)).card := by
  let F := 2*(3:ℝ)^d
  let B := (log (1+q)+2*d*c)/(2*q)
  have lp : 0 ≤ log (1+q) := Real.log_nonneg (by linarith)
  have Bp : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨F*B,by dsimp [F]; positivity,fun L pos D => ⟨play (L:=L) e D q,safe e D q,?_⟩⟩
  intro h all l u widths small big
  let V := geometricVolume l u
  have vp : 0 < V := Finset.prod_pos (fun i _ => by have hi := widths i; change 0 < (u i-l i).toNat; omega)
  have ln : 0 ≤ log V := Real.log_nonneg (by exact_mod_cast vp)
  have logL : log L ≤ (c:ℝ)*log V := by
    rw [←Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast pos)
    exact_mod_cast big
  have one : loss d L q ≤ B*(1+log V) := by
    unfold loss B
    rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right (by positivity)]
    have nn : 0 ≤ 2*(d:ℝ)*c := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left logL (show 0 ≤ 2*(d:ℝ) by positivity),mul_nonneg lp ln,nn]
  have card := card_indices pos (fun i => (widths i).le)
  rw [unitVolume_eq widths] at card
  have cap : ((indices L l u).card:ℝ) ≤ F := by
    have bound := card.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left small L))
    have eq : 3^d*(L+L) = L*(2*3^d) := by ring
    rw [eq] at bound
    dsimp only [F]
    exact_mod_cast Nat.le_of_mul_le_mul_left bound pos
  have sum := combined e D pos hq h1 h all l u
  have total := mul_le_mul cap one (loss_nonneg d pos hq) (show 0 ≤ F by dsimp [F]; positivity)
  dsimp only at sum ⊢
  change _ ≤ _ + (indices L l u).card*loss d L q at sum
  linarith only [sum,total,show F*(B*(1+log V)) = F*B*(1+log V) by ring]

end
end GenLimit.KleinbergWei.Banach.VolumeBand
