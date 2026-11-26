import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ForestGames

/-! Assemble local rectangle-game counts across a finite-rank forest and
a finite cover of the query. The startup loss is uniform over queries. -/
namespace GenLimit.KleinbergWei.Banach.ForestGames
open Set Finset TowerTopology DensityMeasures DensityMeasures.FiniteRankParent
open scoped Classical
noncomputable section
variable {I : Type*} {R : ℕ} {C : LanguageFamily}
  (hr : FiniteRankAtMost (FamilySpace C) R) (cells : Cells I)

def LayerCount (O : Set ℕ) (Q : Finset ℕ) (q loss : ℝ) (k : I)
    (v : FamilyPoint C) (K : Set ℕ) := ∀ j < R,
    (∀ x ∈ board hr cells k v j, x ∈ K) →
    let X := (board hr cells k v j).filter (· ∈ Q)
    (1/2-q)*(X.card:ℝ)-loss ≤ (X.filter (· ∈ O)).card

private theorem cell_count (exactBins : ∀ {k x}, x ∈ cells.bin k ↔ cells.address x = k)
    (O : Set ℕ) (Q : Finset ℕ) {loss q : ℝ} (nn : 0 ≤ loss)
    {s : ℕ → ℕ} {z : ℕ} {k : I}
    (reach : StaticForest.Reaches hr (TileSeed.seed cells.address C s k) (familyPoint C z))
    (bound : LayerCount hr cells O Q q loss k (TileSeed.seed cells.address C s k) (C z)) :
    let T := (Q.filter (· ∈ C z)).filter (fun x => cells.address x=k)
    (1/2-q)*(T.card:ℝ) ≤ (T.filter (· ∈ O)).card + R*loss := by
  let v := TileSeed.seed cells.address C s k
  let B := cells.bin k
  let W (j : ℕ) := (ForestMatching.visible hr B v j).filter (fun x => x ∈ Q)
  obtain ⟨m,lt,last⟩ := StaticForest.bounded_path hr reach
  change (StaticForest.parent hr)^[m] v = familyPoint C z at last
  have est (j : ℕ) (le : j ≤ m+1) :
      (1/2-q)*((W j).card:ℝ) ≤ ((W j).filter (· ∈ O)).card+j*loss := by
    induction j with
    | zero => simp [W,ForestMatching.visible]
    | succ j ih =>
      have old := ih (by omega)
      have sub : ∀ x ∈ board hr cells k v j, x ∈ C z := by
        intro x hx
        have up := ForestMatching.visible_mono hr B v le (Finset.mem_sdiff.mp hx).1
        have mem := (Finset.mem_filter.mp up).2
        rwa [last] at mem
      have new := bound j (by omega) sub
      let D := (board hr cells k v j).filter (fun x => x ∈ Q)
      change (1/2-q)*(D.card:ℝ)-loss ≤ (D.filter (· ∈ O)).card at new
      have up : W j ⊆ W (j+1) :=
        Finset.filter_subset_filter _ (ForestMatching.visible_mono hr B v (Nat.le_succ j))
      have diff : W (j+1) \ W j = D := by
        ext; simp [W,D,board,ForestMatching.layer,B]; tauto
      have diff' : (W (j+1)).filter (· ∈ O) \ (W j).filter (· ∈ O) = D.filter (· ∈ O) := by
        rw [←diff]; ext; simp; tauto
      have a := Finset.card_sdiff_add_card_eq_card up
      have b := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter (p:=(· ∈ O)) up)
      rw [diff] at a; rw [diff'] at b
      rw [←a,←b]; push_cast; linarith
  have eq : W (m+1) = (Q.filter (· ∈ C z)).filter (fun x => cells.address x=k) := by
    ext x
    simp only [W,ForestMatching.visible,Finset.mem_filter,B,exactBins,last]
    change ((_ ∧ x ∈ C z) ∧ _) ↔ ((_ ∧ x ∈ C z) ∧ _)
    tauto
  have bound := est (m+1) le_rfl
  rw [eq] at bound
  dsimp only
  exact bound.trans (add_le_add_left (mul_le_mul_of_nonneg_right
    (by exact_mod_cast lt : ((m+1:ℕ):ℝ) ≤ R) nn) _)

/-- Sum the individual cell losses and pay for exceptional cells only once per text. -/
theorem global_count_with_cell_losses (exactBins : ∀ {k x}, x ∈ cells.bin k ↔ cells.address x = k)
    (O : Set ℕ) {q : ℝ} (hq : 0 ≤ q) {z s} (pres : Presents s (C z)) :
    ∃ H : ℕ, ∀ (Q : Finset ℕ) (J : Finset I) (loss : I → ℝ), (∀ k, 0 ≤ loss k) →
      (∀ x ∈ Q, cells.address x ∈ J) →
      (∀ k ∈ J, LayerCount hr cells O Q q (loss k) k (TileSeed.seed cells.address C s k) (C z)) →
      let T := Q.filter (· ∈ C z)
      (1/2-q)*(T.card:ℝ) ≤ (T.filter (· ∈ O)).card + (∑ k ∈ J, R*loss k)+H := by
  let addr := cells.address
  obtain ⟨bad,good⟩ := TileSeed.eventually_reaches addr C hr pres
  let cost (k : I) : ℝ := if k ∈ bad then ((cells.bin k).card:ℝ) else 0
  let H := ∑ k ∈ bad, (cells.bin k).card
  refine ⟨H,fun Q J loss nn cover bound => ?_⟩
  let T := Q.filter (· ∈ C z)
  let S (k : I) := T.filter (fun x => addr x=k)
  let G := T.filter (· ∈ O)
  have nonneg (k : I) := mul_nonneg (Nat.cast_nonneg (α := ℝ) R) (nn k)
  have piece (k) (hk : k ∈ J) : (1/2-q)*((S k).card:ℝ) ≤
      ((S k).filter (· ∈ O)).card + R*loss k + cost k := by
    by_cases ex : (S k).Nonempty
    · obtain ⟨x,hit⟩ := ex
      obtain ⟨inT,atK⟩ := Finset.mem_filter.mp hit
      have inx := (Finset.mem_filter.mp inT).2
      obtain ⟨t,xt⟩ := (show x ∈ range s from pres.symm ▸ inx)
      by_cases hb : k ∈ bad
      · have sub : S k ⊆ cells.bin k := fun x hx => exactBins.mpr (Finset.mem_filter.mp hx).2
        have le : ((S k).card:ℝ) ≤ (cells.bin k).card := by exact_mod_cast Finset.card_le_card sub
        simp only [cost,if_pos hb]
        nlinarith [nonneg k,mul_nonneg hq (Nat.cast_nonneg (α:=ℝ) (S k).card)]
      · have loc : addr (s t)=k := xt ▸ atK
        have reach := good t (loc ▸ hb)
        rw [loc] at reach
        simpa only [cost,if_neg hb,add_zero] using cell_count hr cells exactBins O Q (nn k) reach (bound k hk)
    · have z := Finset.not_nonempty_iff_eq_empty.mp ex
      simp only [z,Finset.card_empty,Nat.cast_zero,mul_zero,Finset.filter_empty,zero_add]
      have nn : 0 ≤ cost k := by unfold cost; split <;> positivity
      linarith [nonneg k]
  have sums := Finset.sum_le_sum piece
  have cov (x) (hx : x ∈ T) : addr x ∈ J := cover x (Finset.mem_filter.mp hx).1
  have total := Finset.card_eq_sum_card_fiberwise cov
  have hits := Finset.card_eq_sum_card_fiberwise (fun x (hx : x ∈ G) => cov x (Finset.mem_filter.mp hx).1)
  have eq (k) : (S k).filter (· ∈ O) = G.filter (fun x => addr x=k) := by
    ext; simp [S,G]; tauto
  have paid : ∑ k ∈ J, cost k ≤ H := by
    rw [show (∑ k ∈ J, cost k) = ∑ k ∈ J.filter (· ∈ bad), ((cells.bin k).card:ℝ) by
      simp [Finset.sum_filter,cost]]
    exact_mod_cast Finset.sum_le_sum_of_subset (show J.filter (· ∈ bad) ⊆ bad from fun _ hx => (Finset.mem_filter.mp hx).2)
  change (1/2-q)*(T.card:ℝ) ≤ (G.card:ℝ)+(∑ k ∈ J, R*loss k)+H
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,eq] at sums
  rw [total,hits,Nat.cast_sum,Nat.cast_sum,←Finset.mul_sum]
  linarith

theorem global_count_of_nonneg (exactBins : ∀ {k x}, x ∈ cells.bin k ↔ cells.address x = k)
    (O : Set ℕ) {q : ℝ} (hq : 0 ≤ q) {z s} (pres : Presents s (C z)) :
    ∃ H : ℕ, ∀ (Q : Finset ℕ) (J : Finset I) (loss : ℝ), 0 ≤ loss →
      (∀ x ∈ Q, cells.address x ∈ J) →
      (∀ k ∈ J, LayerCount hr cells O Q q loss k (TileSeed.seed cells.address C s k) (C z)) →
      let T := Q.filter (· ∈ C z)
      (1/2-q)*(T.card:ℝ) ≤ (T.filter (· ∈ O)).card + J.card*(R*loss)+H := by
  obtain ⟨H,works⟩ := global_count_with_cell_losses hr cells exactBins O hq pres
  refine ⟨H,fun Q J loss nn cover perCell => ?_⟩
  simpa only [Finset.sum_const,nsmul_eq_mul] using
    works Q J (fun _ => loss) (fun _ => nn) cover perCell

theorem global_count (exactBins : ∀ {k x}, x ∈ cells.bin k ↔ cells.address x = k)
    (O : Set ℕ) {q : ℝ} (hq : 0 < q) {z s} (pres : Presents s (C z)) :
    ∃ H : ℕ, ∀ (Q : Finset ℕ) (J : Finset I) (loss : ℝ), 0 ≤ loss →
      (∀ x ∈ Q, cells.address x ∈ J) →
      (∀ k ∈ J, LayerCount hr cells O Q q loss k (TileSeed.seed cells.address C s k) (C z)) →
      let T := Q.filter (· ∈ C z)
      (1/2-q)*(T.card:ℝ) ≤ (T.filter (· ∈ O)).card + J.card*(R*loss)+H :=
  global_count_of_nonneg hr cells exactBins O hq.le pres

end
end GenLimit.KleinbergWei.Banach.ForestGames
