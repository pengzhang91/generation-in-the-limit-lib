import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardPermutations
import Mathlib.Data.Fintype.Prod

/-! Simultaneous short row and column tests rule out static pairings as a
solution to the local rectangle game. This holds on an ordinary stretched
square grid, where an adaptive generator has a near-half guarantee. -/
namespace GenLimit.KleinbergWei.Banach.MatchingStrips
open Finset Set Filter Real
open scoped Classical
noncomputable section

abbrev Vertex (n : ℕ) := Fin n × Fin n

/-- The two ends of an undirected matched pair lie in at most one of the
2n rows and columns. Orientations count each pair only once. -/
private def line {n} (k : Sum (Fin n) (Fin n)) (p : Vertex n) : Prop :=
  k.elim (fun i => p.1=i) (fun j => p.2=j)

private theorem line_card {n} (k : Sum (Fin n) (Fin n)) :
    (Finset.univ.filter (line k)).card = n := by
  cases k with
  | inl i =>
    have eq : Finset.univ.filter (line (Sum.inl i)) =
        ({i} : Finset (Fin n)) ×ˢ Finset.univ := by ext ⟨a,b⟩; simp [line,eq_comm]
    simp [eq]
  | inr j =>
    have eq : Finset.univ.filter (line (Sum.inr j)) =
        Finset.univ ×ˢ ({j} : Finset (Fin n)) := by ext ⟨a,b⟩; simp [line,eq_comm]
    simp [eq]

private def number {n} (p : Vertex n) := p.1.val*n+p.2.val

private theorem number_inj (n : ℕ) : Function.Injective (number (n:=n)) := by
  intro p q eq
  have pos : 0 < n := (Nat.zero_le _).trans_lt p.2.isLt
  have div (a : Vertex n) : number a / n = a.1.val := by
    rw [number,Nat.mul_comm _ n,Nat.mul_add_div pos,Nat.div_eq_of_lt a.2.isLt,Nat.add_zero]
  have fst := (div p).symm.trans ((congrArg (· / n) eq).trans (div q))
  exact Prod.ext (Fin.ext fst) (Fin.ext (by dsimp [number] at eq; rwa [fst,Nat.add_left_cancel_iff] at eq))

private def sources {n} (mate : Vertex n → Vertex n) :=
  Finset.univ.filter (fun p => number p < number (mate p))

private theorem source_count {n} (mate : Vertex n → Vertex n)
    (flip : Function.Involutive mate) (distinct : ∀ p, mate p ≠ p) :
    2*(sources mate).card = n*n := by
  let S := sources mate
  have eq : S.image mate = Finset.univ \ S := by
    ext p
    simp only [S,sources,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_sdiff,not_lt]
    constructor
    · rintro ⟨v,lt,rfl⟩; simpa [flip v] using lt.le
    · intro le
      have ne : number (mate p) ≠ number p := fun eq => distinct p ((number_inj n) eq)
      exact ⟨mate p,by simpa [flip p] using lt_of_le_of_ne le ne,flip p⟩
  have total := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [←eq,Finset.card_image_of_injective _ flip.injective] at total
  simpa [two_mul,S] using total

private def internal {n} (mate : Vertex n → Vertex n) (k : Sum (Fin n) (Fin n)) :=
  (sources mate).filter (fun p => line k p ∧ line k (mate p))

private theorem internal_total {n} (mate : Vertex n → Vertex n) (distinct : ∀ p, mate p ≠ p) :
    ∑ k, (internal mate k).card ≤ (sources mate).card := by
  classical
  simp only [internal,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p hp
  rw [Fintype.sum_sum_type]
  by_cases row : (mate p).1 = p.1
  · have col : (mate p).2 ≠ p.2 := fun eq => distinct p (Prod.ext row eq)
    have empty (j : Fin n) : ¬ (p.2=j ∧ (mate p).2=j) := fun h => col (h.2.trans h.1.symm)
    simp [line,row,empty]
  · have empty (i : Fin n) : ¬ (p.1=i ∧ (mate p).1=i) := fun h => row (h.2.trans h.1.symm)
    by_cases col : (mate p).2 = p.2
    · simp [line,col,empty]
    · have none (j : Fin n) : ¬ (p.2=j ∧ (mate p).2=j) := fun h => col (h.2.trans h.1.symm)
      simp [line,empty,none]

/-- Some row or column contains at most one matched pair per four sites. -/
private theorem sparse_line {n : ℕ} (positive : 0 < n) (mate : Vertex n → Vertex n)
    (flip : Function.Involutive mate) (distinct : ∀ p, mate p ≠ p) :
    ∃ k, 4*(internal mate k).card ≤ n := by
  classical
  by_contra! high
  letI : NeZero n := ⟨positive.ne'⟩
  have strict := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) Finset.univ_nonempty (fun k _ => high k)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,
    nsmul_eq_mul,←Finset.mul_sum] at strict
  have total := internal_total mate distinct
  have card := source_count mate flip distinct
  nlinarith


open BoardPermutations

/-- On each fresh pair follow its predetermined mate. On all other inputs
the strategy may choose any still unseen word, including a backup. -/
def Follows {V : Type*} (mate : V → V) (move : List V → V → Option V) :=
  ∀ h x, x ∉ h → x ∉ earned move h → mate x ∉ h → mate x ∉ earned move h →
    move h x = some (mate x)

private theorem first_pass {V : Type*} (mate : V → V) (inj : Function.Injective mate)
    (P : Finset V) (outside : ∀ x ∈ P, mate x ∉ P) (move : List V → V → Option V)
    (follows : Follows mate move) (h : List V) (nd : h.Nodup) (inside : ∀ x ∈ h, x ∈ P) :
    ∀ y ∈ earned move h, ∃ x ∈ h, mate x = y := by
  induction h using List.reverseRecOn with
  | nil => rintro y ⟨p,x,pre,_⟩; have := pre.length_le; simp at this
  | append_singleton h x ih =>
    have short : h <+: h++[x] := List.prefix_append ..
    have new : x ∉ h := (List.nodup_cons.mp (by simpa only [List.nodup_append_comm (l₁:=h),List.singleton_append] using nd : (x::h).Nodup)).1
    have old := ih (short.sublist.nodup nd) (fun v hv => inside v (short.subset hv))
    have mem := inside x (by simp)
    have mx := outside x mem
    have step := follows h x new (by
      intro hx; obtain ⟨v,hv,eq⟩ := old _ hx
      exact outside v (inside v (short.subset hv)) (eq ▸ mem))
      (fun hx => mx (inside _ (short.subset hx))) (by
        intro hx; obtain ⟨v,hv,eq⟩ := old _ hx; exact new (inj eq ▸ hv))
    intro y hy
    rcases earned_push.mp hy with prev | last
    · obtain ⟨v,hv,eq⟩ := old _ prev; exact ⟨v,short.subset hv,eq⟩
    · exact ⟨x,by simp,Option.some.inj (step.symm.trans last)⟩

private theorem defeat_line {n} (mate : Vertex n → Vertex n)
    (flip : Function.Involutive mate) (distinct : ∀ p, mate p ≠ p)
    (k : Sum (Fin n) (Fin n)) (move : List (Vertex n) → Vertex n → Option (Vertex n))
    (follows : Follows mate move) (safe : ∀ {h x y}, move h x = some y → y ∉ h++[x]) :
    ∃ h : List (Vertex n), h.Nodup ∧ h.toFinset=Finset.univ ∧
      ((Finset.univ.filter (line k)).filter (· ∈ earned move h)).card ≤ (internal mate k).card := by
  let T := Finset.univ.filter (line k)
  let E := (internal mate k).image mate
  let P := T \ E
  have outside (x) (hx : x ∈ P) : mate x ∉ P := by
    intro both
    obtain ⟨inT,notE⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨inT',notE'⟩ := Finset.mem_sdiff.mp both
    have ne : number x ≠ number (mate x) := fun eq => distinct x ((number_inj n) eq.symm)
    rcases lt_or_gt_of_ne ne with lt | gt
    · apply notE'
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨by simp [sources,lt],
        (Finset.mem_filter.mp inT).2,(Finset.mem_filter.mp inT').2⟩,rfl⟩
    · apply notE
      refine Finset.mem_image.mpr ⟨mate x,Finset.mem_filter.mpr ⟨by simp [sources,flip x,gt],
        (Finset.mem_filter.mp inT').2,by simpa [flip x] using (Finset.mem_filter.mp inT).2⟩,flip x⟩
  let start := P.toList
  let tail := (Finset.univ \ P).toList
  let h := start++tail
  have nd : h.Nodup := by
    refine List.nodup_append.mpr ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb eq
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (eq ▸ Finset.mem_toList.mp ha)
  have full : h.toFinset = Finset.univ := by ext x; simp [h,start,tail]
  refine ⟨h,nd,full,?_⟩
  have used := first_pass mate flip.injective P outside move follows start
    (Finset.nodup_toList _) (fun v hv => Finset.mem_toList.mp hv)
  have disj (y) (inside : y ∈ P) : y ∉ earned move h := by
    rintro ⟨p,x,pre,hit⟩
    rcases List.prefix_or_prefix_of_prefix pre (show start <+: h from List.prefix_append ..) with early | late
    · obtain ⟨v,inStart,eq⟩ := used y ⟨p,x,early,hit⟩
      exact outside v (Finset.mem_toList.mp inStart) (eq ▸ inside)
    · exact safe hit (late.subset (Finset.mem_toList.mpr inside))
  have sub : T.filter (· ∈ earned move h) ⊆ E := by
    intro y hy; by_contra absent
    obtain ⟨t,hit⟩ := Finset.mem_filter.mp hy
    exact disj y (Finset.mem_sdiff.mpr ⟨t,absent⟩) hit
  exact (Finset.card_le_card sub).trans Finset.card_image_le

/-- Actual lattice locations. Each grid row and column can be isolated
by a rectangle of geometric width one in the transverse direction. -/
def point {n} (p : Vertex n) : Lattice 2 := ![2*(p.1.val:ℤ),2*(p.2.val:ℤ)]

private theorem row_test {n} (pos : 0 < n) (k : Sum (Fin n) (Fin n)) :
    ∃ l u : Lattice 2, (∀ i, l i < u i) ∧ geometricVolume l u = 2*n ∧
      ∀ p : Vertex n, point p ∈ Finset.Icc l u ↔ line k p := by
  cases k with
  | inl i =>
    refine ⟨![2*(i.val:ℤ),0],![2*(i.val:ℤ)+1,2*(n:ℤ)],?_,?_,?_⟩
    · intro j; fin_cases j <;> simp; omega
    · simp [geometricVolume,Fin.prod_univ_succ]; omega
    · intro p
      simp only [Finset.mem_Icc,Pi.le_def,Fin.forall_fin_succ,Fin.forall_fin_zero,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,and_true,line,Sum.elim_inl,point]
      have bound := p.2.isLt
      constructor
      · intro h; apply Fin.ext; simp at h; omega
      · intro h; subst i; simp
  | inr j =>
    refine ⟨![0,2*(j.val:ℤ)],![2*(n:ℤ),2*(j.val:ℤ)+1],?_,?_,?_⟩
    · intro i; fin_cases i <;> simp; omega
    · simp [geometricVolume,Fin.prod_univ_succ]; omega
    · intro p
      simp only [Finset.mem_Icc,Pi.le_def,Fin.forall_fin_succ,Fin.forall_fin_zero,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,and_true,line,Sum.elim_inr,point]
      have bound := p.1.isLt
      constructor
      · intro h; apply Fin.ext; simp at h; omega
      · intro h; subst j; simp

/-- For every fixed matching, an ordering of the board forces at most a
quarter of one n-point strip to be generated, even with arbitrary fresh
fallback moves once a pair has already been visited. -/
theorem quarter_strip {n} (positive : 0 < n) (mate : Vertex n → Vertex n)
    (flip : Function.Involutive mate) (distinct : ∀ p, mate p ≠ p)
    (move : List (Vertex n) → Vertex n → Option (Vertex n)) (follows : Follows mate move)
    (safe : ∀ {h x y}, move h x = some y → y ∉ h++[x]) :
    ∃ (l u : Lattice 2) (h : List (Vertex n)), h.Nodup ∧ h.toFinset = Finset.univ ∧
      (∀ i, l i < u i) ∧ geometricVolume l u = 2*n ∧
      let X := Finset.univ.filter (fun p : Vertex n => point p ∈ Finset.Icc l u)
      X.card = n ∧ 4*(X.filter (· ∈ earned move h)).card ≤ n := by
  obtain ⟨k,few⟩ := sparse_line positive mate flip distinct
  obtain ⟨h,nd,all,lost⟩ := defeat_line mate flip distinct k move follows (fun hit => safe hit)
  obtain ⟨l,u,pos,vol,eq⟩ := row_test positive k
  refine ⟨l,u,h,nd,all,pos,vol,?_⟩
  have same : Finset.univ.filter (fun p : Vertex n => point p ∈ Finset.Icc l u) = Finset.univ.filter (line k) := by ext p; simp [eq]
  dsimp only; rw [same]
  exact ⟨line_card k,(Nat.mul_le_mul_left 4 lost).trans few⟩


/-- No fixed-mate strategy, even when a different matching may be chosen
on each board, can give the finite-game logarithmic error at q < 1/4. -/
theorem defeats_logarithmic_allowance {q : ℝ} (small : q < 1/4) (b : ℝ) :
    ∃ k : ℕ, 0 < k ∧ ∀ (mate : Vertex (2*k) → Vertex (2*k)),
      Function.Involutive mate → (∀ p, mate p ≠ p) →
      ∀ move : List (Vertex (2*k)) → Vertex (2*k) → Option (Vertex (2*k)),
      Follows mate move → (∀ {h x y}, move h x = some y → y ∉ h++[x]) →
      ∃ (l u : Lattice 2) (h : List (Vertex (2*k))), h.Nodup ∧ h.toFinset=Finset.univ ∧ (∀ i, l i < u i) ∧
        let X := Finset.univ.filter (fun p : Vertex (2*k) => point p ∈ Finset.Icc l u)
        ((X.filter (· ∈ earned move h)).card:ℝ) <
          (1/2-q)*X.card - b*(1+Real.log (geometricVolume l u)) := by
  have logs : Tendsto (fun k : ℕ => log k/(k:ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have inv : Tendsto (fun k : ℕ => (1:ℝ)/(k:ℝ)) atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop _
  have limit : Tendsto (fun k : ℕ => b*(1+log 4+log k)/(k:ℝ)) atTop (nhds 0) := by
    have h := ((inv.const_mul (1+log 4)).add logs).const_mul b
    convert h using 1
    · funext k; ring
    · simp
  obtain ⟨k,close,pos⟩ := ((limit.eventually_lt_const (by linarith : 0 < 2*(1/4-q))).and
    (eventually_ge_atTop 1)).exists
  refine ⟨k,pos,fun mate flip distinct move follows safe => ?_⟩
  obtain ⟨l,u,h,nd,all,wide,vol,size,bound⟩ :=
    quarter_strip (n:=2*k) (by omega) mate flip distinct move follows (fun hit => safe hit)
  refine ⟨l,u,h,nd,all,wide,?_⟩
  let X := Finset.univ.filter (fun p : Vertex (2*k) => point p ∈ Finset.Icc l u)
  have kr : 0 < (k:ℝ) := by exact_mod_cast pos
  have loss := (div_lt_iff₀ kr).mp close
  have cnt : (4:ℝ)*((X.filter (· ∈ earned move h)).card:ℝ) ≤ 2*(k:ℝ) := by exact_mod_cast bound
  dsimp only
  rw [vol,size,show 2*(2*k)=4*k by omega,Nat.cast_mul,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_ofNat,Real.log_mul (by norm_num) kr.ne']
  change ((X.filter (· ∈ earned move h)).card:ℝ) < _
  linarith

end
end GenLimit.KleinbergWei.Banach.MatchingStrips
