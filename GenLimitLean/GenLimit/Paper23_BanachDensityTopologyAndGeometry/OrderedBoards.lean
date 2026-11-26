import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ChainRows

/-! A finite board on a coordinatewise chain can be sorted even when
the global language indices do not respect the order. This includes the
whole two-sided integer line and targets with no least element. -/
namespace GenLimit.KleinbergWei.Banach.OrderedBoards
open BoardPermutations Finset Filter Set Real
open scoped Classical ENNReal
noncomputable section

private def pull (key : ℕ → ℕ) (move : Move) (h : List ℕ) (x : ℕ) : Option ℕ :=
  (move (h.map key) (key x)).map (Function.invFun key)

private theorem pull_legal (key : ℕ → ℕ) (inj : Function.Injective key)
    {D : Finset ℕ} {move : Move} (safe : Legal (D.image key) move) : Legal D (pull key move) := by
  intro h x y hit
  obtain ⟨k,hk,rfl⟩ := Option.map_eq_some_iff.mp hit
  obtain ⟨inside,target,fresh⟩ := safe hk
  obtain ⟨a,ha,eq⟩ := mem_image.mp inside
  obtain ⟨b,hb,rfl⟩ := mem_image.mp target
  rw [Function.leftInverse_invFun inj b]
  refine ⟨inj eq ▸ ha,hb,fun old => fresh ?_⟩
  simpa only [List.map_append,List.map_singleton] using List.mem_map_of_mem (f:=key) old

private theorem earned_pull (key : ℕ → ℕ) (inj : Function.Injective key)
    (move : Move) (h : List ℕ) (x : ℕ) :
    key x ∈ earned move (h.map key) → x ∈ earned (pull key move) h := by
  induction h using List.reverseRecOn with
  | nil => simp [earned]
  | append_singleton h y ih =>
    simp only [List.map_append,List.map_singleton,earned_push]
    exact Or.imp ih (fun hit => by simp [pull,hit,Function.leftInverse_invFun inj x])

/-- Renaming the finite board preserves its causal rectangle guarantee. -/
theorem of_renaming {d} (e : ℕ → Lattice d) (key : ℕ → ℕ) (inj : Function.Injective key)
    (D : Finset ℕ) (q b : ℝ) (source : BoardResponse (e ∘ Function.invFun key) q b (D.image key)) :
    BoardResponse e q b D := by
  obtain ⟨move,safe,wins⟩ := (board_response_iff ..).mp source
  refine (board_response_iff ..).mpr ⟨pull key move,pull_legal key inj safe,?_⟩
  intro h nodup full l u wide
  have renamed : (h.map key).toFinset = D.image key := by
    rw [←full]
    ext y
    simp
  have bound := wins (h.map key) (nodup.map inj) renamed l u wide
  let X := D.filter (fun x => e x ∈ Finset.Icc l u)
  have back (x : ℕ) : Function.invFun key (key x) = x := Function.leftInverse_invFun inj x
  have trace : (D.image key).filter (fun y => (e ∘ Function.invFun key) y ∈ Finset.Icc l u) = X.image key := by
    rw [Finset.filter_image]
    simp only [X,Function.comp_apply,back]
  dsimp only at bound ⊢
  rw [trace,Finset.card_image_of_injective _ inj,Finset.filter_image,Finset.card_image_of_injective _ inj] at bound
  exact bound.trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.monotone_filter_right X
    (fun x hx => earned_pull key inj move h x hx))))

private def below {d} (e : ℕ → Lattice d) (D : Finset ℕ) (x : ℕ) := D.filter fun y => e y ≤ e x

private theorem below_strict {d} (e : ℕ → Lattice d) (D : Finset ℕ) {x y : ℕ}
    (hy : y ∈ D) (less : e x < e y) : (below e D x).card < (below e D y).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.monotone_filter_right D (fun _ (h : _ ≤ e x) => h.trans less.le),?_⟩
  intro eq
  have mem : y ∈ below e D y := mem_filter.mpr ⟨hy,le_rfl⟩
  rw [←eq] at mem
  exact less.not_ge (mem_filter.mp mem).2

private theorem sorted_key {d} (e : ℕ → Lattice d) (inj : Function.Injective e) (D : Finset ℕ)
    (chain : ∀ x ∈ D, ∀ y ∈ D, e x ≤ e y ∨ e y ≤ e x) :
    ∃ key : ℕ → ℕ, Function.Injective key ∧ ∀ x ∈ D, ∀ y ∈ D, key x ≤ key y → e x ≤ e y := by
  let key (x : ℕ) := if x ∈ D then 2*(below e D x).card else 2*x+1
  have ordered : ∀ x ∈ D, ∀ y ∈ D, key x ≤ key y → e x ≤ e y := by
    intro x hx y hy h
    by_contra no
    have lt := below_strict e D hx (lt_of_le_not_ge ((chain x hx y hy).resolve_left no) no)
    simp only [key,if_pos hx,if_pos hy] at h
    omega
  refine ⟨key,fun x y eq => ?_,ordered⟩
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · exact inj (le_antisymm (ordered x hx y hy eq.le) (ordered y hy x hx eq.ge))
  all_goals simp [key,hx,hy] at eq; omega

/-- Every finite chain board admits the half quota with a constant boundary
loss independent of the index order, the location and the board size. -/
theorem board_response {d} (e : ℕ → Lattice d) (inj : Function.Injective e) (D : Finset ℕ)
    (chain : ∀ x ∈ D, ∀ y ∈ D, e x ≤ e y ∨ e y ≤ e x) : BoardResponse e 0 1 D := by
  obtain ⟨key,key_inj,ordered⟩ := sorted_key e inj D chain
  let E := D.image key
  let g := e ∘ Function.invFun key
  let row (_ : ℕ) : ℕ := 0
  apply of_renaming e key key_inj D
  apply (board_response_iff ..).mpr
  have sort : ChainRows.OrderedOn g row E := by
    rintro _ hx _ hy _ hxy
    obtain ⟨x,hDx,rfl⟩ := mem_image.mp hx
    obtain ⟨y,hDy,rfl⟩ := mem_image.mp hy
    change e (Function.invFun key (key x)) ≤ e (Function.invFun key (key y))
    rw [Function.leftInverse_invFun key_inj x,Function.leftInverse_invFun key_inj y]
    exact ordered x hDx y hDy hxy
  obtain ⟨move,legal,count⟩ := ChainRows.rectangle_count g row E sort
  refine ⟨move,legal,fun h _ full l u wide => ?_⟩
  let T := E.filter (fun x => g x ∈ Finset.Icc l u)
  have rows : (T.image row).card ≤ 1 := Finset.card_le_one.mpr (by simp [row])
  have bound := count h full.ge l u
  change T.card ≤ 2*(T.filter (· ∈ earned move h)).card+2*(T.image row).card at bound
  have counted : T.card ≤ 2*(T.filter (· ∈ earned move h)).card+2 := by omega
  have q : (T.card:ℝ) ≤ 2*(T.filter (· ∈ earned move h)).card+2 := by exact_mod_cast counted
  have vol := Finset.prod_pos (s:=Finset.univ) (fun i _ => (show 0 < (u i-l i).toNat by have := wide i; omega))
  have logn := Real.log_nonneg (show (1:ℝ) ≤ geometricVolume l u by exact_mod_cast vol)
  change (1/2-0)*(T.card:ℝ)-1*(1+log (geometricVolume l u)) ≤ (T.filter (· ∈ earned move h)).card
  linarith

/-- Each target that is a coordinatewise chain attains the bound. Targets
may use different chains and their indices may be in any order. -/
theorem on_chain_targets {d} (e : ℕ → Lattice d) (inj : Function.Injective e) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {n : ℕ} (rank : TowerTopology.FiniteRankAtMost (Set.range C) n)
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z s, Set.range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ((∀ x ∈ C z, ∀ y ∈ C z, e x ≤ e y ∨ e y ≤ e x) →
        ENNReal.ofReal (1/2) ≤ filteredRectangularDensity f (Set.range (cubePlay G s)) (e '' C z)) := by
  obtain ⟨G,works⟩ := filtered_generation_on_supported_targets e inj (le_refl (0:ℝ)) f grows C inf rank
  refine ⟨G,fun z s full => ?_⟩
  obtain ⟨valid,lower⟩ := works z s full
  refine ⟨valid,fun chain => ?_⟩
  simpa only [sub_zero] using lower ⟨1,zero_le_one,fun D sub => board_response e inj D
    (fun x hx y hy => chain x (sub hx) y (sub hy))⟩

/-- On the full integer line every finite board is a chain, in any naming
of its points. The sharp half guarantee holds for all divergent filters. -/
theorem integer_line (e : ℕ → Lattice 1) (inj : Function.Injective e) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {n : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) n)
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) :
    ∃ G : List (Lattice 1) → Lattice 1, ∀ z s, Set.range s = e '' C z →
      cubeValid G s (e '' C z) ∧ ENNReal.ofReal (1/2) ≤ filteredRectangularDensity f (range (cubePlay G s)) (e '' C z) := by
  obtain ⟨G,works⟩ := on_chain_targets e inj C inf rank f grows
  refine ⟨G,fun z s full => ?_⟩
  obtain ⟨valid,lower⟩ := works z s full
  refine ⟨valid,lower (fun x _ y _ => ?_)⟩
  rcases le_total (e x 0) (e y 0) with h | h
  · exact Or.inl fun i => Fin.eq_zero i ▸ h
  · exact Or.inr fun i => Fin.eq_zero i ▸ h

end
end GenLimit.KleinbergWei.Banach.OrderedBoards
