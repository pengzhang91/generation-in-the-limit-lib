import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ClaimGame

/-! Construct an alternating strategy from a position invariant. Auxiliary
memory, such as the active regions in a spatial hierarchy, can be included
in the invariant by existential quantification. -/
namespace GenLimit.KleinbergWei.Banach.ClaimGame
open Finset BoardPermutations
open scoped Classical
noncomputable section

variable (good : Finset ℕ → Finset ℕ → Prop)

private def answer (F W : Finset ℕ) (x : ℕ) : Option ℕ :=
  if x ∈ F then
    if h : ∃ y ∈ F.erase x, good ((F.erase x).erase y) (insert y W) then some h.choose else none
  else none

private def advance (p : Finset ℕ × Finset ℕ) (x : ℕ) : Finset ℕ × Finset ℕ :=
  match answer good p.1 p.2 x with
  | none => (p.1.erase x, p.2)
  | some y => ((p.1.erase x).erase y, insert y p.2)

private def position (D : Finset ℕ) (h : List ℕ) := h.foldl (advance good) (D, ∅)

private def strategy (D : Finset ℕ) (h : List ℕ) (x : ℕ) :=
  answer good (position good D h).1 (position good D h).2 x

private theorem position_spec (D : Finset ℕ) (h : List ℕ) :
    (↑(position good D h).2 : Set ℕ) = earned (strategy good D) h ∧
    ∀ x, x ∈ (position good D h).1 ↔ Free D (strategy good D) h x := by
  induction h using List.reverseRecOn with
  | nil => simp [position,earned,Free]
  | append_singleton h x ih =>
    obtain ⟨white,free⟩ := ih
    have advance_eq : position good D (h ++ [x]) = advance good (position good D h) x := by
      simp [position]
    rw [advance_eq,advance]
    cases reply : answer good (position good D h).1 (position good D h).2 x with
    | none =>
      have pass : strategy good D h x = none := reply
      constructor
      · ext y; simp [←white,earned_push,pass]
      · intro y; simp [free,Free,earned_push,pass]; tauto
    | some z =>
      have hit : strategy good D h x = some z := reply
      constructor
      · ext y; simp [←white,earned_push,hit,eq_comm,or_comm]
      · intro y; simp [free,Free,earned_push,hit,eq_comm]; tauto

/-- If each Black claim admits a pass or a legal reply preserving the
invariant, White can force every terminal consequence of the invariant. -/
theorem canForce_of_invariant (D : Finset ℕ) (quota : Set ℕ → Prop)
    (initial : good D ∅)
    (reply : ∀ F W, good F W → ∀ x ∈ F, good (F.erase x) W ∨
      ∃ y ∈ F.erase x, good ((F.erase x).erase y) (insert y W))
    (terminal : ∀ W, good ∅ W → quota (↑W)) : CanForce D quota := by
  refine ⟨strategy good D, ?_, ?_⟩
  · intro h _ x fx y hy
    have mem := ((position_spec good D h).2 x).mpr fx
    change answer good _ _ _ = some y at hy
    unfold answer at hy
    rw [if_pos mem] at hy
    split at hy
    next ex =>
      cases hy
      obtain ⟨ne,inF⟩ := Finset.mem_erase.mp ex.choose_spec.1
      exact ⟨((position_spec good D h).2 _).mp inF,ne⟩
    next => contradiction
  · intro h play exhausted
    have invariant : good (position good D h).1 (position good D h).2 := by
      clear exhausted
      induction play with
      | start => exact initial
      | @claim h x _ fx ih =>
        have inF := ((position_spec good D h).2 x).mpr fx
        have choices := reply _ _ ih x inF
        have step_eq : position good D (h ++ [x]) = advance good (position good D h) x := by
          simp [position]
        rw [step_eq]
        unfold advance answer
        rw [if_pos inF]
        by_cases ex : ∃ y ∈ (position good D h).1.erase x,
            good (((position good D h).1.erase x).erase y) (insert y (position good D h).2)
        · simpa only [dif_pos ex] using ex.choose_spec.2
        · simpa only [dif_neg ex] using choices.resolve_right ex
    have empty := Finset.eq_empty_iff_forall_notMem.mpr
      (fun x hx => exhausted x (((position_spec good D h).2 x).mp hx))
    rw [empty] at invariant
    rw [←(position_spec good D h).1]
    exact terminal _ invariant

/-- A finite family of weighted tests shares one causal strategy. The
additive loss of each test is determined by its fraction of the total weight. -/
theorem weighted_tests {I : Type*} [Fintype I] (D : Finset ℕ)
    (E : I → Finset ℕ) (inside : ∀ i, E i ⊆ D) (w : I → ℝ) (pos : ∀ i, 0 < w i)
    {q : ℝ} (hq : 0 < q) (small : q ≤ 1/2) :
    CanForce D (fun W => ∀ i, (1/2-q)*((E i).card:ℝ) -
      Real.log ((1+q)*(∑ j, w j)/w i)/(2*q) ≤ ((E i).filter (· ∈ W)).card) := by
  let move (h : List ℕ) (x : ℕ) := FiniteGame.recommend E w q (FiniteGame.run E w q D h) x
  apply (canForce_iff ..).mpr
  refine ⟨move,?_,fun h _ full i => ?_⟩
  · intro h x y hit
    obtain ⟨inD,old,ne⟩ := FiniteGame.recommendation_fresh E w q hit
    exact ⟨FiniteGame.active_input E w q hit,inD,by simpa using And.intro old ne⟩
  · have bound := FiniteGame.covering_bound E w q pos hq small h full.ge i
    rw [Finset.inter_eq_right.mpr (inside i)] at bound
    apply bound.trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
    intro y mem
    obtain ⟨out,member⟩ := Finset.mem_inter.mp mem
    obtain ⟨p,x,t,split,rec⟩ := FiniteGame.output_source E w q (List.mem_toFinset.mp out)
    exact Finset.mem_filter.mpr ⟨member,p,x,⟨t,split.symm⟩,rec⟩

end
end GenLimit.KleinbergWei.Banach.ClaimGame
