import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ShellGeneration

/-! A finite criterion with one play for each permutation of the known board.
Projecting an arbitrary input prefix to its first visits preserves every local
response. In particular, a losing board can be witnessed by a genuine
permutation without dummy inputs or repetitions. -/
namespace GenLimit.KleinbergWei.Banach.BoardPermutations
open Set Finset
open scoped Classical
noncomputable section

abbrev Move := List ℕ → ℕ → Option ℕ

def Legal (D : Finset ℕ) (move : Move) :=
  ∀ {h x y}, move h x = some y → x ∈ D ∧ y ∈ D ∧ y ∉ h ++ [x]

/-- Words recommended during a finite history. -/
def earned {V : Type*} (move : List V → V → Option V) (h : List V) : Set V :=
  {y | ∃ p x, (p++[x]) <+: h ∧ move p x = some y}

theorem earned_mono {V : Type*} (move : List V → V → Option V) {h h' : List V} (ext : h <+: h') :
    earned move h ⊆ earned move h' := by
  rintro y ⟨p,x,hp,hit⟩
  exact ⟨p,x,hp.trans ext,hit⟩

theorem earned_push {V : Type*} {move : List V → V → Option V} {h : List V} {x y : V} :
    y ∈ earned move (h++[x]) ↔ y ∈ earned move h ∨ move h x = some y := by
  constructor
  · rintro ⟨p,z,pre,hit⟩
    by_cases short : (p++[z]).length ≤ h.length
    · refine Or.inl ⟨p,z,?_,hit⟩
      exact (List.prefix_iff_eq_take.mpr (by
        rw [List.prefix_iff_eq_take.mp pre, List.length_take]
        simp only [List.length_append,List.length_singleton] at short ⊢
        rw [Nat.min_eq_left (by omega),List.take_append_of_le_length (by omega)]))
    · have eq := pre.eq_of_length (by have := pre.length_le; simp at *; omega)
      have len : p.length = h.length := by simpa using congrArg List.length eq
      obtain ⟨rfl,tail⟩ := List.append_inj eq len
      simpa using Or.inr (show move p x = some y from (List.singleton_inj.mp tail) ▸ hit)
  · rintro (old | hit)
    · exact earned_mono _ (List.prefix_append ..) old
    · exact ⟨h,x,List.prefix_refl _,hit⟩

/-- Test every ordering against the same strategy. -/
def Wins {d} (e : ℕ → Lattice d) (q b : ℝ) (D : Finset ℕ) (move : Move) :=
  ∀ h : List ℕ, h.Nodup → h.toFinset = D → ∀ l u : Lattice d, (∀ i, l i < u i) →
    let X := D.filter (fun x => e x ∈ Finset.Icc l u)
    (1/2-q)*(X.card:ℝ) - b*(1+Real.log (geometricVolume l u)) ≤
      (X.filter (· ∈ earned move h)).card

private def appendNew (D : Finset ℕ) (p : List ℕ) (x : ℕ) :=
  if x ∈ D ∧ x ∉ p then p++[x] else p

def visits (D : Finset ℕ) (h : List ℕ) := h.foldl (appendNew D) []

private theorem visits_push (D : Finset ℕ) (h : List ℕ) (x : ℕ) :
    visits D (h++[x]) = appendNew D (visits D h) x := by simp [visits]

theorem mem_visits (D : Finset ℕ) (h : List ℕ) (y : ℕ) :
    y ∈ visits D h ↔ y ∈ D ∧ y ∈ h := by
  induction h using List.reverseRecOn generalizing y with
  | nil => simp [visits]
  | append_singleton p x ih =>
    rw [visits_push]; simp only [appendNew]
    by_cases eq : y=x
    · subst y
      split_ifs with new <;> simp_all
    · split_ifs with new <;> simp [eq,ih]

theorem distinct_visits (D : Finset ℕ) (h : List ℕ) : (visits D h).Nodup := by
  induction h using List.reverseRecOn with
  | nil => simp [visits]
  | append_singleton p x ih =>
    rw [visits_push]; unfold appendNew
    split
    next new => simpa [List.nodup_append_comm,ih] using new.2
    next => exact ih

private def lifted (D : Finset ℕ) (move : Move) (h : List ℕ) (x : ℕ) :=
  if x ∈ D ∧ x ∉ h then move (visits D h) x else none

private theorem lift_legal {D move} (safe : Legal D move) : Legal D (lifted D move) := by
  intro h x y hit
  unfold lifted at hit
  split at hit
  · obtain ⟨inD,outD,fresh⟩ := safe hit
    simp only [List.mem_append,List.mem_singleton,not_or] at fresh ⊢
    exact ⟨inD,outD,fun old => fresh.1 ((mem_visits ..).2 ⟨outD,old⟩),fresh.2⟩
  · contradiction

private theorem projection (D : Finset ℕ) (move : Move) (h : List ℕ) :
    earned move (visits D h) ⊆ earned (lifted D move) h := by
  induction h using List.reverseRecOn with
  | nil => exact fun _ ⟨p,x,pre,_⟩ => by have := pre.length_le; simp [visits] at this
  | append_singleton h x ih =>
    rw [visits_push]
    by_cases new : x ∈ D ∧ x ∉ h
    · rw [appendNew,if_pos (show x ∈ D ∧ x ∉ visits D h from
        ⟨new.1,fun m => new.2 ((mem_visits ..).1 m).2⟩)]
      intro y hy
      rcases earned_push.mp hy with old | hit
      · exact earned_push.mpr (Or.inl (ih old))
      · exact earned_push.mpr (Or.inr (by simpa [lifted,new] using hit))
    · rw [appendNew,if_neg (by simpa only [mem_visits] using
        (show ¬(x ∈ D ∧ ¬(x ∈ D ∧ x ∈ h)) by tauto))]
      exact ih.trans (earned_mono _ (List.prefix_append ..))

theorem earned_prefix (move : Move) (s : ℕ → ℕ) (n y : ℕ) :
    y ∈ earned move (textPrefix s n) ↔ ∃ t < n, move (textPrefix s t) (s t) = some y := by
  induction n with
  | zero => simp [earned]
  | succ n ih =>
    rw [textPrefix_succ,earned_push,ih]
    constructor
    · rintro (⟨t,ht,hit⟩ | hit)
      · exact ⟨t,by omega,hit⟩
      · exact ⟨n,by omega,hit⟩
    · rintro ⟨t,ht,hit⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with lt | rfl
      · exact Or.inl ⟨t,lt,hit⟩
      · exact Or.inr hit

theorem board_response_iff {d} (e : ℕ → Lattice d) (q b : ℝ) (D : Finset ℕ) :
    BoardResponse e q b D ↔ ∃ move : Move, Legal D move ∧ Wins e q b D move := by
  constructor
  · rintro ⟨move,safe,win⟩
    refine ⟨move,safe,fun h _ covers l u widths => ?_⟩
    let s (i : ℕ) := (h[i]?).getD 0
    have pre : textPrefix s h.length = h := by
      apply List.ext_getElem <;> simp [textPrefix,s]
      intro i hi _; simp [hi]
    have bound := win s h.length (by rw [pre,covers]) l u widths
    simpa only [←earned_prefix,pre] using bound
  · rintro ⟨move,safe,win⟩
    refine ⟨lifted D move,lift_legal safe,fun s n covered l u widths => ?_⟩
    let h := textPrefix s n
    have eq : (visits D h).toFinset = D := by
      ext x; simp only [List.mem_toFinset,mem_visits,and_iff_left_iff_imp]
      exact fun mem => List.mem_toFinset.mp (covered mem)
    have bound := win (visits D h) (distinct_visits ..) eq l u widths
    apply bound.trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro y hy
    obtain ⟨inside,hit⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨inside,(earned_prefix _ _ _ _).mp (projection D move h hit)⟩

theorem finite_response_iff {d} (e : ℕ → Lattice d) (q : ℝ) :
    FiniteRectangleResponse e q ↔
      ∃ b : ℝ, 0 ≤ b ∧ ∀ D, ∃ move : Move, Legal D move ∧ Wins e q b D move := by
  simp only [FiniteRectangleResponse,board_response_iff]

end
end GenLimit.KleinbergWei.Banach.BoardPermutations
