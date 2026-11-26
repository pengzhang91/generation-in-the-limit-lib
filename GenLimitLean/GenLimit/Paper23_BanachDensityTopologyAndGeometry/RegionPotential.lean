import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ClaimInvariant

/-! The active regions of the finite rectangle game in Kleinberg and Wei,
arXiv:2611.14887v1, Appendix A. A point belongs to a chain of regions.
Activation delegates its points away from proper ancestors. Credits already
earned by White remain with the regions that counted those claims. -/
namespace GenLimit.KleinbergWei.Banach.RegionGame
open Finset
open scoped Classical
noncomputable section
variable {V : Type*} [PartialOrder V]

/-- Smaller vertices are ancestors. Vertices may have identical board
traces, for example at consecutive geometric scales of a sparse board. -/
structure Hierarchy (V : Type*) [PartialOrder V] where
  board : Finset ℕ
  region : V → Finset ℕ
  root : V
  cover : board ⊆ region root
  nested : ∀ {v u}, v ≤ u → region u ⊆ region v
  path : ∀ {x v u}, x ∈ region v → x ∈ region u → v ≤ u ∨ u ≤ v

structure State (V : Type*) where
  free : Finset ℕ
  white : Finset ℕ
  active : Finset V
  credit : V → Finset ℕ

open Hierarchy
variable (T : Hierarchy V)

def Hierarchy.start : State V := ⟨T.board, ∅, {T.root}, fun _ => ∅⟩

def Hierarchy.effective (s : State V) (v : V) (x : ℕ) : Prop :=
  x ∈ T.region v ∧ ∀ u ∈ s.active, v < u → x ∉ T.region u

def Hierarchy.available (s : State V) (v : V) : Finset ℕ := s.free.filter (T.effective s v)

def black (s : State V) (x : ℕ) : State V := {s with free := s.free.erase x}

def activate (s : State V) (u : V) : State V := {s with active := insert u s.active}

def Hierarchy.white (s : State V) (y : ℕ) : State V :=
  {s with
    free := s.free.erase y
    white := insert y s.white
    credit := fun v => if T.effective s v y then insert y (s.credit v) else s.credit v}

private theorem effective_disjoint {s : State V} {v u : V} {x : ℕ}
    (av : v ∈ s.active) (au : u ∈ s.active) (ne : v ≠ u)
    (ev : T.effective s v x) : ¬ T.effective s u x := by
  intro eu
  rcases T.path ev.1 eu.1 with le | le
  · exact ev.2 u au (lt_of_le_of_ne le ne) eu.1
  · exact eu.2 v av (lt_of_le_of_ne le ne.symm) ev.1

private theorem effective_activate {s : State V} {v u : V} (away : ¬ v < u) (x : ℕ) :
    T.effective (activate s u) v x ↔ T.effective s v x := by
  simp [effective,activate,away]

variable (P : State V → V → ℝ)

def score (s : State V) (v : V) (x : ℕ) : ℝ := P (black s x) v - P s v

/-- Including zero handles a pass when the effective board is exhausted. -/
def Hierarchy.peak (s : State V) (v : V) : ℝ :=
  (insert 0 ((T.available s v).image (score P s v))).max' (Finset.insert_nonempty ..)

def Hierarchy.reserve (s : State V) (v : V) := P s v + T.peak P s v

def Small (s : State V) := ∀ v, P s v ≤ 1/4

/-- A free point can receive its first White credit in any region that
still counts it. Numerical bounds for a White claim use this condition. -/
def FreshCredits (s : State V) := ∀ v, Disjoint s.free (s.credit v)

private theorem peak_nonneg (s : State V) (v : V) : 0 ≤ T.peak P s v :=
  Finset.le_max' _ 0 (Finset.mem_insert_self ..)

private theorem score_le_peak {s : State V} {v : V} {x : ℕ} (hx : x ∈ T.available s v) :
    score P s v x ≤ T.peak P s v := Finset.le_max' _ _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))

private theorem peak_le {s : State V} {v : V} {a : ℝ} (pos : 0 ≤ a)
    (bound : ∀ x ∈ T.available s v, score P s v x ≤ a) : T.peak P s v ≤ a := by
  apply Finset.max'_le
  simp only [Finset.mem_insert,Finset.mem_image]
  rintro _ (rfl | ⟨x,hx,rfl⟩)
  · exact pos
  · exact bound x hx

/-- Locality, bounded one-move effects, greedy White advantage and delegation
from Appendix A, (P2)–(P4). The strategy will only invoke the numerical
hypotheses while every region has potential at most one quarter. -/
structure Laws (σ : ℝ) : Prop where
  nonneg : ∀ s v, 0 ≤ P s v
  sigma_nonneg : 0 ≤ σ
  sigma_le : σ ≤ 1/16
  black_far : ∀ s v x, x ∈ s.free → ¬ T.effective s v x → P (black s x) v = P s v
  white_far : ∀ s v y, y ∈ s.free → ¬ T.effective s v y → P (T.white s y) v = P s v
  activate_far : ∀ s v u, ¬ v < u → P (activate s u) v = P s v
  black_score : ∀ s, Small P s → ∀ v x, x ∈ T.available s v →
    0 ≤ score P s v x ∧ score P s v x ≤ σ * P s v
  white_le : ∀ s, Small P s → FreshCredits s → ∀ v y, y ∈ s.free → P (T.white s y) v ≤ P s v
  white_gain : ∀ s, Small P s → FreshCredits s → ∀ v y, y ∈ T.available s v →
    P (T.white s y) v ≤ P s v - (1+8*σ)*score P s v y
  remaining_score : ∀ s, Small P s → FreshCredits s → ∀ v y, y ∈ T.available s v →
    ∀ x ∈ T.available (T.white s y) v, score P (T.white s y) v x ≤ (1+2*σ)*score P s v x
  delegate_potential : ∀ s, Small P s → ∀ u, u ∉ s.active → 1/12 ≤ P s u →
    ∀ x ∈ T.available s u, ∀ v, v < u →
      P (activate (black s x) u) v ≤ P s v

variable {T P} {σ : ℝ} (law : Laws T P σ)

include law in
private theorem peak_small {s : State V} (small : Small P s) (v : V) :
    T.peak P s v ≤ σ * P s v :=
  peak_le T P (mul_nonneg law.sigma_nonneg (law.nonneg ..))
    fun x mem => (law.black_score _ small _ x mem).2

include law in
private theorem black_le_reserve {s : State V} {x : ℕ} (free : x ∈ s.free) (v : V) :
    P (black s x) v ≤ T.reserve P s v := by
  by_cases eff : T.effective s v x
  · have h := score_le_peak T P (Finset.mem_filter.mpr ⟨free,eff⟩ : x ∈ T.available s v)
    unfold score at h; unfold reserve; linarith
  · rw [law.black_far _ _ _ free eff]; exact le_add_of_nonneg_right (peak_nonneg ..)

include law in
private theorem reserve_black_far {s : State V} {v : V} {x : ℕ}
    (free : x ∈ s.free) (far : ¬ T.effective s v x) :
    T.reserve P (black s x) v ≤ T.reserve P s v := by
  have unchanged := law.black_far _ _ _ free far
  apply add_le_add unchanged.le
  apply peak_le T P (peak_nonneg ..)
  intro y hy
  obtain ⟨fy,eff⟩ := Finset.mem_filter.mp hy
  obtain ⟨ne,old⟩ := Finset.mem_erase.mp fy
  have commute : black (black s x) y = black (black s y) x := by
    simp only [black,Finset.erase_right_comm]
  have eq := law.black_far (black s y) v x (Finset.mem_erase.mpr ⟨ne.symm,free⟩) far
  simpa only [score,commute,eq,unchanged] using
    (show score P s v y ≤ T.peak P s v from score_le_peak T P (Finset.mem_filter.mpr ⟨old,eff⟩))

include law in
private theorem reserve_white_far {s : State V} {v : V} {y : ℕ}
    (free : y ∈ s.free) (far : ¬ T.effective s v y) :
    T.reserve P (T.white s y) v ≤ T.reserve P s v := by
  have unchanged := law.white_far _ _ _ free far
  apply add_le_add unchanged.le
  apply peak_le T P (peak_nonneg ..)
  intro x hx
  obtain ⟨fx,eff⟩ := Finset.mem_filter.mp hx
  obtain ⟨ne,old⟩ := Finset.mem_erase.mp fx
  have commute : black (T.white s y) x = T.white (black s x) y := by
    simp only [white,black,effective,Finset.erase_right_comm,State.mk.injEq,true_and]
    funext w
    split_ifs <;> rfl
  have eq := law.white_far (black s x) v y (Finset.mem_erase.mpr ⟨ne.symm,free⟩) far
  simpa only [score,commute,eq,unchanged] using
    (show score P s v x ≤ T.peak P s v from score_le_peak T P (Finset.mem_filter.mpr ⟨old,eff⟩))

include law in
private theorem reserve_activate_far (s : State V) {v u : V} (away : ¬ v < u) :
    T.reserve P (activate s u) v ≤ T.reserve P s v := by
  have unchanged := law.activate_far s v u away
  apply add_le_add unchanged.le
  apply peak_le T P (peak_nonneg ..)
  intro x hx
  obtain ⟨free,eff⟩ := Finset.mem_filter.mp hx
  have eq := law.activate_far (black s x) v u away
  change P (activate (black s x) u) v - P (activate s u) v ≤ _
  rw [eq,unchanged]
  exact score_le_peak T P (Finset.mem_filter.mpr ⟨free,(effective_activate T away x).mp eff⟩)

/-- The root remains active, only board points remain free, and each
previously credited point belongs to White. -/
structure Accounting (T : Hierarchy V) (s : State V) : Prop where
  root_active : T.root ∈ s.active
  inside : s.free ⊆ T.board
  credits : ∀ v, s.credit v ⊆ s.white
  fresh : Disjoint s.free s.white

private theorem accounting_black {s : State V} (h : Accounting T s) (x : ℕ) :
    Accounting T (black s x) :=
  ⟨h.root_active,(Finset.erase_subset ..).trans h.inside,h.credits,h.fresh.mono_left (Finset.erase_subset ..)⟩

private theorem accounting_activate {s : State V} (h : Accounting T s) (u : V) :
    Accounting T (activate s u) :=
  ⟨Finset.mem_insert_of_mem h.root_active,h.inside,h.credits,h.fresh⟩

private theorem accounting_white {s : State V} (h : Accounting T s) (y : ℕ) :
    Accounting T (T.white s y) := by
  refine ⟨h.root_active,(Finset.erase_subset ..).trans h.inside,fun v => ?_,?_⟩
  · dsimp only [white]
    split
    · exact Finset.insert_subset_insert _ (h.credits v)
    · exact (h.credits v).trans (Finset.subset_insert ..)
  · exact Finset.disjoint_insert_right.mpr
      ⟨Finset.notMem_erase _ _,h.fresh.mono_left (Finset.erase_subset ..)⟩

private def Bounded (T : Hierarchy V) (P : State V → V → ℝ) (s : State V) : Prop :=
  (∀ v ∈ s.active, T.reserve P s v ≤ 1/4) ∧ ∀ v ∉ s.active, P s v < 1/8

private def Ready (T : Hierarchy V) (P : State V → V → ℝ) (s : State V) (u : V) : Prop :=
  u ∈ s.active ∧ P s u ≤ 1/4 ∧
  (∀ v ∈ s.active, v ≠ u → T.reserve P s v ≤ 1/4) ∧ ∀ v ∉ s.active, P s v < 1/8

private theorem active_potential (s : State V) (v : V) : P s v ≤ T.reserve P s v :=
  le_add_of_nonneg_right (peak_nonneg ..)

private theorem bounded_small {s : State V} (b : Bounded T P s) : Small P s := by
  intro v
  by_cases active : v ∈ s.active
  · exact (active_potential ..).trans (b.1 v active)
  · linarith [b.2 v active]

private theorem ready_small {s : State V} {u : V} (r : Ready T P s u) : Small P s := by
  intro v
  by_cases eq : v = u
  · exact eq ▸ r.2.1
  by_cases active : v ∈ s.active
  · exact (active_potential ..).trans (r.2.2.1 v active eq)
  · linarith [r.2.2.2 v active]

include law in
private theorem next_small {s : State V} (b : Bounded T P s) {x} (free : x ∈ s.free) :
    Small P (black s x) := by
  intro v
  apply (black_le_reserve law free v).trans
  by_cases active : v ∈ s.active
  · exact b.1 v active
  · have pk := peak_small law (bounded_small b) v
    have cap := mul_le_mul_of_nonneg_right law.sigma_le (law.nonneg s v)
    unfold reserve
    linarith [b.2 v active]

include law in
/-- The potential part of (P4) also protects the reserve. Test it a second
time after a hypothetical Black claim outside the delegated region. -/
theorem reserve_of_delegation {s : State V} (small : Small P s)
    (next : ∀ y ∈ s.free, Small P (black s y)) {u v : V}
    (inactive : u ∉ s.active) (warning : 1/12 ≤ P s u) {x : ℕ}
    (claim : x ∈ T.available s u) (anc : v < u) :
    T.reserve P (activate (black s x) u) v ≤ T.reserve P s v := by
  let t := activate (black s x) u
  have drop := law.delegate_potential s small u inactive warning x claim v anc
  have base := drop.trans (active_potential (T:=T) (P:=P) s v)
  change P t v + T.peak P t v ≤ T.reserve P s v
  apply le_sub_iff_add_le'.mp
  apply peak_le T P (sub_nonneg.mpr base)
  intro y hy
  obtain ⟨fy,eff⟩ := Finset.mem_filter.mp hy
  obtain ⟨ne,old⟩ := Finset.mem_erase.mp fy
  have outside := eff.2 u (Finset.mem_insert_self ..) anc
  have stable := law.black_far s u y old (fun h => outside h.1)
  have claim' : x ∈ T.available (black s y) u := Finset.mem_filter.mpr
    ⟨Finset.mem_erase.mpr ⟨ne.symm,(Finset.mem_filter.mp claim).1⟩,(Finset.mem_filter.mp claim).2⟩
  have second := law.delegate_potential (black s y) (next y old) u inactive
    (stable.symm ▸ warning) x claim' v anc
  have commute : black t y = activate (black (black s y) x) u := by
    simp only [t,black,activate,Finset.erase_right_comm]
  change P (black t y) v - P t v ≤ _
  exact sub_le_sub_right ((congrArg (fun a => P a v) commute).le.trans
    (second.trans (black_le_reserve law old v))) _

private theorem finish_ready {s : State V} {u : V} (ready : Ready T P s u)
    (safe : T.reserve P s u ≤ 1/4) : Bounded T P s := by
  refine ⟨fun v av => ?_,ready.2.2.2⟩
  by_cases eq : v = u
  · simpa [eq] using safe
  · exact ready.2.2.1 v av eq

include law in
private theorem settle {s : State V} {u : V} (account : Accounting T s) (ready : Ready T P s u) :
    Bounded T P s ∨ ∃ y ∈ s.free, Bounded T P (T.white s y) := by
  let available := T.available s u
  have fresh : FreshCredits s := fun v => account.fresh.mono_right (account.credits v)
  by_cases somePoint : available.Nonempty
  · obtain ⟨y,hy,maximal⟩ := available.exists_max_image (score P s u) somePoint
    have free := (Finset.mem_filter.mp hy).1
    have small := ready_small ready
    have pos := (law.black_score s small u y hy).1
    have mult : 0 ≤ 1+2*σ := by linarith [law.sigma_nonneg]
    have cap : T.peak P (T.white s y) u ≤ (1+2*σ)*score P s u y := by
      apply peak_le T P (mul_nonneg mult pos)
      intro x hx
      obtain ⟨fx,eff⟩ := Finset.mem_filter.mp hx
      have old : x ∈ available :=
        Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase fx,eff⟩
      exact (law.remaining_score _ small fresh u y hy x hx).trans
        (mul_le_mul_of_nonneg_left (maximal x old) mult)
    refine Or.inr ⟨y,free,fun v av => ?_,fun v inactive => ?_⟩
    · by_cases eq : v = u
      · subst v
        have gain := law.white_gain s small fresh u y hy
        unfold reserve
        nlinarith only [gain,cap,ready.2.1,mul_nonneg law.sigma_nonneg pos]
      · have far := effective_disjoint T ready.1 av (Ne.symm eq) (Finset.mem_filter.mp hy).2
        exact (reserve_white_far law free far).trans (ready.2.2.1 v av eq)
    · exact (law.white_le s small fresh v y free).trans_lt (ready.2.2.2 v inactive)
  · apply Or.inl
    apply finish_ready ready
    have cap : T.peak P s u ≤ 0 := peak_le T P le_rfl (fun x hx => (somePoint ⟨x,hx⟩).elim)
    unfold reserve; linarith [ready.2.1]

include law in
private theorem prepare [Fintype V] {s : State V} (acc : Accounting T s) (b : Bounded T P s)
    {x : ℕ} (free : x ∈ s.free) :
    ∃ t u, t.free = s.free.erase x ∧ t.white = s.white ∧ Accounting T t ∧ Ready T P t u := by
  let B := black s x
  let danger := Finset.univ.filter (fun v => v ∉ s.active ∧ 1/8 ≤ P B v)
  have danger_iff (v : V) : v ∈ danger ↔ v ∉ s.active ∧ 1/8 ≤ P B v := by simp [danger]
  have crossed {v : V} (threat : v ∈ danger) : T.effective s v x := by
    by_contra far
    obtain ⟨inactive,high⟩ := (danger_iff v).mp threat
    rw [show P B v = P s v from law.black_far _ _ _ free far] at high
    exact (b.2 v inactive).not_ge high
  have post : Small P B := next_small law b free
  by_cases any : danger.Nonempty
  · obtain ⟨u,threat,deep⟩ := danger.exists_maximal any
    obtain ⟨inactive,high⟩ := (danger_iff u).mp threat
    have eu := crossed threat
    have xu : x ∈ T.available s u := Finset.mem_filter.mpr ⟨free,eu⟩
    have delta := (law.black_score s (bounded_small b) u x xu).2
    have cap := mul_le_mul_of_nonneg_right law.sigma_le (law.nonneg s u)
    have before : 1/12 ≤ P s u := by
      change P B u - P s u ≤ _ at delta
      linarith
    let t := activate B u
    have delegation := law.delegate_potential s (bounded_small b) u inactive before x xu
    refine ⟨t,u,rfl,rfl,accounting_activate (accounting_black acc x) u,
      Finset.mem_insert_self ..,?_,?_,?_⟩
    · exact (law.activate_far B u u (lt_irrefl u)).le.trans (post u)
    · intro v av ne
      have was : v ∈ s.active := (Finset.mem_insert.mp av).resolve_left ne
      by_cases anc : v < u
      · exact (reserve_of_delegation law (bounded_small b) (fun _ => next_small law b)
          inactive before xu anc).trans (b.1 v was)
      · have far : ¬ T.effective s v x := by
          intro ev
          rcases T.path ev.1 eu.1 with le | le
          · exact anc (lt_of_le_of_ne le ne)
          · exact eu.2 v was (lt_of_le_of_ne le ne.symm) ev.1
        exact (reserve_activate_far law B anc).trans ((reserve_black_far law free far).trans (b.1 v was))
    · intro v off
      have absent : v ≠ u ∧ v ∉ s.active := by simpa [t,activate,B,black] using off
      by_cases anc : v < u
      · exact (delegation v anc).trans_lt (b.2 v absent.2)
      · rw [show P t v = P B v from law.activate_far B v u anc]
        by_contra! highv
        have th := (danger_iff v).mpr ⟨absent.2,highv⟩
        rcases T.path (crossed th).1 eu.1 with le | le
        · exact anc (lt_of_le_of_ne le absent.1)
        · exact absent.1 (le_antisymm (deep th le) le)
  · let containing := s.active.filter (fun v => x ∈ T.region v)
    have root : T.root ∈ containing := Finset.mem_filter.mpr ⟨acc.root_active,T.cover (acc.inside free)⟩
    obtain ⟨u,mem,deep⟩ := containing.exists_maximal ⟨_,root⟩
    obtain ⟨au,inside⟩ := Finset.mem_filter.mp mem
    have eu : T.effective s u x := ⟨inside,fun v av lt hit =>
      lt.not_ge (deep (Finset.mem_filter.mpr ⟨av,hit⟩) lt.le)⟩
    refine ⟨B,u,rfl,rfl,accounting_black acc x,au,post u,?_,?_⟩
    · intro v av ne
      have far := effective_disjoint T au av ne.symm eu
      exact (reserve_black_far law free far).trans (b.1 v av)
    · intro v inactive
      by_contra! high
      exact any ⟨v,(danger_iff v).mpr ⟨inactive,high⟩⟩

include law in
/-- Appendix A, Lemma A.2. One alternating strategy meets all quotas. The
terminal test uses actual White claims; (P1) can detect failure using only
the smaller sets of claims credited locally before delegation. -/
theorem canForce_quotas [Fintype V] (requests : V → Finset (Finset ℕ))
    (demand : V → Finset ℕ → ℝ) (initial : ∀ v, P T.start v ≤ 1/16)
    (detect : ∀ s : State V, Accounting T s → s.free = ∅ → ∀ v, ∀ Q ∈ requests v,
      ((s.credit v ∩ Q).card : ℝ) < demand v Q → 1 ≤ P s v) :
    ClaimGame.CanForce T.board (fun W => ∀ v, ∀ Q ∈ requests v,
      demand v Q ≤ (Q.filter (· ∈ W)).card) := by
  let good (F W : Finset ℕ) := ∃ s, s.free = F ∧ s.white = W ∧ Accounting T s ∧ Bounded T P s
  apply ClaimGame.canForce_of_invariant good
  · refine ⟨T.start,rfl,rfl,⟨Finset.mem_singleton_self _,Finset.Subset.rfl,fun _ => Finset.Subset.rfl,
      Finset.disjoint_empty_right _⟩,
      fun v _ => ?_,fun v _ => ?_⟩
    · have small : Small P T.start := fun w => by linarith [initial w]
      have cap := peak_small law small v
      have prod := mul_le_mul_of_nonneg_right law.sigma_le (law.nonneg T.start v)
      unfold reserve; linarith [initial v]
    · linarith [initial v]
  · rintro F W ⟨s,rfl,rfl,acc,b⟩ x free
    obtain ⟨t,u,ft,wt,acct,ready⟩ := prepare law acc b free
    rcases settle law acct ready with pass | ⟨y,fy,after⟩
    · exact Or.inl ⟨t,ft,wt,acct,pass⟩
    · exact Or.inr ⟨y,ft ▸ fy,T.white t y,congrArg (fun a => a.erase y) ft,
        congrArg (insert y) wt,accounting_white acct y,after⟩
  · rintro W ⟨s,empty,rfl,acc,b⟩ v Q mem
    by_contra! missed
    simp only [Finset.mem_coe,Finset.filter_mem_eq_inter] at missed
    have subset : s.credit v ∩ Q ⊆ Q ∩ s.white :=
      fun x hx => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2,acc.credits v (Finset.mem_inter.mp hx).1⟩
    have high := detect s acc empty v Q mem ((Nat.cast_le.mpr (Finset.card_le_card subset)).trans_lt missed)
    linarith [bounded_small b v]

end
end GenLimit.KleinbergWei.Banach.RegionGame
