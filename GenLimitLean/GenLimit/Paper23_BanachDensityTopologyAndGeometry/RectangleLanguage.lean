import GenLimit.Paper23_BanachDensityTopologyAndGeometry.GeneralPosition
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.CenteredCubes

/-! An infinite language in every lattice of dimension at least two.
Block j consists of two disjoint translates of a point set forcing a
monochromatic rectangle with at least j+1 points. Cropping a rectangle at
the edge of its copy preserves its trace and isolates it from every other copy. -/
namespace GenLimit.KleinbergWei.Banach.Rectangles
open Stages Set
open scoped Classical
noncomputable section

def sample (j : ℕ) := (finite_rectangle_distinct (j+1) (Nat.succ_pos _)).choose

theorem force (j : ℕ) (color : Point → Bool) : Monochromatic (sample j) (j+1) color :=
  (finite_rectangle_distinct (j+1) (Nat.succ_pos _)).choose_spec.2 color

private theorem distinct (j : ℕ) : GeneralPosition (sample j) :=
  (finite_rectangle_distinct (j+1) (Nat.succ_pos _)).choose_spec.1

private theorem nonempty_sample (j : ℕ) : (sample j).Nonempty := by
  obtain ⟨lo,hi,_,h,_⟩ := force j (fun _ => true)
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos j) h)
  exact ⟨p,(mem_trace.mp hp).1⟩

private def extent (j : ℕ) := max ((sample j).sup Prod.fst) ((sample j).sup Prod.snd)
private theorem capX {j : ℕ} {p : Point} (h : p ∈ sample j) : p.1 ≤ extent j :=
  (Finset.le_sup h).trans (le_max_left ..)

private theorem capY {j : ℕ} {p : Point} (h : p ∈ sample j) : p.2 ≤ extent j :=
  (Finset.le_sup h).trans (le_max_right ..)

private def base : ℕ → ℕ
  | 0 => 0
  | j+1 => base j + 2*(extent j+1)
private def start (j : ℕ) (b : Bool) := base j + (if b then extent j+1 else 0)

private theorem base_strict : StrictMono base := by
  apply strictMono_nat_of_lt_succ; intro j
  change base j < base j+2*(extent j+1); omega

private theorem bounds (j : ℕ) (b : Bool) : base j ≤ start j b ∧
    start j b + extent j < base (j+1) := by
  cases b <;> simp [start,base] <;> omega

private def lift (d : ℕ) (p : Point) : Lattice (d+2) :=
  Fin.cons (p.1 : ℤ) (Fin.cons (p.2 : ℤ) (fun _ => (p.1 : ℤ)))

private theorem lift_le {d : ℕ} {p q : Point} : lift d p ≤ lift d q ↔ p ≤ q := by
  unfold lift
  rw [Fin.cons_le_cons,Fin.cons_le_cons]
  exact ⟨fun h => ⟨Int.ofNat_le.mp h.1,Int.ofNat_le.mp h.2.1⟩,
    fun h => ⟨Int.ofNat_le.mpr h.1,Int.ofNat_le.mpr h.2,fun _ => Int.ofNat_le.mpr h.1⟩⟩

private theorem lift_inj (d : ℕ) : Function.Injective (lift d) := by
  intro p q h; exact le_antisymm (lift_le.mp h.le) (lift_le.mp h.ge)

def place (d j : ℕ) (b : Bool) (p : Point) := lift d (start j b+p.1,start j b+p.2)

private theorem place_inj (d j : ℕ) (b : Bool) : Function.Injective (place d j b) := by
  intro p q h; have same := lift_inj d h
  have fstEq := congrArg Prod.fst same
  have sndEq := congrArg Prod.snd same
  exact Prod.ext (Nat.add_left_cancel fstEq) (Nat.add_left_cancel sndEq)

private theorem unique_band {j k : ℕ} {b c : Bool} {x : ℕ}
    (l : start j b ≤ x) (u : x ≤ start j b + extent j)
    (l' : start k c ≤ x) (u' : x ≤ start k c + extent k) : j=k ∧ b=c := by
  obtain ⟨leftL,leftU⟩ := bounds j b
  obtain ⟨rightL,rightU⟩ := bounds k c
  have same : j=k := by
    rcases lt_trichotomy j k with lt | eq | gt
    · have inter : base (j+1) ≤ base k := base_strict.monotone lt
      omega
    · exact eq
    · have inter : base (k+1) ≤ base j := base_strict.monotone gt
      omega
  subst k
  exact ⟨rfl,by cases b <;> cases c <;> simp_all [start] <;> omega⟩

def put (d j : ℕ) : Bool × (sample j) ↪ Lattice (d+2) where
  toFun v := place d j v.1 v.2.val
  inj' := by
    rintro ⟨b,⟨p,hp⟩⟩ ⟨c,⟨q,hq⟩⟩ h
    have same := lift_inj d h
    have x : start j b+p.1=start j c+q.1 := congrArg Prod.fst same
    have ub : p.1 ≤ extent j := capX hp
    have vb : q.1 ≤ extent j := capX hq
    obtain ⟨_,rfl⟩ := unique_band (j:=j) (k:=j) (b:=b) (c:=c) (x:=start j b+p.1)
      (by omega) (by omega) (by omega) (by omega)
    exact Prod.ext rfl (Subtype.ext (place_inj d j b h))

def language (d : ℕ) : Set (Lattice (d+2)) := {x | ∃ j bi, put d j bi = x}

theorem contains (d j : ℕ) (bi) : put d j bi ∈ language d := ⟨j,bi,rfl⟩

private def axis {d : ℕ} (i : Fin (d+2)) : Point → ℕ :=
  if i = (0 : Fin (d+1)).succ then Prod.snd else Prod.fst

private theorem project (d j : ℕ) (b : Bool) (p : Point) (i : Fin (d+2)) :
    place d j b p i = (start j b + axis i p : ℕ) := by
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [place,lift,axis]
  · refine Fin.cases ?_ (fun v => ?_) a
    · simp [place,lift,axis]
    · have ne : v.succ.succ ≠ (0 : Fin (d+1)).succ := fun e => Fin.succ_ne_zero _ (Fin.succ_inj.mp e)
      simp only [place,lift,Fin.cons_succ,axis,if_neg ne]

/-- Each lattice hyperplane perpendicular to a coordinate axis contains
at most one word of the target. -/
theorem thin {d : ℕ} (i : Fin (d+2)) : InjOn (fun x => x i) (language d) := by
  rintro _ ⟨j,⟨b,⟨p,hp⟩⟩,rfl⟩ _ ⟨k,⟨c,⟨q,hq⟩⟩,rfl⟩ same
  change place d j b p i = place d k c q i at same
  simp only [project,Nat.cast_inj] at same
  have cap {t : ℕ} {v : Point} (hv : v ∈ sample t) : axis i v ≤ extent t := by
    unfold axis; split
    · exact capY hv
    · exact capX hv
  have cp := cap hp; have cq := cap hq
  obtain ⟨rfl,rfl⟩ := unique_band (j:=j) (k:=k) (b:=b) (c:=c) (x:=start j b+axis i p)
    (by omega) (by omega) (by omega) (by omega)
  have equal : p=q := by
    have e := Nat.add_left_cancel same
    unfold axis at e
    split at e
    · exact (distinct j).2 hp hq e
    · exact (distinct j).1 hp hq e
  cases equal; rfl

theorem outside {d : ℕ} (S : Finset (Lattice (d+2))) (n : ℕ) :
    ∃ j ≥ n, ∀ bi, put d j bi ∉ S := by
  let j := max n ((S.sup fun x => (x 0).toNat)+1)
  refine ⟨j,le_max_left ..,?_⟩
  intro bi h
  have low : j ≤ start j bi.1 := (base_strict.id_le j).trans (bounds j bi.1).1
  have upper := Finset.le_sup (f:=fun x : Lattice (d+2) => (x 0).toNat) h
  change ((lift d (start j bi.1+bi.2.val.1,start j bi.1+bi.2.val.2) 0).toNat) ≤ _ at upper
  simp [lift] at upper
  have := le_max_right n ((S.sup fun x => (x 0).toNat)+1)
  dsimp only [j] at *; omega

theorem infinite (d : ℕ) : (language d).Infinite := by
  intro h
  obtain ⟨j,_,out⟩ := outside h.toFinset 0
  obtain ⟨p,hp⟩ := nonempty_sample j
  exact out (false,⟨p,hp⟩) (h.mem_toFinset.mpr (contains ..))

def box {d : ℕ} (K : Set (Lattice d)) (l u : Lattice d) :=
  (Finset.Icc l u).filter (· ∈ K)

@[simp] theorem mem_box {d} {K : Set (Lattice d)} {l u x : Lattice d} :
    x ∈ box K l u ↔ (l ≤ x ∧ x ≤ u) ∧ x ∈ K := by simp [box]

/-- Every rectangular trace on a sample can be realized on either copy,
with no contribution from the rest of the infinite language. -/
theorem isolate (d j : ℕ) (b : Bool) (lo hi : Point) :
    ∃ l u, box (language d) l u = (trace (sample j) lo hi).image (place d j b) := by
  refine ⟨place d j b lo,place d j b (min hi.1 (extent j),hi.2),?_⟩
  ext x
  rw [mem_box,Finset.mem_image]
  constructor
  · rintro ⟨⟨lower,upper⟩,k,⟨c,⟨p,hp⟩⟩,rfl⟩
    obtain ⟨lx,ly⟩ := lift_le.mp lower
    obtain ⟨ux,uy⟩ := lift_le.mp upper
    change start j b+lo.1 ≤ start k c+p.1 at lx
    change start k c+p.1 ≤ start j b+min hi.1 (extent j) at ux
    have cp : p.1 ≤ extent k := capX hp
    obtain ⟨rfl,rfl⟩ := unique_band (j:=j) (k:=k) (b:=b) (c:=c) (x:=start k c+p.1)
      (by omega) (by omega) (by omega) (by omega)
    exact ⟨p,mem_trace.mpr ⟨hp,⟨by omega,Nat.le_of_add_le_add_left ly⟩,⟨by omega,Nat.le_of_add_le_add_left uy⟩⟩,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨mem,⟨lx,ly⟩,⟨ux,uy⟩⟩ := mem_trace.mp hp
    have cap : p.1 ≤ extent j := capX mem
    refine ⟨⟨lift_le.mpr ⟨Nat.add_le_add_left lx _,Nat.add_le_add_left ly _⟩,
      lift_le.mpr ⟨Nat.add_le_add_left (le_min ux cap) _,Nat.add_le_add_left uy _⟩⟩,contains d j (b,⟨p,mem⟩)⟩

theorem image_card (d j : ℕ) (b : Bool) (T : Finset Point) :
    (T.image (place d j b)).card = T.card := Finset.card_image_of_injective _ (place_inj ..)

end
end GenLimit.KleinbergWei.Banach.Rectangles
