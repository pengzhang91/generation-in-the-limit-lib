import GenLimit.Paper23_BanachDensityTopologyAndGeometry.StageCoordinates
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-! A planar integer realization of the two-color stage forest. The first
coordinate gives each root its own band. The second coordinate identifies
the stage. Horizontal rectangles select consecutive roots of one stage,
and a rectangle within a single root band selects all ancestors of a node. -/
namespace GenLimit.KleinbergWei.Banach.Stages
open Set
open scoped Classical
noncomputable section

abbrev History (n : ℕ) := List (Finset (Fin n))
abbrev Point := ℕ × ℕ

def active {n : ℕ} (s : History n) :=
  Finset.univ.filter fun r : Fin n => ∀ T ∈ s, r ∈ T

@[simp] theorem active_nil (n : ℕ) : active ([] : History n) = Finset.univ := by ext; simp [active]

@[simp] theorem active_next {n : ℕ} (s : History n) (T : Finset (Fin n)) :
    active (s++[T]) = active s ∩ T := by
  ext r
  simp [active]; aesop

theorem active_mono {n : ℕ} {s t : History n} (pre : s <+: t) : active t ⊆ active s := by
  intro r hr
  simp only [active,Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
  exact fun T hT => hr T (pre.subset hT)

def digits (n : ℕ) := Fintype.equivFin (Finset (Fin n))
def span (n d : ℕ) := width (Fintype.card (Finset (Fin n))) d
def row {n : ℕ} (d : ℕ) (s : History n) := address (digits n) d s
def offset {n : ℕ} (d : ℕ) (s : History n) := address (fun x => (digits n x).rev) d s
def point {n : ℕ} (d : ℕ) (s : History n) (r : Fin n) : Point :=
  (r.val*span n d+offset d s,row d s)

private theorem band {a b w u : ℕ} (lt : a < b) (hu : u < w) : a*w+u < b*w := by
  have h := Nat.mul_le_mul_right w lt
  rw [Nat.succ_mul] at h
  omega

private def carrier (n d : ℕ) : Set Point :=
  {p | ∃ (s : History n), s.length ≤ d ∧ ∃ r ∈ active s, point d s r = p}

private theorem finite_carrier (n d : ℕ) : (carrier n d).Finite := by
  apply (Set.finite_Iic ((n*span n d,span n d) : Point)).subset
  rintro _ ⟨s,_,r,_,rfl⟩
  exact ⟨(band r.isLt (address_lt _ d s)).le,(address_lt _ d s).le⟩

def points (n d : ℕ) := (finite_carrier n d).toFinset

@[simp] theorem in_points {n d : ℕ} {p : Point} : p ∈ points n d ↔
    ∃ (s : History n), s.length ≤ d ∧ ∃ r ∈ active s, point d s r = p :=
  Set.Finite.mem_toFinset _

def trace {α : Type*} [Preorder α] (P : Finset α) (lo hi : α) := P.filter fun p => lo ≤ p ∧ p ≤ hi

@[simp] theorem mem_trace {α : Type*} [Preorder α] {P : Finset α} {lo hi x : α} :
    x ∈ trace P lo hi ↔ x ∈ P ∧ lo ≤ x ∧ x ≤ hi := Finset.mem_filter

/-- All and only the active roots in an ordered interval on stage s. -/
theorem row_box {n d : ℕ} (s : History n) (hs : s.length ≤ d) (a b : Fin n) :
    ∃ lo hi : Point, ∀ (t : History n), t.length ≤ d → ∀ r : Fin n,
      (lo ≤ point d t r ∧ point d t r ≤ hi) ↔ t=s ∧ a ≤ r ∧ r ≤ b := by
  let W := span n d
  refine ⟨(a.val*W,row d s),((b.val+1)*W-1,row d s),?_⟩
  intro t ht r
  have off : offset d t < W := address_lt _ _ _
  change ((a.val*W ≤ r.val*W+offset d t ∧ row d s ≤ row d t) ∧
    (r.val*W+offset d t ≤ (b.val+1)*W-1 ∧ row d t ≤ row d s)) ↔ _
  constructor
  · rintro ⟨⟨x₁,y₁⟩,x₂,y₂⟩
    refine ⟨address_injective (digits n).injective ht hs (le_antisymm y₂ y₁),?_,?_⟩
    · by_contra! h
      exact (band h off).not_ge x₁
    · by_contra! h
      have bnd := Nat.mul_le_mul_right W (show b.val+1 ≤ r.val from h)
      have pos : 0 < (b.val+1)*W := by unfold W span width; positivity
      omega
  · rintro ⟨rfl,al,ub⟩
    have lower := Nat.mul_le_mul_right W (show a.val ≤ r.val from al)
    have upper := band (Nat.lt_succ_of_le (show r.val ≤ b.val from ub)) off
    exact ⟨⟨by omega,le_rfl⟩,Nat.le_sub_one_of_lt upper,le_rfl⟩

/-- A single root band, cut off at the two preorder coordinates of s. -/
theorem path_box {n d : ℕ} (s : History n) (hs : s.length ≤ d) (r : Fin n) :
    ∃ lo hi : Point, ∀ (t : History n), t.length ≤ d → ∀ v : Fin n,
      (lo ≤ point d t v ∧ point d t v ≤ hi) ↔ v=r ∧ t <+: s := by
  let W := span n d
  refine ⟨(r.val*W,0),point d s r,?_⟩
  intro t ht v
  change ((r.val*W ≤ v.val*W+offset d t ∧ 0 ≤ row d t) ∧
      (v.val*W+offset d t ≤ r.val*W+offset d s ∧ row d t ≤ row d s)) ↔ _
  have anc : (row d t ≤ row d s ∧ offset d t ≤ offset d s) ↔ t <+: s :=
    ancestor_iff (digits n).injective ht hs
  constructor
  · rintro ⟨⟨low,_⟩,high,y⟩
    have eq : v = r := by
      apply le_antisymm
      · by_contra! h
        have := band h (show offset d s < W from address_lt ..); omega
      · by_contra! h
        exact (band h (show offset d t < W from address_lt ..)).not_ge low
    subst v
    exact ⟨rfl,anc.mp ⟨y,Nat.le_of_add_le_add_left high⟩⟩
  · rintro ⟨rfl,pre⟩
    obtain ⟨y,x⟩ := anc.mpr pre
    exact ⟨⟨Nat.le_add_right ..,Nat.zero_le _⟩,Nat.add_le_add_left x _,y⟩

theorem point_injective {n d : ℕ} {s t : History n} {r v : Fin n} (hs : s.length ≤ d)
    (ht : t.length ≤ d) (eq : point d s r = point d t v) : s=t ∧ r=v := by
  have y := congrArg Prod.snd eq
  have same := address_injective (digits n).injective hs ht y
  obtain ⟨lo,hi,hbox⟩ := path_box s hs r
  have id := (hbox s hs r).mpr ⟨rfl,List.prefix_refl _⟩
  rw [eq] at id
  exact ⟨same,((hbox t ht v).mp id).1.symm⟩

end
end GenLimit.KleinbergWei.Banach.Stages
