import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Size of a binary derivation with protected transitions

On a branch on which the number of marked nodes stays the same, a reduced
derivation cannot repeat a colour. Unmarked side trees then have bounded
height. Branches that split the marks pay for both new branches. This gives
a bound linear in the number of marks, with a constant depending only on
the finite palette.
-/
namespace GenLimit.ComputationalTrace.PDA

inductive Tree (α : Type) where
  | nil
  | node (a : α) (l r : Tree α)

namespace Tree
variable {α β : Type}

def items : Tree α → List α
  | .nil => []
  | .node a l r => a :: l.items ++ r.items

def size (t : Tree α) := t.items.length

def marks (mark : α → Bool) (t : Tree α) := (t.items.filter mark).length

@[simp] theorem size_nil : (nil : Tree α).size = 0 := rfl
@[simp] theorem size_node (a : α) (l r : Tree α) :
    (node a l r).size = l.size + r.size + 1 := by simp [size,items]

@[simp] theorem marks_nil (mark : α → Bool) : (nil : Tree α).marks mark = 0 := rfl
theorem marks_node (mark : α → Bool) (a : α) (l r : Tree α) :
    (node a l r).marks mark = l.marks mark + r.marks mark + (if mark a then 1 else 0) := by
  cases ha : mark a <;> simp [marks,items,ha]

inductive Sub : Tree α → Tree α → Prop
  | refl (t) : Sub t t
  | left {t a l r} (h : Sub t l) : Sub t (.node a l r)
  | right {t a l r} (h : Sub t r) : Sub t (.node a l r)

theorem Sub.trans {t u v : Tree α} (htu : Sub t u) (huv : Sub u v) : Sub t v := by
  induction huv with
  | refl => exact htu
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem Sub.size_le {t u : Tree α} (h : Sub t u) : t.size ≤ u.size := by
  induction h <;> simp_all <;> omega

/-- Every descendant in the same band of marks must use a fresh colour. -/
def Reduced (colour : α → β) (mark : α → Bool) (t : Tree α) : Prop :=
  ∀ a l r, Sub (.node a l r) t → ∀ b x y, (Sub (.node b x y) l ∨ Sub (.node b x y) r) →
    (.node b x y : Tree α).marks mark = (.node a l r : Tree α).marks mark → colour b ≠ colour a

def Palette [DecidableEq β] (colour : α → β) (mark : α → Bool)
    (t : Tree α) (P : Finset β) : Prop :=
  ∀ a l r, Sub (.node a l r) t → (.node a l r : Tree α).marks mark = t.marks mark → colour a ∈ P

private def cost (b : ℕ) := (2*b+2)*2^b

private theorem combine {m l r a x y p b : ℕ} (hlr : l+r ≤ m)
    (hzero : m=0 → x < 2^p ∧ y < 2^p)
    (lx : l=0 → x < 2^b) (ry : r=0 → y < 2^b)
    (ls : 0<l → x + cost b ≤ (2*l)*cost b + (if l=m then p else b)*2^b)
    (rs : 0<r → y + cost b ≤ (2*r)*cost b + (if r=m then p else b)*2^b)
    (ha : a=x+y+1) :
    (m=0 → a < 2^(p+1)) ∧
    (0<m → a + cost b ≤ (2*m)*cost b + (p+1)*2^b) := by
  have hc : 2*(b*2^b) + 2*2^b = cost b := by unfold cost; ring
  have hpow : 0 < 2^b := Nat.two_pow_pos _
  constructor
  · intro hm
    obtain ⟨hx,hy⟩ := hzero hm
    rw [pow_succ]; omega
  · intro hm
    by_cases hL : l=m
    · subst l
      have hr : r=0 := by omega
      have h := ls hm
      simp only [if_true] at h
      have := ry hr
      rw [Nat.add_mul]; omega
    by_cases hR : r=m
    · subst r
      have hl : l=0 := by omega
      have h := rs hm
      simp only [if_true] at h
      have := lx hl
      rw [Nat.add_mul]; omega
    simp only [hL,hR,if_false] at ls rs
    by_cases hl : l=0 <;> by_cases hr : r=0
    · have := lx hl
      have := ry hr
      have hbase := Nat.mul_le_mul_right (cost b) (show 2 ≤ 2*m by omega)
      omega
    · have := lx hl
      have := rs (by omega)
      have hbase := Nat.mul_le_mul_right (cost b) (show 2*r+2 ≤ 2*m by omega)
      rw [Nat.add_mul] at hbase
      omega
    · have := ry hr
      have := ls (by omega)
      have hbase := Nat.mul_le_mul_right (cost b) (show 2*l+2 ≤ 2*m by omega)
      rw [Nat.add_mul] at hbase
      omega
    · have := ls (by omega)
      have := rs (by omega)
      have hbase := Nat.mul_le_mul_right (cost b) (show 2*l+2*r ≤ 2*m by omega)
      rw [Nat.add_mul] at hbase
      omega

private theorem size_potential [DecidableEq β] (colour : α → β) (mark : α → Bool)
    (B : Finset β) (t : Tree α) (all : ∀ a l r, Sub (.node a l r) t → colour a ∈ B)
    (red : Reduced colour mark t) (P : Finset β) (hP : P ⊆ B) (hp : Palette colour mark t P) :
    (t.marks mark = 0 → t.size < 2^P.card) ∧
    (0 < t.marks mark → t.size + cost B.card ≤ 2*t.marks mark*cost B.card + P.card*2^B.card) := by
  induction t generalizing P with
  | nil => simp
  | node a l r il ir =>
    let t := node a l r
    have hac := hp a l r (.refl _) rfl
    let E := P.erase (colour a)
    have hE : E.card + 1 = P.card := Finset.card_erase_add_one hac
    have child (u : Tree α) (side : u=l ∨ u=r) :
        let U := if u.marks mark = t.marks mark then E else B
        (∀ b x y, Sub (.node b x y) u → colour b ∈ B) ∧ Reduced colour mark u ∧
          U ⊆ B ∧ Palette colour mark u U := by
      have sub : Sub u t := side.elim (fun h => h ▸ Sub.left (.refl _)) (fun h => h ▸ Sub.right (.refl _))
      refine ⟨fun b x y h => all b x y (h.trans sub),fun b x y h => red b x y (h.trans sub),?_⟩
      dsimp only
      split
      next eq =>
        refine ⟨(Finset.erase_subset ..).trans hP, fun b x y h hmark => ?_⟩
        exact Finset.mem_erase.mpr ⟨red a l r (.refl _) b x y
          (side.elim (fun e => Or.inl (e ▸ h)) (fun e => Or.inr (e ▸ h))) (hmark.trans eq),
          hp b x y (h.trans sub) (hmark.trans eq)⟩
      next => exact ⟨Finset.Subset.refl _,fun b x y h _ => all b x y (h.trans sub)⟩
    have ⟨xl,xr,xs,xp⟩ := child l (Or.inl rfl)
    have ⟨yl,yr,ys,yp⟩ := child r (Or.inr rfl)
    have h₁ := il xl xr _ xs xp
    have h₂ := ir yl yr _ ys yp
    have hsum : l.marks mark + r.marks mark ≤ t.marks mark := by simp [t,marks_node]
    have hEB : E.card ≤ B.card := Finset.card_le_card ((Finset.erase_subset ..).trans hP)
    have power : 2^E.card ≤ 2^B.card := Nat.pow_le_pow_right (by decide) hEB
    have hL (eq : l.marks mark = 0) : l.size < 2^B.card := by
      have h := h₁.1 eq
      split at h <;> omega
    have hR (eq : r.marks mark = 0) : r.size < 2^B.card := by
      have h := h₂.1 eq
      split at h <;> omega
    rw [← hE]
    apply combine hsum _ hL hR _ _ (size_node ..)
    · intro h
      change t.marks mark = 0 at h
      have l0 : l.marks mark = 0 := by omega
      have r0 : r.marks mark = 0 := by omega
      exact ⟨by simpa [l0.trans h.symm] using h₁.1 l0,by simpa [r0.trans h.symm] using h₂.1 r0⟩
    · intro hl
      split <;> rename_i eq <;> simpa [eq] using h₁.2 hl
    · intro hr
      split <;> rename_i eq <;> simpa [eq] using h₂.2 hr

def treeFactor (b : ℕ) := 3 * cost b

theorem size_le_marks [DecidableEq β] (colour : α → β) (mark : α → Bool)
    (B : Finset β) (t : Tree α) (all : ∀ a l r, Sub (.node a l r) t → colour a ∈ B)
    (red : Reduced colour mark t) :
    t.size ≤ treeFactor B.card * (t.marks mark + 1) := by
  have h := size_potential colour mark B t all red B (Finset.Subset.refl _) (fun a l r ha _ => all a l r ha)
  have h₁ : B.card * 2^B.card ≤ cost B.card := by
    exact Nat.mul_le_mul_right _ (by omega)
  have h₂ : 2^B.card ≤ cost B.card := by
    unfold cost; exact Nat.le_mul_of_pos_left _ (by omega)
  by_cases eq : t.marks mark = 0
  · have := h.1 eq
    simp only [eq,Nat.zero_add,Nat.mul_one,treeFactor]; omega
  · have := h.2 (by omega)
    unfold treeFactor
    nlinarith [Nat.zero_le (cost B.card * t.marks mark)]

end Tree
end GenLimit.ComputationalTrace.PDA
