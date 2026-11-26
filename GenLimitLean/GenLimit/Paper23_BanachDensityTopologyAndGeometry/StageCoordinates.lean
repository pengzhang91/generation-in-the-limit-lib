import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.Infix
import Mathlib.Tactic

/-! Integer coordinates for the two-color forest construction behind P23
Theorem 5.2. Each finite history has two preorder numbers. The second
reverses the order of siblings. Their common order records exactly the
ancestor relation. The first coordinate alone distinguishes stage lines.

The construction follows the horizontal-stage realization of
*Coloring Questions on Axis-Parallel Rectangles and Arithmetic Progressions*,
Sections 2–3 (arXiv:2602.18235), specialized to two colors. -/
namespace GenLimit.KleinbergWei.Banach.Stages
open scoped Classical
noncomputable section

def width (b d : ℕ) := (b+1)^d

def address {α : Type*} {b : ℕ} (digit : α → Fin b) : ℕ → List α → ℕ
  | 0, _ => 0
  | _+1, [] => 0
  | d+1, a::s => 1+(digit a).val*width b d+address digit d s

theorem address_lt {α : Type*} {b : ℕ} (digit : α → Fin b) (d : ℕ) (s : List α) :
    address digit d s < width b d := by
  induction d generalizing s with
  | zero => simp [address,width]
  | succ d ih =>
    cases s with
    | nil => simp [address,width]
    | cons a s =>
      have h := ih s
      have grow := Nat.mul_le_mul_right (width b d) (digit a).isLt
      have pos : 0 < width b d := by unfold width; positivity
      simp only [address,width,pow_succ] at *
      nlinarith

private theorem head_lt {α : Type*} {b : ℕ} (digit : α → Fin b) {a a' : α}
    (h : digit a < digit a') (d : ℕ) (s t : List α) :
    address digit (d+1) (a::s) < address digit (d+1) (a'::t) := by
  have grow := Nat.mul_le_mul_right (width b d) (show (digit a).val+1 ≤ (digit a').val from h)
  have remain := address_lt digit d s
  simp only [address,Nat.add_mul,Nat.one_mul] at *
  omega

theorem address_injective {α : Type*} {b : ℕ} {digit : α → Fin b} (inj : Function.Injective digit)
    {d : ℕ} {s t : List α} (hs : s.length ≤ d) (ht : t.length ≤ d)
    (eq : address digit d s = address digit d t) : s = t := by
  induction d generalizing s t with
  | zero => simp_all
  | succ d ih =>
    cases s with
    | nil => cases t with
      | nil => rfl
      | cons a t => simp only [address] at eq; omega
    | cons a s => cases t with
      | nil => simp only [address] at eq; omega
      | cons u t =>
        have same : a = u := by
          apply inj; apply le_antisymm
          · by_contra! h; exact (head_lt digit h d t s).ne eq.symm
          · by_contra! h; exact (head_lt digit h d s t).ne eq
        subst u
        simp only [address,Nat.add_left_cancel_iff] at eq
        exact congrArg (a::·) (ih (by simpa using hs) (by simpa using ht) eq)

theorem ancestor_iff {α : Type*} {b : ℕ} {digit : α → Fin b} (inj : Function.Injective digit)
    {d : ℕ} {s t : List α} (hs : s.length ≤ d) (ht : t.length ≤ d) :
    address digit d s ≤ address digit d t ∧
      address (fun x => (digit x).rev) d s ≤ address (fun x => (digit x).rev) d t ↔ s <+: t := by
  induction d generalizing s t with
  | zero => simp_all
  | succ d ih =>
    cases s with
    | nil => cases t <;> simp [address]
    | cons a s => cases t with
      | nil => simp [address]
      | cons u t =>
        by_cases eq : a=u
        · subst u; simp only [address,Nat.add_le_add_iff_left,List.cons_prefix_cons,true_and]
          exact ih (by simpa using hs) (by simpa using ht)
        · have ne : digit a ≠ digit u := fun h => eq (inj h)
          constructor
          · intro ⟨p,q⟩
            rcases lt_or_gt_of_ne ne with h | h
            · exact False.elim ((head_lt (fun x => (digit x).rev) (Fin.rev_lt_rev.mpr h) d t s).not_ge q)
            · exact False.elim ((head_lt digit h d t s).not_ge p)
          · intro prefixEq
            exact False.elim (eq (List.cons_prefix_cons.mp prefixEq).1)

end
end GenLimit.KleinbergWei.Banach.Stages
