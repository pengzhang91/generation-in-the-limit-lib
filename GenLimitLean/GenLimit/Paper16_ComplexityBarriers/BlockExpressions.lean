import GenLimit.Paper16_ComplexityBarriers.BinaryBlocks
import GenLimit.Paper16_ComplexityBarriers.RegexAutomaton

/-! # Regular expressions for fixed-width address comparisons -/
namespace GenLimit.ComplexityBarriers.Blocks
open List RegularExpression
open scoped Classical
noncomputable section

abbrev RE := RegularExpression Bool

private def bit : RE := .plus (.char false) (.char true)

private def anyBits : ℕ → RE
  | 0 => 1
  | k+1 => bit * anyBits k

private def exactBits : List Bool → RE
  | [] => 1
  | a::u => .char a * exactBits u

/-- The first unequal bit is b. Later bits are unrestricted. -/
private def orderedBits (b : Bool) : List Bool → RE
  | [] => 0
  | a::u =>
    let same := .char a * orderedBits b u
    if a=b then same else same + .char b * anyBits u.length

private theorem mem_bit (w : List Bool) : w ∈ bit.matches' ↔ ∃ a : Bool, w=[a] := by
  change (w=[false] ∨ w=[true]) ↔ _
  constructor
  · rintro (rfl|rfl) <;> exact ⟨_,rfl⟩
  · rintro ⟨a,rfl⟩; cases a <;> simp

private theorem char_mul (a : Bool) (r : RE) (w : List Bool) :
    w ∈ ((.char a : RE)*r).matches' ↔ ∃ u, w = a::u ∧ u ∈ r.matches' := by
  rw [RegularExpression.matches'_mul,Language.mem_mul]
  constructor
  · rintro ⟨_,rfl,u,hu,rfl⟩; exact ⟨_,rfl,hu⟩
  · rintro ⟨u,rfl,hu⟩; exact ⟨[a],rfl,u,hu,rfl⟩

private theorem mem_anyBits (k : ℕ) (w : List Bool) :
    w ∈ (anyBits k).matches' ↔ w.length=k := by
  induction k generalizing w with
  | zero => change w=[] ↔ _; simp
  | succ k ih =>
    rw [anyBits,RegularExpression.matches'_mul,Language.mem_mul]
    constructor
    · rintro ⟨v,hv,u,hu,rfl⟩
      obtain ⟨a,rfl⟩ := (mem_bit v).mp hv
      simp [(ih _).mp hu]
    · intro hl
      cases w with
      | nil => simp at hl
      | cons a w => exact ⟨[a],(mem_bit _).mpr ⟨a,rfl⟩,w,(ih _).mpr (by simpa using hl),rfl⟩

private theorem mem_exactBits (u w : List Bool) : w ∈ (exactBits u).matches' ↔ w=u := by
  induction u generalizing w with
  | nil => rfl
  | cons a u ih => rw [exactBits,char_mul]; simp [ih]

private theorem mem_orderedBits (b : Bool) (d w : List Bool) :
    w ∈ (orderedBits b d).matches' ↔ w.length=d.length ∧ (if b then d<w else w<d) := by
  induction d generalizing w with
  | nil => cases w <;> cases b <;> simp [orderedBits]
  | cons a d ih =>
    cases w with
    | nil => cases a <;> cases b <;>
        simp only [orderedBits,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,RegularExpression.matches'_add,Language.mem_add,char_mul] <;> simp
    | cons x xs =>
      cases a <;> cases x <;> cases b <;>
        simp only [orderedBits,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,RegularExpression.matches'_add,Language.mem_add,char_mul,mem_anyBits,ih] <;>
        simp [List.cons_lt_cons_iff,and_comm]

def tokenExpression (d : Address ℓ) : Ordering → RE
  | .lt => orderedBits false d.val * bit
  | .eq => exactBits d.val * bit
  | .gt => orderedBits true d.val * bit

def relation (d e : Address ℓ) : Ordering → Prop
  | .lt => e < d
  | .eq => e = d
  | .gt => d < e

def atom (d : Address ℓ) (o : Ordering) : _root_.Language (Token ℓ) :=
  {w | ∃ t : Token ℓ, w = [t] ∧ relation d t.1 o}

def packed (L : _root_.Language (Token ℓ)) : _root_.Language Bool := encode '' (L : Set (List (Token ℓ)))

theorem token_spec (d : Address ℓ) (o) : (tokenExpression d o).matches' = packed (atom d o) := by
  let r := match o with
    | .lt => orderedBits false d.val
    | .eq => exactBits d.val
    | .gt => orderedBits true d.val
  have hr (v : List Bool) : v ∈ r.matches' ↔ ∃ e : Address ℓ, v=e.val ∧ relation d e o := by
    cases o with
    | lt =>
      change v ∈ (orderedBits false d.val).matches' ↔ _
      rw [mem_orderedBits]
      exact ⟨fun ⟨hl,h⟩ ↦ ⟨⟨v,hl.trans d.property⟩,rfl,h⟩,fun ⟨e,hv,h⟩ ↦ hv ▸ ⟨e.property.trans d.property.symm,h⟩⟩
    | gt =>
      change v ∈ (orderedBits true d.val).matches' ↔ _
      rw [mem_orderedBits]
      exact ⟨fun ⟨hl,h⟩ ↦ ⟨⟨v,hl.trans d.property⟩,rfl,h⟩,fun ⟨e,hv,h⟩ ↦ hv ▸ ⟨e.property.trans d.property.symm,h⟩⟩
    | eq =>
      change v ∈ (exactBits d.val).matches' ↔ _
      rw [mem_exactBits]
      exact ⟨fun hv ↦ ⟨d,hv,rfl⟩,fun ⟨e,hv,he⟩ ↦ hv.trans (congrArg Subtype.val he)⟩
  have ht : tokenExpression d o = r*bit := by cases o <;> rfl
  ext w
  rw [ht,RegularExpression.matches'_mul,Language.mem_mul]
  constructor
  · rintro ⟨v,hv,u,hu,rfl⟩
    obtain ⟨e,rfl,he⟩ := (hr v).mp hv
    obtain ⟨b,rfl⟩ := (mem_bit u).mp hu
    exact ⟨[(e,b)],⟨(e,b),rfl,he⟩,by simp [encode,bits]⟩
  · rintro ⟨_,⟨t,rfl,ht⟩,rfl⟩
    exact ⟨t.1.val,(hr _).mpr ⟨t.1,rfl,ht⟩,[t.2],(mem_bit _).mpr ⟨_,rfl⟩,by simp [encode,bits]⟩

private theorem any_size (k : ℕ) : Automata.regexSize (anyBits k) = 4*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => change 3+Automata.regexSize (anyBits k)+1 = _; rw [ih]; omega

private theorem exact_size (d : List Bool) : Automata.regexSize (exactBits d) = 2*d.length+1 := by
  induction d with
  | nil => rfl
  | cons a d ih => change 1+Automata.regexSize (exactBits d)+1 = 2*(d.length+1)+1; rw [ih]; omega

private theorem ordered_size (b : Bool) (d : List Bool) :
    Automata.regexSize (orderedBits b d) ≤ 4*(d.length+1)^2 := by
  induction d with
  | nil => exact (by decide : 1 ≤ 4*(0+1)^2)
  | cons a d ih =>
    rw [orderedBits]
    split
    · change 1+Automata.regexSize (orderedBits b d)+1 ≤ 4*(d.length+1+1)^2
      ring_nf at ih ⊢; omega
    · change 1+Automata.regexSize (orderedBits b d)+1+(1+Automata.regexSize (anyBits d.length)+1)+1 ≤ 4*(d.length+1+1)^2
      rw [any_size]; ring_nf at ih ⊢; omega

theorem token_size (d : Address ℓ) (o) : Automata.regexSize (tokenExpression d o) ≤ 8*(ℓ+1)^2 := by
  have hh (b) := ordered_size b d.val
  have he := exact_size d.val
  simp only [d.property] at hh he
  cases o <;> change _ + 3 + 1 ≤ _ <;> first | nlinarith [hh false] | nlinarith [hh true]

end
end GenLimit.ComplexityBarriers.Blocks
