import GenLimit.Paper11_LearningAlgorithmsInTheLimit.MSMMergeOrder
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/-! # Determinizing mergers and observable transition types

A merger is the least equivalence identifying the chosen states and
identifying successors on each common input. Incompatible outputs make its
score zero. Otherwise the score is precisely the number of eliminated
states. If a matching read/write/move label determines its source type,
a valid merger across types can eliminate only one state. -/
namespace GenLimit.LearningAlgorithmsLimit.MSM
open scoped Classical

abbrev Diagram (Q A B : Type*) := Q → A → B → Q → Prop

def Closed (E : Diagram Q A B) (r : Setoid Q) : Prop :=
  ∀ q p a b c u v, r.r q p → E q a b u → E p a c v → r.r u v

def Consistent (E : Diagram Q A B) (r : Setoid Q) : Prop :=
  ∀ q p a b c u v, r.r q p → E q a b u → E p a c v → b = c

def merge (E : Diagram Q A B) (p q : Q) : Setoid Q where
  r x y := ∀ r : Setoid Q, r.r p q → Closed E r → r.r x y
  iseqv := ⟨fun x r _ _ ↦ r.refl x,
    fun h r hp hc ↦ r.symm (h r hp hc),
    fun h₁ h₂ r hp hc ↦ r.trans (h₁ r hp hc) (h₂ r hp hc)⟩

theorem joins (E : Diagram Q A B) (p q : Q) : (merge E p q).r p q := fun _ h _ ↦ h

theorem closed_merge (E : Diagram Q A B) (p q : Q) : Closed E (merge E p q) :=
  fun x y a b c u v h e f r hp hc ↦ hc x y a b c u v (h r hp hc) e f

/-- Determinism of the target and recoverability of the source type from
any observed transition's input and output labels. -/
structure Typed (E : Diagram Q A B) (kind : Q → S) : Prop where
  next : Closed E (Setoid.ker kind)
  consistent : Consistent E (Setoid.ker kind)
  source : ∀ q p a b u v, E q a b u → E p a b v → kind q = kind p

theorem same_valid {E : Diagram Q A B} {kind : Q → S} (ht : Typed E kind) {p q}
    (h : kind p = kind q) : Consistent E (merge E p q) :=
  fun x y a b c u v hr e f ↦ ht.consistent x y a b c u v (hr _ h ht.next) e f

/-- A diagram is deterministic when at most one output and successor can
follow a given state and input. -/
def Deterministic (E : Diagram Q A B) :=
  ∀ q a b c u v, E q a b u → E q a c v → b = c ∧ u = v

private def squash [DecidableEq Q] (p q x : Q) := if x = p then q else x

private theorem squash_eq [DecidableEq Q] {p q x y : Q} (h : squash p q x = squash p q y) :
    x = y ∨ x = p ∧ y = q ∨ x = q ∧ y = p := by
  by_cases hx : x = p <;> by_cases hy : y = p <;> simp_all [squash]

theorem cross_eq [DecidableEq Q] {E : Diagram Q A B} {kind : Q → S}
    (hd : Deterministic E) (ht : Typed E kind) {p q : Q} (hn : kind p ≠ kind q)
    (hv : Consistent E (merge E p q)) : merge E p q = Setoid.ker (squash p q) := by
  have hpair : (Setoid.ker (squash p q)).r p q := by
    change squash p q p = squash p q q
    simp [squash]
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    apply h _ hpair
    intro x y a b c u v hxy ex ey
    rcases squash_eq hxy with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact congrArg _ (hd _ _ _ _ _ _ ex ey).2
    · have he := hv _ _ _ _ _ _ _ (joins E _ _) ex ey
      subst c
      exact (hn (ht.source _ _ _ _ _ _ ex ey)).elim
    · have he := hv _ _ _ _ _ _ _ (joins E _ _) ey ex
      subst c
      exact (hn (ht.source _ _ _ _ _ _ ey ex)).elim
  · intro h
    rcases squash_eq h with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (merge E p q).refl _
    · exact joins E _ _
    · exact (merge E _ _).symm (joins E _ _)

noncomputable def score [Fintype Q] (E : Diagram Q A B) (p q : Q) : ℕ :=
  if Consistent E (merge E p q) then Fintype.card Q - Nat.card (Quotient (merge E p q)) else 0

theorem score_pos [Fintype Q] {E : Diagram Q A B} {kind : Q → S} (ht : Typed E kind)
    {p q : Q} (hne : p ≠ q) (h : kind p = kind q) : 0 < score E p q := by
  classical
  let r := merge E p q
  letI := Fintype.ofFinite (Quotient r)
  have less := Fintype.card_lt_of_surjective_not_injective (Quotient.mk r) Quotient.mk_surjective
    (fun hinj ↦ hne (hinj (Quotient.sound (joins E p q))))
  simpa only [score,if_pos (same_valid ht h),Nat.card_eq_fintype_card,Nat.sub_pos_iff_lt] using less

/-- Distinct types can tie at one. An observed-type tie break is required
if such ties are to be resolved as intended. -/
theorem cross_score_le_one [Fintype Q] {E : Diagram Q A B} {kind : Q → S}
    (hd : Deterministic E) (ht : Typed E kind) {p q : Q} (hn : kind p ≠ kind q) :
    score E p q ≤ 1 := by
  classical
  by_cases hv : Consistent E (merge E p q)
  · have hne : p ≠ q := fun e ↦ hn (congrArg kind e)
    rw [score,if_pos hv,cross_eq hd ht hn hv]
    let f := squash p q
    have ran : Set.range f = {x | x ≠ p} := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩
        by_cases hy : y = p <;> simp [f,squash,hy,hne.symm]
      · intro hx
        exact ⟨x,by simp [f,squash,show x ≠ p from hx]⟩
    have he := Nat.card_congr (Setoid.quotientKerEquivRange f)
    rw [ran] at he
    rw [he,Nat.card_eq_fintype_card]
    change Fintype.card Q - Fintype.card {x : Q // ¬ x = p} ≤ 1
    rw [Fintype.card_subtype_compl (fun x : Q ↦ x = p)]
    have one : Fintype.card {x : Q // x = p} = 1 := Fintype.card_unique
    rw [one]
    omega
  · simp [score,hv]

end GenLimit.LearningAlgorithmsLimit.MSM
