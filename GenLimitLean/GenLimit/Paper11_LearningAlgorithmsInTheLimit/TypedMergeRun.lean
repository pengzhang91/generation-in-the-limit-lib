import GenLimit.Paper11_LearningAlgorithmsInTheLimit.DeterminizingMerge

/-! # Maximum-similarity merging with observable type ties

A finite diagram whose edge labels identify their source admits a run of
genuine highest-score mergers that reaches one state per observed type.
Quotienting preserves the entire set of observed, type-labelled transitions.
-/
namespace GenLimit.LearningAlgorithmsLimit.MSM

universe u v w z

/-- Edges observed after identifying states. -/
def quotientEdges {Q A B : Type*} (E : Diagram Q A B) (r : Setoid Q) :
    Diagram (Quotient r) A B :=
  fun x a b y ↦ ∃ p q, Quotient.mk r p = x ∧ Quotient.mk r q = y ∧ E p a b q

/-- Every valid determinizing merger yields a deterministic quotient. -/
theorem quotient_deterministic {Q A B : Type*} {E : Diagram Q A B} {r : Setoid Q}
    (hc : Closed E r) (hv : Consistent E r) : Deterministic (quotientEdges E r) := by
  rintro _ a b c _ _ ⟨p, u, rfl, rfl, e⟩ ⟨q, v, heq, rfl, f⟩
  have h := Quotient.exact heq.symm
  exact ⟨hv _ _ _ _ _ _ _ h e f, Quotient.sound (hc _ _ _ _ _ _ _ h e f)⟩

def quotientKind {Q S : Type*} (kind : Q → S) (r : Setoid Q)
    (hr : r ≤ Setoid.ker kind) : Quotient r → S :=
  Quotient.lift kind fun _ _ h ↦ hr h

theorem quotient_typed {Q A B S : Type*} {E : Diagram Q A B} {kind : Q → S}
    (ht : Typed E kind) {r : Setoid Q} (hr : r ≤ Setoid.ker kind) :
    Typed (quotientEdges E r) (quotientKind kind r hr) := by
  constructor
  · rintro _ _ a b c _ _ h ⟨p, u, rfl, rfl, e⟩ ⟨q, v, rfl, rfl, f⟩
    exact ht.next _ _ _ _ _ _ _ h e f
  · rintro _ _ a b c _ _ h ⟨p, u, rfl, rfl, e⟩ ⟨q, v, rfl, rfl, f⟩
    exact ht.consistent _ _ _ _ _ _ _ h e f
  · rintro _ _ a b _ _ ⟨p, u, rfl, rfl, e⟩ ⟨q, v, rfl, rfl, f⟩
    exact ht.source _ _ _ _ _ _ e f

/-- Finite labelled diagrams through which a state-merging run passes. -/
structure LabelledDiagram (A : Type v) (B : Type w) (S : Type z) where
  State : Type u
  finiteState : Fintype State
  edge : Diagram State A B
  kind : State → S

attribute [instance] LabelledDiagram.finiteState

namespace LabelledDiagram

variable {A : Type v} {B : Type w} {S : Type z}

def typeEdges (D : LabelledDiagram.{u} A B S) : Diagram S A B :=
  fun s a b t ↦ ∃ p q, D.kind p = s ∧ D.kind q = t ∧ D.edge p a b q

noncomputable def quotient (D : LabelledDiagram.{u} A B S) (r : Setoid D.State)
    (hr : r ≤ Setoid.ker D.kind) : LabelledDiagram.{u} A B S :=
  ⟨Quotient r, Fintype.ofFinite _, quotientEdges D.edge r, quotientKind D.kind r hr⟩

theorem quotient_typeEdges (D : LabelledDiagram.{u} A B S) (r : Setoid D.State)
    (hr : r ≤ Setoid.ker D.kind) : (D.quotient r hr).typeEdges = D.typeEdges := by
  funext s a b t
  apply propext
  constructor
  · rintro ⟨_, _, hs, ht, p, q, rfl, rfl, he⟩
    exact ⟨p, q, hs, ht, he⟩
  · rintro ⟨p, q, rfl, rfl, he⟩
    exact ⟨Quotient.mk r p, Quotient.mk r q, rfl, rfl, p, q, rfl, rfl, he⟩

/-- A source-permitted positive maximum. Equal observed types are preferred
when there is a tie. -/
def SoundStep (D F : LabelledDiagram.{u} A B S) : Prop :=
  ∃ p q : D.State, p ≠ q ∧ D.kind p = D.kind q ∧ 0 < score D.edge p q ∧
    (∀ x y, x ≠ y → score D.edge x y ≤ score D.edge p q) ∧
    ∃ hr : merge D.edge p q ≤ Setoid.ker D.kind, F = D.quotient _ hr

theorem exists_best_same (D : LabelledDiagram.{u} A B S) (hd : Deterministic D.edge)
    (ht : Typed D.edge D.kind) (hn : ¬ Function.Injective D.kind) :
    ∃ p q, p ≠ q ∧ D.kind p = D.kind q ∧ 0 < score D.edge p q ∧
      ∀ x y, x ≠ y → score D.edge x y ≤ score D.edge p q := by
  classical
  have ⟨p, q, h, hpq⟩ : ∃ p q, D.kind p = D.kind q ∧ p ≠ q := by
    simpa only [Function.Injective, not_forall, exists_prop] using hn
  let pairs := Finset.univ.filter (fun z : D.State × D.State ↦ z.1 ≠ z.2 ∧ D.kind z.1 = D.kind z.2)
  have mem (x y : D.State) : (x,y) ∈ pairs ↔ x ≠ y ∧ D.kind x = D.kind y := by simp [pairs]
  obtain ⟨⟨s,t⟩, hs, hmax⟩ := pairs.exists_max_image
    (fun z ↦ score D.edge z.1 z.2) ⟨(p,q),(mem p q).2 ⟨hpq,h⟩⟩
  have hs' := (mem s t).1 hs
  have hpos := score_pos ht hs'.1 hs'.2
  refine ⟨s, t, hs'.1, hs'.2, hpos, fun x y hxy ↦ ?_⟩
  by_cases hk : D.kind x = D.kind y
  · exact hmax (x,y) ((mem x y).2 ⟨hxy,hk⟩)
  · exact (cross_score_le_one hd ht hk).trans hpos

/-- Starting from any typed deterministic diagram, actual maximum-score
mergers reach one state per type and preserve all type-labelled edges. -/
theorem reaches_types (D : LabelledDiagram.{u} A B S) (hd : Deterministic D.edge)
    (ht : Typed D.edge D.kind) :
    ∃ F, Relation.ReflTransGen SoundStep D F ∧ Function.Injective F.kind ∧
      F.typeEdges = D.typeEdges := by
  classical
  by_cases hi : Function.Injective D.kind
  · exact ⟨D, .refl, hi, rfl⟩
  obtain ⟨p,q,hne,hk,hpos,hm⟩ := D.exists_best_same hd ht hi
  let r := merge D.edge p q
  have hr : r ≤ Setoid.ker D.kind := fun _ _ h ↦ h _ hk ht.next
  let C := D.quotient r hr
  have hd' : Deterministic C.edge := quotient_deterministic (closed_merge D.edge p q) (same_valid ht hk)
  have ht' : Typed C.edge C.kind := quotient_typed ht hr
  have dec : Fintype.card C.State < Fintype.card D.State :=
    Fintype.card_lt_of_surjective_not_injective (Quotient.mk r) Quotient.mk_surjective
      (fun h ↦ hne (h (Quotient.sound (joins D.edge p q))))
  obtain ⟨F,hpath,hi',hedge⟩ := reaches_types C hd' ht'
  exact ⟨F, hpath.head ⟨p,q,hne,hk,hpos,hm,hr,rfl⟩, hi', hedge.trans (D.quotient_typeEdges r hr)⟩
termination_by Fintype.card D.State

end LabelledDiagram
end GenLimit.LearningAlgorithmsLimit.MSM
