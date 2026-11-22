import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TypedMergeRun

/-! # Terminal maximum-similarity quotients

A run may rename states between iterations. Each positive maximum reduces
the state count, and its quotient map carries every observed transition to
a transition with the same input and output. -/
namespace GenLimit.LearningAlgorithmsLimit.MSM.LabelledDiagram
open GenLimit.LearningAlgorithmsLimit.MSM

universe u v w z
variable {A : Type v} {B : Type w} {S : Type z}

def Maximum (D : LabelledDiagram.{u} A B S) (p q : D.State) : Prop :=
  p ≠ q ∧ 0 < score D.edge p q ∧ ∀ x y, x ≠ y → score D.edge x y ≤ score D.edge p q

def Terminal (D : LabelledDiagram.{u} A B S) := ∀ p q, p ≠ q → score D.edge p q = 0

def Preserves (D F : LabelledDiagram.{u} A B S) (h : D.State → F.State) : Prop :=
  ∀ x a b y, D.edge x a b y → F.edge (h x) a b (h y)

/-- A legal maximum-score merger up to a change of state names. -/
def Legal (D F : LabelledDiagram.{u} A B S) : Prop :=
  ∃ p q, Maximum D p q ∧ ∃ e : Quotient (merge D.edge p q) ≃ F.State,
    ∀ x a b y, quotientEdges D.edge (merge D.edge p q) x a b y ↔ F.edge (e x) a b (e y)

/-- A finite rooted run records the actual quotient map, including changes of
state names. A root travels through the composed map of the run. -/
inductive Run : (D F : LabelledDiagram.{u} A B S) → (D.State → F.State) → Prop
  | refl (D) : Run D D id
  | rename {D F} (e : D.State ≃ F.State)
      (edges : ∀ x a b y, D.edge x a b y ↔ F.edge (e x) a b (e y)) : Run D F e
  | merger {D F} (p q : D.State) (hm : Maximum D p q)
      (e : Quotient (merge D.edge p q) ≃ F.State)
      (edges : ∀ x a b y, quotientEdges D.edge (merge D.edge p q) x a b y ↔ F.edge (e x) a b (e y)) :
      Run D F (e ∘ Quotient.mk _)
  | trans {D F G f g} (one : Run D F f) (two : Run F G g) : Run D G (g ∘ f)

theorem Run.preserves {D F : LabelledDiagram.{u} A B S} {f} (h : Run D F f) : Preserves D F f := by
  induction h with
  | refl => exact fun _ _ _ _ he ↦ he
  | rename _ he => exact fun x a b y hx ↦ (he x a b y).mp hx
  | merger _ _ _ _ he =>
    exact fun x a b y hx ↦ (he _ a b _).mp ⟨x,y,rfl,rfl,hx⟩
  | trans _ _ hf hg => exact fun x a b y he ↦ hg _ a b _ (hf x a b y he)

theorem sound_run_map {D F : LabelledDiagram.{u} A B S} (h : Relation.ReflTransGen SoundStep D F) :
    ∃ f, Run D F f ∧ ∀ x, F.kind (f x) = D.kind x := by
  induction h with
  | refl => exact ⟨id,.refl _,fun _ ↦ rfl⟩
  | @tail M F _ step ih =>
    obtain ⟨f,hf,ht⟩ := ih
    obtain ⟨p,q,hn,hk,hpos,hm,hr,rfl⟩ := step
    have one : Run M (M.quotient _ hr) (Quotient.mk (merge M.edge p q)) :=
      Run.merger (D := M) (F := M.quotient _ hr) p q ⟨hn,hpos,hm⟩
        (Equiv.refl (Quotient (merge M.edge p q))) (fun _ _ _ _ ↦ Iff.rfl)
    exact ⟨_,hf.trans one,ht⟩

theorem SoundStep.legal {D F : LabelledDiagram.{u} A B S} (h : SoundStep D F) : Legal D F := by
  obtain ⟨p,q,hne,_,hp,hm,hr,rfl⟩ := h
  exact ⟨p,q,⟨hne,hp,hm⟩,Equiv.refl _,fun _ _ _ _ ↦ Iff.rfl⟩

theorem SoundStep.range_eq {D F : LabelledDiagram.{u} A B S} (h : SoundStep D F) :
    Set.range F.kind = Set.range D.kind := by
  obtain ⟨p,q,_,_,_,_,hr,rfl⟩ := h
  ext s
  constructor
  · rintro ⟨v,rfl⟩
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective v
    exact ⟨x,rfl⟩
  · rintro ⟨v,rfl⟩
    exact ⟨Quotient.mk _ v,rfl⟩

theorem range_eq_of_sound_run {D F : LabelledDiagram.{u} A B S}
    (h : Relation.ReflTransGen SoundStep D F) : Set.range F.kind = Set.range D.kind := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact h.range_eq.trans ih

private theorem positive_valid {D : LabelledDiagram.{u} A B S} {p q : D.State}
    (h : 0 < score D.edge p q) : Consistent D.edge (merge D.edge p q) := by
  classical
  by_contra hn
  simp [score,hn] at h

/-- From every finite deterministic diagram, MSM reaches a terminal quotient
by genuine maximum-score mergers. The displayed map preserves every
observed labelled edge. -/
theorem terminal_quotient (D : LabelledDiagram.{u} A B S) (fallback : S) (hd : Deterministic D.edge) :
    ∃ F, Relation.ReflTransGen Legal D F ∧ Terminal F ∧ Deterministic F.edge ∧
      ∃ h : D.State → F.State, Run D F h := by
  classical
  by_cases hterm : Terminal D
  · exact ⟨D,.refl,hterm,hd,id,.refl _⟩
  obtain ⟨p,q,hne,hpos⟩ : ∃ p q, p ≠ q ∧ 0 < score D.edge p q := by
    simpa only [Terminal,not_forall,exists_prop,Nat.pos_iff_ne_zero] using hterm
  let pairs := Finset.univ.filter (fun v : D.State × D.State ↦ v.1 ≠ v.2)
  have mem (x y : D.State) : (x,y) ∈ pairs ↔ x ≠ y := by simp [pairs]
  obtain ⟨⟨x,y⟩,hx,hm⟩ := pairs.exists_max_image (fun v ↦ score D.edge v.1 v.2)
    ⟨(p,q),(mem p q).mpr hne⟩
  have hxy := (mem x y).mp hx
  have hmax : Maximum D x y := ⟨hxy,hpos.trans_le (hm _ ((mem p q).mpr hne)),
    fun a b hab ↦ hm (a,b) ((mem a b).mpr hab)⟩
  let r := merge D.edge x y
  let C : LabelledDiagram.{u} A B S := ⟨Quotient r,Fintype.ofFinite _,quotientEdges D.edge r,fun _ ↦ fallback⟩
  have hstep : Legal D C := ⟨x,y,hmax,Equiv.refl _,fun _ _ _ _ ↦ Iff.rfl⟩
  have hc : Deterministic C.edge := quotient_deterministic (closed_merge D.edge x y) (positive_valid hmax.2.1)
  have dec : Fintype.card C.State < Fintype.card D.State :=
    Fintype.card_lt_of_surjective_not_injective (Quotient.mk r) Quotient.mk_surjective
      (fun h ↦ hxy (h (Quotient.sound (joins D.edge x y))))
  obtain ⟨F,hpath,ht,hdet,hmap,hh⟩ := terminal_quotient C fallback hc
  exact ⟨F,hpath.head hstep,ht,hdet,_,(.merger x y hmax (Equiv.refl _) (fun _ _ _ _ ↦ Iff.rfl) : Run D C _).trans hh⟩
termination_by Fintype.card D.State
decreasing_by
  simp only [← Nat.card_eq_fintype_card] at dec ⊢
  exact dec

end GenLimit.LearningAlgorithmsLimit.MSM.LabelledDiagram
