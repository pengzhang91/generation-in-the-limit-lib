import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TerminalQuotient
import Mathlib.Data.List.Infix

/-! # Observation trees with recoverable transition endpoints

Vertices are prefixes of observed read/output histories. A complete data
set determines a finite collection of labelled transitions and their endpoint
names. This collection is exactly the image of the tree under the endpoint
labelling, including the root when the sample is empty. -/
namespace GenLimit.LearningAlgorithmsLimit.MSM.ObservedTree
open LabelledDiagram

variable {A B : Type*} [DecidableEq A] [DecidableEq B]
abbrev Samples (A B : Type*) := Finset (List (A × B))

def vertices (S : Samples A B) := insert [] (S.biUnion (fun es ↦ es.inits.toFinset))
abbrev Node (S : Samples A B) := ↥(vertices S)

def content (S : Samples A B) : Finset (A × B) := S.biUnion List.toFinset

def kind (endpts : A × B → ℕ × ℕ) (root : ℕ) (u : List (A × B)) :=
  u.foldl (fun _ e ↦ (endpts e).2) root

theorem kind_append (endpts : A × B → ℕ × ℕ) (root : ℕ) (u : List (A × B)) (e) :
    kind endpts root (u ++ [e]) = (endpts e).2 := by simp [kind,List.foldl_append]

def edge (S : Samples A B) (x : Node S) (a : A) (b : B) (y : Node S) :=
  y.val = x.val ++ [(a,b)]

def tree (endpts : A × B → ℕ × ℕ) (root : ℕ) (S : Samples A B) : LabelledDiagram A B ℕ :=
  ⟨Node S,inferInstance,edge S,fun x ↦ kind endpts root x.val⟩

/-- A complete sample follows the displayed labelled transitions from the
given root. -/
inductive Path (endpts : A × B → ℕ × ℕ) : ℕ → List (A × B) → ℕ → Prop
  | nil (q) : Path endpts q [] q
  | cons (e : A × B) {es r} (rest : Path endpts (endpts e).2 es r) :
    Path endpts (endpts e).1 (e :: es) r

theorem Path.uncons {en : A × B → ℕ × ℕ} {q r e es}
    (h : Path en q (e::es) r) : (en e).1 = q ∧ Path en (en e).2 es r := by
  cases h with | cons _ rest => exact ⟨rfl,rest⟩

theorem prefix_source {en : A × B → ℕ × ℕ} {root last : ℕ} {u e v}
    (h : Path en root (u ++ e :: v) last) : kind en root u = (en e).1 := by
  induction u generalizing root with
  | nil => cases h; rfl
  | cons x u ih => cases h with | cons _ ht => exact ih ht

theorem node_prefix {S : Samples A B} {es u : List (A × B)} (hes : es ∈ S)
    (hu : u <+: es) : u ∈ vertices S :=
  Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨es,hes,List.mem_toFinset.mpr ((List.mem_inits ..).mpr hu)⟩)

private theorem split_edge {S : Samples A B} {x y : Node S} {a b} (h : edge S x a b y) :
    ∃ tail, x.val ++ (a,b) :: tail ∈ S := by
  have hv := y.property
  rw [show y.val = x.val ++ [(a,b)] from h] at hv
  simp only [vertices,Finset.mem_insert,Finset.mem_biUnion,List.mem_toFinset] at hv
  rcases hv with hnil | ⟨es,hes,hu⟩
  · simp at hnil
  · obtain ⟨tail,hEq⟩ := (List.mem_inits ..).mp hu
    exact ⟨tail,by simpa [← hEq,List.append_assoc] using hes⟩

/-- Read the graph endpoints and the actual transition table from any tree edge. -/
theorem edge_spec {en : A × B → ℕ × ℕ} {root : ℕ} {S : Samples A B}
    (paths : ∀ es ∈ S, ∃ r, Path en root es r)
    {x y : Node S} {a b} (he : edge S x a b y) :
    kind en root x.val = (en (a,b)).1 ∧ kind en root y.val = (en (a,b)).2 ∧ (a,b) ∈ content S := by
  obtain ⟨tail,ht⟩ := split_edge he
  obtain ⟨_,hp⟩ := paths _ ht
  exact ⟨prefix_source hp,by rw [show y.val = _ from he,kind_append],
    Finset.mem_biUnion.mpr ⟨_,ht,List.mem_toFinset.mpr (by simp)⟩⟩

theorem edge_of_mem {S : Samples A B} {e : A × B} (h : e ∈ content S) :
    ∃ x y : Node S, edge S x e.1 e.2 y := by
  obtain ⟨es,hes,he⟩ := Finset.mem_biUnion.mp h
  obtain ⟨u,v,rfl⟩ := List.append_of_mem (List.mem_toFinset.mp he)
  exact ⟨⟨u,node_prefix hes ⟨e::v,rfl⟩⟩,⟨u++[e],node_prefix hes ⟨v,by simp⟩⟩,rfl⟩

theorem typed_tree {en : A × B → ℕ × ℕ} {root : ℕ} {S : Samples A B}
    (paths : ∀ es ∈ S, ∃ r, Path en root es r) (δ : ℕ → A → ℕ × B)
    (ok : ∀ e ∈ content S, δ (en e).1 e.1 = ((en e).2,e.2)) :
    Deterministic (edge S) ∧ Typed (edge S) (tree en root S).kind := by
  have step {x y : Node S} {a b} (he : edge S x a b y) :
      δ (kind en root x.val) a = (kind en root y.val,b) := by
    obtain ⟨hx,hy,hm⟩ := edge_spec paths he
    rw [hx,hy]
    exact ok (a,b) hm
  have agree {x y u v : Node S} {a b c} (h : kind en root x.val = kind en root y.val)
      (e : edge S x a b u) (f : edge S y a c v) :
      (kind en root u.val,b) = (kind en root v.val,c) :=
    (step e).symm.trans ((congrArg (fun q ↦ δ q a) h).trans (step f))
  constructor
  · intro q a b c u v e f
    have h := congrArg Prod.snd (agree rfl e f)
    refine ⟨h,Subtype.ext ?_⟩
    exact e.trans ((congrArg (fun z ↦ q.val ++ [(a,z)]) h).trans f.symm)
  · exact ⟨fun _ _ _ _ _ _ _ h e f ↦ congrArg Prod.fst (agree h e f),
      fun _ _ _ _ _ _ _ h e f ↦ congrArg Prod.snd (agree h e f),
      fun _ _ _ _ _ _ e f ↦ (edge_spec paths e).1.trans (edge_spec paths f).1.symm⟩

theorem typeEdges_eq {en : A × B → ℕ × ℕ} {root : ℕ} {S : Samples A B}
    (paths : ∀ es ∈ S, ∃ r, Path en root es r) :
    (tree en root S).typeEdges = fun q a b r ↦
      (a,b) ∈ content S ∧ q = (en (a,b)).1 ∧ r = (en (a,b)).2 := by
  funext q a b r
  apply propext
  constructor
  · rintro ⟨x,y,rfl,rfl,he⟩
    obtain ⟨hx,hy,hm⟩ := edge_spec paths he
    exact ⟨hm,hx,hy⟩
  · rintro ⟨hm,rfl,rfl⟩
    obtain ⟨x,y,he⟩ := edge_of_mem hm
    obtain ⟨hx,hy,_⟩ := edge_spec paths he
    exact ⟨x,y,hx,hy,he⟩

def names (en : A × B → ℕ × ℕ) (root : ℕ) (C : Finset (A × B)) :=
  insert root (C.image fun e ↦ (en e).2)

theorem kind_range (en : A × B → ℕ × ℕ) (root : ℕ) (S : Samples A B) :
    Set.range (tree en root S).kind = (names en root (content S) : Set ℕ) := by
  ext q
  constructor
  · rintro ⟨⟨u,hu⟩,rfl⟩
    induction u using List.reverseRecOn with
    | nil => exact Finset.mem_insert_self ..
    | append_singleton u e _ =>
      have he : edge S ⟨u,by
        rcases Finset.mem_insert.mp hu with hn | hmem
        · simp at hn
        · obtain ⟨es,hes,hm⟩ := Finset.mem_biUnion.mp hmem
          exact node_prefix hes ((List.prefix_append ..).trans ((List.mem_inits ..).mp (List.mem_toFinset.mp hm)))⟩
          e.1 e.2 ⟨u++[e],hu⟩ := rfl
      obtain ⟨v,hv⟩ := split_edge he
      change kind en root (u++[e]) ∈ names en root (content S)
      rw [kind_append]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e,Finset.mem_biUnion.mpr
        ⟨_,hv,List.mem_toFinset.mpr (by simp)⟩,rfl⟩)
  · intro h
    rcases Finset.mem_insert.mp h with rfl | him
    · exact ⟨⟨[],Finset.mem_insert_self ..⟩,rfl⟩
    · obtain ⟨e,hm,rfl⟩ := Finset.mem_image.mp him
      obtain ⟨x,y,hxy⟩ := edge_of_mem hm
      exact ⟨y,by change kind en root y.val = _; rw [show y.val = _ from hxy,kind_append]⟩

end GenLimit.LearningAlgorithmsLimit.MSM.ObservedTree
