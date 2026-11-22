import GenLimit.Paper11_LearningAlgorithmsInTheLimit.ObservedTree

namespace GenLimit.LearningAlgorithmsLimit.MSM.ObservedTree
open LabelledDiagram
variable {A B : Type} [DecidableEq A] [DecidableEq B]

def canonical (en : A × B → ℕ × ℕ) (root : ℕ) (C : Finset (A × B)) : LabelledDiagram A B ℕ :=
  ⟨↥(names en root C),inferInstance,fun x a b y ↦
    (a,b) ∈ C ∧ x.val = (en (a,b)).1 ∧ y.val = (en (a,b)).2,Subtype.val⟩

def rootNode (S : Samples A B) : Node S := ⟨[],Finset.mem_insert_self ..⟩
def rootName (en : A × B → ℕ × ℕ) (root : ℕ) (C : Finset (A × B)) :
    (canonical en root C).State := ⟨root,Finset.mem_insert_self ..⟩

def named (en : A × B → ℕ × ℕ) (root : ℕ) (C : Finset (A × B)) (q : ℕ) :
    (canonical en root C).State :=
  if h : q ∈ names en root C then ⟨q,h⟩ else rootName en root C

theorem named_val {en : A × B → ℕ × ℕ} {root : ℕ} {C : Finset (A × B)} {q : ℕ}
    (h : q ∈ names en root C) : (named en root C q).val = q := by simp [named,h]

theorem named_root (en : A × B → ℕ × ℕ) (root : ℕ) (C : Finset (A × B)) :
    named en root C root = rootName en root C := by
  simp [named,names,rootName]

theorem canonical_deterministic {en : A × B → ℕ × ℕ} {root : ℕ} {C : Finset (A × B)}
    (δ : ℕ → A → ℕ × B) (ok : ∀ e ∈ C, δ (en e).1 e.1 = ((en e).2,e.2)) :
    Deterministic (canonical en root C).edge := by
  rintro x a b c u v ⟨hb,hx,hu⟩ ⟨hc,hx',hv⟩
  have eq := (ok (a,b) hb).symm.trans ((congrArg (fun q ↦ δ q a) (hx.symm.trans hx')).trans (ok (a,c) hc))
  exact ⟨congrArg Prod.snd eq,Subtype.ext (hu.trans ((congrArg Prod.fst eq).trans hv.symm))⟩

theorem canonical_run {en : A × B → ℕ × ℕ} {root : ℕ} {S : Samples A B}
    (paths : ∀ es ∈ S, ∃ r, Path en root es r) (δ : ℕ → A → ℕ × B)
    (ok : ∀ e ∈ content S, δ (en e).1 e.1 = ((en e).2,e.2)) :
    ∃ h, Run (tree en root S) (canonical en root (content S)) h ∧
      h (rootNode S) = rootName en root (content S) := by
  classical
  obtain ⟨hd,ht⟩ := typed_tree paths δ ok
  obtain ⟨F,hpath,hinj,hE⟩ := (tree en root S).reaches_types hd ht
  have ran := (range_eq_of_sound_run hpath).trans (kind_range en root S)
  let f (x : F.State) : (canonical en root (content S)).State :=
    ⟨F.kind x,by change F.kind x ∈ (↑(names en root (content S)) : Set ℕ); rw [← ran]; exact Set.mem_range_self x⟩
  have bij : Function.Bijective f := ⟨fun _ _ h ↦ hinj (congrArg Subtype.val h),by
    intro y
    obtain ⟨x,hx⟩ := (show y.val ∈ Set.range F.kind from ran.symm ▸ y.property)
    exact ⟨x,Subtype.ext hx⟩⟩
  let eqv := Equiv.ofBijective f bij
  have rel : Run F (canonical en root (content S)) eqv := by
    apply Run.rename
    intro x a b y
    change F.edge x a b y ↔ (a,b) ∈ content S ∧ F.kind x = (en (a,b)).1 ∧ F.kind y = (en (a,b)).2
    rw [← show F.typeEdges (F.kind x) a b (F.kind y) =
        ((a,b) ∈ content S ∧ F.kind x = (en (a,b)).1 ∧ F.kind y = (en (a,b)).2) by
      rw [hE,typeEdges_eq paths]]
    constructor
    · intro he
      exact ⟨x,y,rfl,rfl,he⟩
    · rintro ⟨u,v,hu,hv,he⟩
      simpa [hinj hu,hinj hv] using he
  obtain ⟨g,hg,hk⟩ := sound_run_map hpath
  exact ⟨_,hg.trans rel,Subtype.ext (hk (rootNode S))⟩

/-- The learner fixes its tie order on the normalized graph, so its terminal
representation depends only on the observed transitions. -/
structure Solution (D : LabelledDiagram.{0} A B ℕ) where
  graph : LabelledDiagram.{0} A B ℕ
  map : D.State → graph.State
  run : Run D graph map
  terminal : Terminal graph
  deterministic : Deterministic graph.edge

noncomputable def solve (D : LabelledDiagram.{0} A B ℕ) (hd : Deterministic D.edge) : Solution D :=
  Classical.choice (show Nonempty (Solution D) by
    obtain ⟨F,_,ht,hdet,f,hf⟩ := terminal_quotient D 0 hd
    exact ⟨⟨F,f,hf,ht,hdet⟩⟩)

theorem solve_tree {en : A × B → ℕ × ℕ} {root : ℕ} {S : Samples A B}
    (paths : ∀ es ∈ S, ∃ r, Path en root es r) (δ : ℕ → A → ℕ × B)
    (ok : ∀ e ∈ content S, δ (en e).1 e.1 = ((en e).2,e.2)) :
    let sol := solve (canonical en root (content S)) (canonical_deterministic δ ok)
    ∃ f, Run (tree en root S) sol.graph f ∧ f (rootNode S) = sol.map (rootName en root (content S)) := by
  dsimp only
  obtain ⟨f,hf,hr⟩ := canonical_run paths δ ok
  let sol := solve (canonical en root (content S)) (canonical_deterministic δ ok)
  exact ⟨_,hf.trans sol.run,congrArg sol.map hr⟩

end GenLimit.LearningAlgorithmsLimit.MSM.ObservedTree
