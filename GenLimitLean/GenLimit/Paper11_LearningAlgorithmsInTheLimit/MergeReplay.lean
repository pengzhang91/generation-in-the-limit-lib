import GenLimit.Paper11_LearningAlgorithmsInTheLimit.CanonicalMerge
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TaggedTape

/-! # Compiling a terminal observation-tree quotient as a tape machine -/
namespace GenLimit.LearningAlgorithmsLimit.MSM.Replay
open Policy Rational ObservedTree LabelledDiagram
variable {σ : Type} [Fintype σ] [Encodable σ] [DecidableEq σ]

private noncomputable def number {Q : Type} [Fintype Q] (root x : Q) : ℕ := by
  classical
  exact if x = root then 1 else (Fintype.equivFin Q x).val + 2

private theorem number_pos {Q : Type} [Fintype Q] (root x : Q) : 0 < number root x := by
  classical
  unfold number
  split <;> omega

private theorem number_inj {Q : Type} [Fintype Q] (root : Q) : Function.Injective (number root) := by
  classical
  intro x y h
  by_cases hx : x = root <;> by_cases hy : y = root
  · exact hx.trans hy.symm
  · simp [number,hx,hy] at h
  · simp [number,hx,hy] at h
  · exact (Fintype.equivFin Q).injective (Fin.ext (Nat.add_right_cancel (by simpa only [number,if_neg hx,if_neg hy] using h)))

private noncomputable def stateOf {Q : Type} [Fintype Q] (root : Q) (n : ℕ) : Q := by
  classical
  exact if h : ∃ x, number root x = n then h.choose else root

private theorem stateOf_number {Q : Type} [Fintype Q] (root x : Q) :
    stateOf root (number root x) = x := by
  classical
  let h : ∃ y, number root y = number root x := ⟨x,rfl⟩
  simp only [stateOf,dif_pos h]
  exact number_inj root h.choose_spec

private noncomputable def row (G : LabelledDiagram.{0} σ (Action σ) ℕ) (root : G.State)
    (stop : Event σ → Bool) (blank : σ) (x : G.State) (a : σ) : TuringInstruction σ := by
  classical
  exact if h : ∃ w : Action σ × G.State, G.edge x a w.1 w.2 then
    (if stop (a,h.choose.1) then 0 else number root h.choose.2,h.choose.1)
    else (0,blank,.stay)

private theorem row_edge {G : LabelledDiagram.{0} σ (Action σ) ℕ} (hd : Deterministic G.edge)
    (root : G.State) (stop : Event σ → Bool) (blank : σ) {x y a b} (he : G.edge x a b y) :
    row G root stop blank x a = (if stop (a,b) then 0 else number root y,b) := by
  classical
  have h : ∃ w : Action σ × G.State, G.edge x a w.1 w.2 := ⟨(b,y),he⟩
  obtain ⟨hb,hy⟩ := hd _ _ _ _ _ _ h.choose_spec he
  simp [row,h,hb,hy]

noncomputable def compile (G : LabelledDiagram.{0} σ (Action σ) ℕ) (root : G.State)
    (stop : Event σ → Bool) (blank : σ) : TuringProgram σ := by
  classical
  exact (tabulate 1 (Finset.univ.image (number root)) (blank,TuringHeadMove.stay)
    (fun k a ↦ row G root stop blank (stateOf root k) a)).rows

theorem compile_edge {G : LabelledDiagram.{0} σ (Action σ) ℕ} (hd : Deterministic G.edge)
    (root : G.State) (stop : Event σ → Bool) (blank : σ) {x y a b} (he : G.edge x a b y) :
    (compile G root stop blank).instruction (number root x) a =
      (if stop (a,b) then 0 else number root y,b) := by
  classical
  unfold TuringProgram.instruction compile
  rw [tabulate_row _ _ _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)),stateOf_number]
  exact row_edge hd root stop blank he

private abbrev Endpoints (σ : Type) := Event σ → ℕ × ℕ

noncomputable def guess (en : Endpoints σ) (blank : σ) (C : Finset (Event σ)) : TuringProgram σ := by
  classical
  exact if hd : Deterministic (canonical en 1 C).edge then
    let sol := solve _ hd
    compile sol.graph (sol.map (rootName en 1 C)) (fun e ↦ decide ((en e).2 = 0)) blank
    else []

/-- The returned representation compiles an actual terminal MSM quotient
with the observation tree's initial state carried through its mergers. -/
def IsMSMOutput (en : Event σ → ℕ × ℕ) (blank : σ) (S : Samples σ (Action σ)) (M : TuringProgram σ) :=
  ∃ (G : LabelledDiagram.{0} σ (Action σ) ℕ) (f : (tree en 1 S).State → G.State),
    Run (tree en 1 S) G f ∧ Terminal G ∧ Deterministic G.edge ∧
      M = compile G (f (rootNode S)) (fun e ↦ decide ((en e).2 = 0)) blank

theorem guess_isMSM {en : Event σ → ℕ × ℕ} (blank : σ) {S : Samples σ (Action σ)}
    (paths : ∀ es ∈ S, ∃ r, Path en 1 es r) (δ : ℕ → σ → ℕ × Action σ)
    (ok : ∀ e ∈ content S, δ (en e).1 e.1 = ((en e).2,e.2)) :
    IsMSMOutput en blank S (guess en blank (content S)) := by
  classical
  have hd : Deterministic (canonical en 1 (content S)).edge := canonical_deterministic δ ok
  let sol := solve (canonical en 1 (content S)) hd
  obtain ⟨f,hf,hr⟩ := solve_tree paths δ ok
  exact ⟨sol.graph,f,hf,sol.terminal,sol.deterministic,by simp [guess,hd,hr,sol]⟩

/-- Replay on the actual single tape preserves the full read/write/move
record and the final tape. The public endpoint tags mark the final step
even when a terminal quotient merges a leaf with another state. -/
theorem replay {en : Endpoints σ} {C : Finset (Event σ)} {P : TuringProgram σ} {blank : σ}
    (ok : ∀ e ∈ C, P.instruction (en e).1 e.1 = ((en e).2,e.2))
    {t ds out} (exec : Execution P blank 1 t ds out) (path : Path en 1 ds 0)
    (mem : ∀ e ∈ ds, e ∈ C) : Execution (guess en blank C) blank 1 t ds out := by
  classical
  have hd : Deterministic (canonical en 1 C).edge := canonical_deterministic P.instruction ok
  let sol := solve (canonical en 1 C) hd
  let root := sol.map (rootName en 1 C)
  let code (q : ℕ) := if q = 0 then 0 else number root (sol.map (named en 1 C q))
  let M := compile sol.graph root (fun e ↦ decide ((en e).2 = 0)) blank
  have lift {q t ds out} (ex : Execution P blank q t ds out) (hp : Path en q ds 0)
      (hmem : ∀ e ∈ ds, e ∈ C) (hq : q ∈ names en 1 C) : Execution M blank (code q) t ds out := by
    induction ex with
    | halt => exact .halt _
    | @step q t es out hn ht ih =>
      let e : Event σ := (t.scanned,(P.instruction q t.scanned).2)
      have src : (en e).1 = q := hp.uncons.1
      have rest : Path en (en e).2 es 0 := hp.uncons.2
      have hm : e ∈ C := hmem e List.mem_cons_self
      have dest : (P.instruction q t.scanned).1 = (en e).2 := by
        have h := ok e hm
        rw [src] at h
        exact congrArg Prod.fst h
      have hy : (en e).2 ∈ names en 1 C := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hm)
      have arc : (canonical en 1 C).edge (named en 1 C q) e.1 e.2 (named en 1 C (en e).2) :=
        ⟨hm,(named_val hq).trans src.symm,named_val hy⟩
      have hrow := compile_edge sol.deterministic root (fun z : Event σ ↦ decide ((en z).2 = 0)) blank
        (sol.run.preserves _ _ _ _ arc)
      have hval : M.instruction (code q) t.scanned = (code (en e).2,e.2) := by
        simpa only [M,code,if_neg hn,decide_eq_true_eq] using hrow
      have nonzero : code q ≠ 0 := by simp only [code,if_neg hn]; exact (number_pos ..).ne'
      have child := ih (dest ▸ rest) (fun v hv ↦ hmem v (List.mem_cons_of_mem _ hv)) (dest ▸ hy)
      rw [dest] at child
      have tail : Execution M blank (M.instruction (code q) t.scanned).1
          (t.writeAndMove blank (M.instruction (code q) t.scanned).2.1 (M.instruction (code q) t.scanned).2.2)
          es out := by rw [hval]; exact child
      simpa only [hval] using Execution.step nonzero tail
  have h1 : code 1 = 1 := by simp [code,named_root,root,number]
  have hM : guess en blank C = M := by simp [guess,hd,M,sol,root]
  rw [hM,← h1]
  exact lift exec path mem (Finset.mem_insert_self ..)

end GenLimit.LearningAlgorithmsLimit.MSM.Replay
