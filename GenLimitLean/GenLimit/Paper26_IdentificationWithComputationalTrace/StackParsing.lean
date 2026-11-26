import GenLimit.Paper26_IdentificationWithComputationalTrace.StackDerivation

namespace GenLimit.ComputationalTrace.PDA
open Control

private theorem graft {P : Program ℕ} {p q z : Vertex} {b eat selected : Bool} {op bs fs}
    (legal : ∀ stop, (Label.mk p b stop q eat op selected).Legal P)
    (tail : Forest P fs q (op.apply (b :: bs)) z) :
    ∃ fs' stop, Forest P fs' p (b :: bs) z ∧
      tokens fs' = Label.mk p b stop q eat op selected :: tokens fs := by
  cases op with
  | pop =>
    refine ⟨.node _ .nil .nil :: fs,q,.cons (.pop (legal _) rfl rfl) tail,?_⟩
    simp [tokens,Tree.items]
  | keep =>
    cases tail with
    | @cons t ts _ _ mid _ _ one more =>
      refine ⟨.node _ t .nil :: ts,mid,.cons (.keep (legal _) rfl one) more,?_⟩
      simp [tokens,Tree.items]
  | push bit =>
    cases tail with
    | @cons t ts _ _ mid _ _ one more =>
      cases more with
      | @cons r rs _ _ fin _ _ two rest =>
        refine ⟨.node _ t r :: rs,fin,.cons (.push (legal _) rfl one two) rest,?_⟩
        simp [tokens,Tree.items,List.append_assoc]

/-- Select the last cutoff-many consuming steps of this computation. This
bounds the number of extra marks needed to keep a shortened input long. -/
theorem parse_finish {P : Program ℕ} {c ds} (hf : Finish device P.machine c ds) (cutoff : ℕ) :
    ∃ z fs, z.look = none ∧ Forest P fs (vtx c) c.2.stack z ∧
      letters (tokens fs) = c.2.input ∧
      (tokens fs).map (fun a => a.start.state) ++ [z.state] = c.1 :: ds.map Prod.fst ∧
      ((tokens fs).filter Label.selected).length = min cutoff c.2.input.length := by
  induction hf with
  | @halt c yes =>
    obtain ⟨hu,hb⟩ : c.2.input = [] ∧ c.2.stack = [] := by simpa using yes
    refine ⟨vtx c,[],by simp [vtx,hu],hb ▸ .nil _,by simp [letters,tokens,hu],rfl,by simp [tokens,hu]⟩
  | @next c d ds no hstep tail ih =>
    obtain ⟨z,fs,hz,forest,ws,states,sel⟩ := ih
    obtain ⟨b,bs,eat,op,hb,rule,eok,du,db⟩ := edge_info hstep
    let flag := eat && decide (c.2.input.length ≤ cutoff)
    have legal (stop) : (Label.mk (vtx c) b stop (vtx d) eat op flag).Legal P := by
      refine ⟨rule,?_,by simp [flag]; tauto⟩
      cases he : eat <;> cases hu : c.2.input <;> simp_all [vtx]
    obtain ⟨fs',stop,g,eq⟩ := graft legal (db ▸ forest)
    refine ⟨z,fs',hz,hb ▸ g,?_,?_,?_⟩
    · rw [eq]
      simp only [letters,List.flatMap_cons,Label.word]
      change (if eat then c.2.input.head?.toList else []) ++ letters (tokens fs) = _
      rw [ws,du]
      cases he : eat <;> cases hu : c.2.input <;> simp
    · rw [eq,List.map_cons,List.cons_append,states]
      rfl
    · rw [eq]
      cases he : eat <;> cases hu : c.2.input <;>
        by_cases hl : c.2.input.length ≤ cutoff <;> simp_all [flag] <;> omega

theorem Parse.chain {P : Program ℕ} {t p b z} (h : Parse P t p b z) :
    t.items.map Label.start ++ [z] = p :: t.items.map Label.next := by
  induction h with
  | pop _ _ he => simp [Tree.items,he]
  | @keep a l _ _ _ ih => simpa [Tree.items] using congrArg (List.cons a.start) ih
  | @push a l r bit mid _ _ _ _ il ir =>
    simp only [Tree.items,List.map_cons,List.map_append,List.cons_append,List.append_assoc,ir]
    have hl := congrArg (· ++ r.items.map Label.next) il
    simpa [List.append_assoc] using congrArg (List.cons a.start) hl

end GenLimit.ComputationalTrace.PDA
