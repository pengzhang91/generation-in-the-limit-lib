import GenLimit.Paper26_IdentificationWithComputationalTrace.StackContext

namespace GenLimit.ComputationalTrace.PDA

private theorem cast_parse {P : Program ℕ} {t p b z p' b' z'} (h : Parse P t p b z)
    (e : (p,b,z) = (p',b',z')) : Parse P t p' b' z' := by
  obtain ⟨rfl,e'⟩ := Prod.mk.inj e
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj e'
  exact h

/-- Shorten a derivation while preserving the entire ordered list of
protected instructions. The size factor depends only on the observed states. -/
theorem compress {P : Program ℕ} {original : Tree Label} {p b z}
    (originalParse : Parse P original p b z) (S : Finset ℕ) :
    ∃ t, Parse P t p b z ∧ t.items.filter (protect S) = original.items.filter (protect S) ∧
      t.size ≤ Tree.treeFactor (palette S).card * (t.marks (protect S) + 1) := by
  classical
  let candidate (n : ℕ) := ∃ t : Tree Label, Parse P t p b z ∧
    t.items.filter (protect S) = original.items.filter (protect S) ∧ t.size = n
  have existsSize : ∃ n, candidate n := ⟨_,original,originalParse,rfl,rfl⟩
  obtain ⟨t,parsed,same,sz⟩ := Nat.find_spec existsSize
  refine ⟨t,parsed,same,Tree.size_le_marks _ _ (palette S) t (fun a _ _ _ => mem_palette S a) ?_⟩
  intro a l r outerIn a' l' r' side hcount hcolour
  let outer := Tree.node a l r
  let inner := Tree.node a' l' r'
  obtain ⟨s₁,b₁,z₁,first,last,parseA,whole,plug⟩ := Parse.context outerIn (by simp) parsed
  have innerIn : inner.Sub outer := side.elim Tree.Sub.left Tree.Sub.right
  obtain ⟨s₂,b₂,z₂,pre,post,parseB,inside,_⟩ := Parse.context innerIn (by simp [inner]) parseA
  have hsize : inner.size < outer.size := by
    change inner.Sub l ∨ inner.Sub r at side
    rcases side with h | h
    · exact lt_of_le_of_lt h.size_le (by simp [outer]; omega)
    · exact lt_of_le_of_lt h.size_le (by simp [outer]; omega)
  have hf : (inner.items.filter (protect S)).length = (outer.items.filter (protect S)).length := hcount
  rw [inside,List.filter_append,List.filter_append,List.length_append,List.length_append] at hf
  have hp : pre.filter (protect S) = [] := List.length_eq_zero_iff.mp (by omega)
  have hq : post.filter (protect S) = [] := List.length_eq_zero_iff.mp (by omega)
  have hac := cast_parse parseA parseA.root
  have hbc := cast_parse parseB parseB.root
  have key := equal_key_of_unmarked_context hac hbc inside hp hq hcolour.symm
  have fill : Parse P inner s₁ b₁ z₁ := cast_parse parseB (parseB.root.trans (key.symm.trans parseA.root.symm))
  obtain ⟨smaller,ok,items⟩ := plug _ fill
  have filt : outer.items.filter (protect S) = inner.items.filter (protect S) := by
    simp [inside,List.filter_append,hp,hq]
  have valid : candidate smaller.size := by
    refine ⟨smaller,ok,?_,rfl⟩
    rw [← same,items,whole]
    change (first ++ inner.items ++ last).filter _ = (first ++ outer.items ++ last).filter _
    simp only [List.filter_append,filt]
  have minimal := Nat.find_min' existsSize valid
  rw [← sz] at minimal
  change t.items.length ≤ smaller.items.length at minimal
  rw [whole,items] at minimal
  change (first ++ outer.items ++ last).length ≤ (first ++ inner.items ++ last).length at minimal
  simp only [List.length_append] at minimal
  change inner.items.length < outer.items.length at hsize
  omega

end GenLimit.ComputationalTrace.PDA
