import GenLimit.Paper00_LanguageIdentification.Effective.PresentationBoundary

/-! # Total range generators for nonempty targets

Appendix II describes a sequence of words, whereas §11 uses the range of
a partial recursive function. A uniform index map converts the latter into
a total sequence on every nonempty target.
-/

namespace GenLimit.Gold.Effective

open Nat.Partrec (Code)

def TotalGenerator (c : Code) (L : Language) : Prop := Generator c L ∧ ∀ x, (c.eval x).Dom

private def output (c : Code) (n : ℕ) := Code.evaln n.unpair.2 c n.unpair.1

private theorem output_comp : Computable₂ output :=
  (Code.primrec_evaln.to_comp.comp (((Computable.snd.comp (Computable.unpair.comp Computable.snd)).pair
    Computable.fst).pair (Computable.fst.comp (Computable.unpair.comp Computable.snd)))).to₂

/-- Search for one emitted word. While bounded evaluation of the requested
input has no answer, return that first word. -/
theorem totalize_range :
    ∃ k : Code → Code, Computable k ∧ ∀ c L, Generator c L → L.Nonempty → TotalGenerator (k c) L := by
  let result (c : Code) (n : ℕ) :=
    (Nat.rfindOpt (output c)).map fun y => (output c n).getD y
  have comp : Partrec₂ result :=
    ((Partrec.rfindOpt output_comp).comp Computable.fst).map
      (Computable.option_getD (output_comp.comp (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst)) Computable.snd).to₂
  obtain ⟨k,hk,eq⟩ := compile comp
  refine ⟨k,hk,fun c L hc he => ?_⟩
  have occur (x : ℕ) : x ∈ L ↔ ∃ n, output c n = some x := by
    rw [hc x]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨t, ht⟩ := Code.evaln_complete.mp hu
      exact ⟨Nat.pair u t, by simpa [output] using ht⟩
    · rintro ⟨n,hn⟩
      exact ⟨_, Code.evaln_sound hn⟩
  obtain ⟨x,hx⟩ := he
  obtain ⟨n, hn⟩ := (occur x).mp hx
  have dom := Nat.rfindOpt_dom.mpr ⟨n,x,hn⟩
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp dom
  have chosen := Part.eq_some_iff.mpr hy
  have eval (u : ℕ) : (k c).eval u = Part.some ((output c u).getD y) := by
    rw [eq]
    simp [result, chosen]
  refine ⟨fun w => ⟨fun hw => ?_, ?_⟩, fun u => (eval u) ▸ Part.some_dom _⟩
  · obtain ⟨u, hu⟩ := (occur w).mp hw
    exact ⟨u, by simp [eval, hu]⟩
  · rintro ⟨u,hu⟩
    rw [eval] at hu
    have hval := Part.mem_some_iff.mp hu
    cases hv : output c u with
    | none =>
      have : w = y := by simpa [hv] using hval
      exact this ▸ (occur y).mpr (Nat.rfindOpt_spec hy)
    | some b =>
      have : w = b := by simpa [hv] using hval
      exact this ▸ (occur b).mpr ⟨u,hv⟩

theorem total_generator_identification_of_tester {I : Type*} [Primcodable I]
    {m : Method I} {C : Set Language} (nonempty : ∀ L ∈ C, ∀ s ∈ m L, L.Nonempty)
    (h : Identifiable Tester m C) : Identifiable TotalGenerator m C := by
  obtain ⟨k,hk,hs⟩ := totalize_range
  obtain ⟨M,hM,hm⟩ := generator_identification_of_tester h
  refine ⟨k ∘ M,hk.comp hM,fun L hL s hs' => ?_⟩
  obtain ⟨c,hc,T,stable⟩ := hm L hL s hs'
  exact ⟨k c, hs c L hc (nonempty L hL s hs'), T,fun t ht => congrArg k (stable t ht)⟩

/-- I.7 also supplies total names, since the learned program computes the text. -/
theorem total_generator_primitive_text (C : Set Language) :
    Identifiable TotalGenerator primitiveRecursiveText C := by
  obtain ⟨M,hM,hm⟩ := learns_primitive_functions
  refine ⟨M,hM,fun L _ s hs => ?_⟩
  obtain ⟨c,he,stable⟩ := hm s hs.1
  refine ⟨c, ⟨fun x => ?_, fun x => (he x) ▸ Part.some_dom _⟩, stable⟩
  rw [← hs.2]
  simp [he, Set.mem_range, eq_comm]

end GenLimit.Gold.Effective
