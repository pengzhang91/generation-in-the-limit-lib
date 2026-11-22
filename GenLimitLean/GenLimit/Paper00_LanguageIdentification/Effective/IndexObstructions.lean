import GenLimit.Paper00_LanguageIdentification.Effective.PresentationBoundary

/-! # The two index-translation obstructions in Gold's §11 -/

namespace GenLimit.Gold.Effective

open Nat.Partrec (Code)
open GenLimit.Support

/-- The universal assertion in the printed Corollary 10.1 already fails
for the class of all languages, with the universal language as its infinite recursive member. -/
theorem printed_corollary_10_1_is_false :
    ¬ ∀ C : Set Language, Text.finiteLanguages ⊆ C →
      (∃ L ∈ C, L.Infinite ∧ L ∈ recursiveLanguages) → ¬ LimitTranslation Tester Generator C := by
  intro claim
  have hi : (Set.univ : Language) ∈ recursiveLanguages := by
    change Computable (bit Set.univ)
    exact (Computable.const 1).of_eq fun x => by simp [bit]
  exact claim Set.univ (Set.subset_univ _) ⟨Set.univ, Set.mem_univ _, Set.infinite_univ, hi⟩
    (tester_to_generator_limit Set.univ)

/-- Corrected direction of the printed Corollary 10.1. -/
theorem no_generator_to_tester_limit {C : Set Language} (finite : Text.finiteLanguages ⊆ C)
    {L : Language} (hl : L ∈ C) (hi : L.Infinite) (hr : L ∈ recursiveLanguages) :
    ¬ LimitTranslation Generator Tester C := by
  intro tr
  obtain ⟨e,he⟩ := tester_of_recursive hr
  obtain ⟨c,hc⟩ := generator_of_tester he
  obtain ⟨s,hs,hp⟩ := primitive_text_of_generator hc hi.nonempty
  exact PrimitiveDiagonal.obstruction finite hl hi hs hp
    (identification_of_limitTranslation (generator_primitive_text C) tr)

/-- Recognize the range by dovetailing over argument/time pairs. -/
theorem range_to_domain :
    ∃ k : Code → Code, Computable k ∧ ∀ c L, Generator c L → DomainGenerator (k c) L := by
  let test (p : Code × ℕ) (n : ℕ) := Code.evaln n.unpair.2 p.1 n.unpair.1 == some p.2
  have ht : Computable₂ test := by
    apply (Primrec.beq.to_comp.comp (Code.primrec_evaln.to_comp.comp
      (((Computable.snd.comp (Computable.unpair.comp Computable.snd)).pair
        (Computable.fst.comp Computable.fst)).pair (Computable.fst.comp (Computable.unpair.comp Computable.snd))))
      (Computable.option_some.comp (Computable.snd.comp Computable.fst))).of_eq
    intro a
    apply Bool.eq_iff_iff.mpr
    simp [test]
  obtain ⟨k,hk,spec⟩ := compile (f := fun c x => Nat.rfind (fun n => Part.some (test (c,x) n)))
    (Partrec.rfind (p := fun p n => Part.some (test p n)) ht.partrec)
  refine ⟨k,hk,fun c L h x => ?_⟩
  rw [spec, h x]
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨t,ht⟩ := Code.evaln_complete.mp hu
    have yes : test (c,x) (Nat.pair u t) = true := by
      change Code.evaln t c u = some x at ht
      simp [test, ht]
    obtain ⟨j,hj,_⟩ := Nat.rfind_min' yes
    exact Part.dom_iff_mem.mpr ⟨j,hj⟩
  · intro dom
    obtain ⟨j,hj⟩ := Part.dom_iff_mem.mp dom
    have yes := (Part.mem_some_iff.mp (Nat.rfind_spec hj)).symm
    exact ⟨j.unpair.1, Code.evaln_sound (by simpa [test] using yes)⟩

private def answer (p : (Code × Code) × ℕ) (t : ℕ) : Option ℕ :=
  bif (Code.evaln t p.1.1 p.2).isSome then some 1 else
    bif (Code.evaln t p.1.2 p.2).isSome then some 0 else none

private theorem answer_comp : Computable₂ answer := by
  have run {a : ((Code × Code) × ℕ) × ℕ → Code} (ha : Computable a) :=
    Primrec.option_isSome.to_comp.comp (Code.primrec_evaln.to_comp.comp
      ((Computable.snd.pair ha).pair (Computable.snd.comp Computable.fst)))
  exact ((run (Computable.fst.comp (Computable.fst.comp Computable.fst))).cond (Computable.const (some 1))
    ((run (Computable.snd.comp (Computable.fst.comp Computable.fst))).cond (Computable.const (some 0))
      (Computable.const none))).to₂

private theorem rfind_value {f : ℕ → Option ℕ} {b : ℕ} (h : ∃ t, f t = some b)
    (only : ∀ t a, f t = some a → a = b) : Nat.rfindOpt f = Part.some b := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a,ha⟩ := Part.dom_iff_mem.mp (Nat.rfindOpt_dom.mpr ⟨t,b,ht⟩)
  obtain ⟨u,hu⟩ := Nat.rfindOpt_spec ha
  exact Part.eq_some_iff.mpr ((only u a hu) ▸ ha)

/-- Race the two semidecision procedures to decide membership. -/
theorem tester_from_domains :
    ∃ k : Code × Code → Code, Computable k ∧ ∀ a b L,
      DomainGenerator a L → AntiDomainGenerator b L → Tester (k (a,b)) L := by
  obtain ⟨k,hk,spec⟩ := compile (f := fun ab x => Nat.rfindOpt (answer (ab,x))) (Partrec.rfindOpt answer_comp)
  refine ⟨k,hk, fun a b L ha hb x => ?_⟩
  rw [spec]
  have never (c : Code) (h : ¬ (c.eval x).Dom) (t : ℕ) : Code.evaln t c x = none := by
    apply Option.eq_none_iff_forall_not_mem.mpr
    exact fun _ mem => h (Part.dom_iff_mem.mpr ⟨_,Code.evaln_sound mem⟩)
  have someAt (c : Code) (h : (c.eval x).Dom) : ∃ t y, Code.evaln t c x = some y := by
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp h
    obtain ⟨t, ht⟩ := Code.evaln_complete.mp hy
    exact ⟨t,y,ht⟩
  constructor
  · intro hx
    obtain ⟨t,y,ht⟩ := someAt a ((ha x).mp hx)
    apply rfind_value ⟨t, by simp [answer, ht]⟩
    intro u r
    have hno := never b (fun d => (hb x).mpr d hx) u
    cases h : Code.evaln u a x <;> simp [answer, hno, h, eq_comm]
  · intro hx
    obtain ⟨t,y,ht⟩ := someAt b ((hb x).mp hx)
    have hno := never a (fun d => hx ((ha x).mpr d))
    apply rfind_value ⟨t, by simp [answer, hno, ht]⟩
    intro u r
    cases h : Code.evaln u b x <;> simp [answer, hno, h, eq_comm]

theorem no_domain_to_antidomain_limit {C : Set Language} (finite : Text.finiteLanguages ⊆ C)
    {L : Language} (hl : L ∈ C) (hi : L.Infinite) (hr : L ∈ recursiveLanguages) :
    ¬ LimitTranslation DomainGenerator AntiDomainGenerator C := by
  rintro ⟨g,hg,htr⟩
  obtain ⟨d,hd,hD⟩ := range_to_domain
  obtain ⟨k,hk,hK⟩ := tester_from_domains
  apply no_generator_to_tester_limit finite hl hi hr
  refine ⟨fun e t => k (d e, g (d e) t), (hk.comp ((hd.comp Computable.fst).pair
    (hg.comp (hd.comp Computable.fst) Computable.snd))).to₂, ?_⟩
  intro A hA e he
  have hdom := hD e A he
  obtain ⟨b,hb,T,stable⟩ := htr A hA (d e) hdom
  exact ⟨_, hK _ _ _ hdom hb, T, fun t ht => congrArg (fun c => k (d e,c)) (stable t ht)⟩

/-- A partial translation represented by a single-valued Σ⁰₂ graph.
The computable matrix is shared across inputs, outputs and witnesses. -/
def TwoRecursiveTranslation (src dst : NameRelation Code) (C : Set Language) : Prop :=
  ∃ R : (Code × Code) × ℕ → ℕ → Bool, Computable₂ R ∧
    let graph (a b : Code) := ∃ w, ∀ u, R ((a,b),w) u = true
    (∀ a b c, graph a b → graph a c → b = c) ∧
      ∀ L ∈ C, ∀ a, src a L → ∃ b, graph a b ∧ dst b L

/-- Approximate a Σ⁰₂ graph by its first surviving output/witness pair.
Single-valuedness makes the eventual output the translated name. -/
theorem limit_of_twoRecursive {src dst C} (tr : TwoRecursiveTranslation src dst C) :
    LimitTranslation src dst C := by
  classical
  obtain ⟨R, hR, unique, covers⟩ := tr
  let out (j : ℕ) := Denumerable.ofNat Code j.unpair.1
  let test (a : Code) (t j : ℕ) := boundedAll R ((a,out j),j.unpair.2) t
  have htest : Computable₂ fun p : Code × ℕ => fun j => test p.1 p.2 j := by
    have hpair := Computable.unpair.comp (Computable.snd (α := Code × ℕ) (β := ℕ))
    exact ((boundedAll_computable hR).comp (((Computable.fst.comp Computable.fst).pair
      ((Primrec.ofNat Code).to_comp.comp (Computable.fst.comp hpair))).pair (Computable.snd.comp hpair))
      (Computable.snd.comp Computable.fst)).to₂
  let choice (a : Code) (t : ℕ) := (firstTrue (fun p j => test p.1 p.2 j) (a,t) t).getD 0
  have hchoice : Computable₂ choice :=
    (Computable.option_getD ((firstTrue_computable htest).comp Computable.id Computable.snd) (Computable.const 0)).to₂
  refine ⟨fun a t => out (choice a t), (((Primrec.ofNat Code).to_comp.comp
    (Computable.fst.comp (Computable.unpair.comp hchoice)))).to₂, fun L hL a ha => ?_⟩
  obtain ⟨b,⟨w,hw⟩,hb⟩ := covers L hL a ha
  let P (j : ℕ) := ∀ u, R ((a,out j),j.unpair.2) u = true
  have ex : ∃ j, P j := ⟨Nat.pair (Encodable.encode b) w, by simpa [P,out] using hw⟩
  let k := Nat.find ex
  have hk : P k := Nat.find_spec ex
  have hOut := unique a (out k) b ⟨_,hk⟩ ⟨w,hw⟩
  have elim (i : ℕ) (hi : i < k) : ∃ S, ∀ t ≥ S, test a t i = false := by
    have bad : ¬ ∀ u, R ((a,out i),i.unpair.2) u = true := Nat.find_min ex hi
    push_neg at bad
    obtain ⟨u,hu⟩ := bad
    exact ⟨u+1,fun t ht => Bool.eq_false_iff.mpr (fun h => hu ((boundedAll_eq_true_iff ..).mp h u (by omega)))⟩
  obtain ⟨S, hS⟩ := eventually_forall_lt elim
  refine ⟨b,hb,max (k+1) S,fun t ht => ?_⟩
  have hkt : k < t := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left ..).trans ht)
  have good : test a t k = true := (boundedAll_eq_true_iff ..).mpr fun u _ => hk u
  let p (z : Code × ℕ) (j : ℕ) := test z.1 z.2 j
  have yes : firstTrue p (a,t) t ≠ none :=
    fun bad => Bool.noConfusion (good.symm.trans ((firstTrue_eq_none_iff p ..).mp bad k hkt))
  obtain ⟨j,hj⟩ := Option.ne_none_iff_exists'.mp yes
  have hjk := firstTrue_le_of_true hj hkt good
  have hkj : k ≤ j := by
    by_contra! h
    exact Bool.noConfusion ((firstTrue_spec hj).2.1.symm.trans (hS t ((le_max_right ..).trans ht) j h))
  have hck : choice a t = k := by
    change (firstTrue p (a,t) t).getD 0 = k
    simp [hj, Nat.le_antisymm hjk hkj]
  exact (congrArg out hck).trans hOut

/-- §11, Theorem 10.2, in the paper's graph-hierarchy formulation. -/
theorem no_two_recursive_domain_to_antidomain {C : Set Language} (finite : Text.finiteLanguages ⊆ C)
    {L : Language} (hl : L ∈ C) (hi : L.Infinite) (hr : L ∈ recursiveLanguages) :
    ¬ TwoRecursiveTranslation DomainGenerator AntiDomainGenerator C :=
  fun tr => no_domain_to_antidomain_limit finite hl hi hr (limit_of_twoRecursive tr)

end GenLimit.Gold.Effective
