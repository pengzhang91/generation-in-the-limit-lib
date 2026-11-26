import GenLimit.Paper22_LanguageGenerationWithReplay.ProperMembershipLowerBound
import GenLimit.Support.ComputableLists

/-! Finite execution certificates for the proper membership-query lower bound. -/

namespace GenLimit.Replay.ProperDiagonal

open Support.AdaptiveMembershipDialogue
open Support.ComputableLists

variable {σ β : Type*} [Primcodable σ] [Primcodable β] [Inhabited β]

/-- Check each entry together with the exact prefix preceding it. -/
private def everyEntry (xs : List β) (p : List β → β → Bool) : Bool :=
  (List.range xs.length).all fun k => p (xs.take k) (xs[k]?.getD default)

omit [Primcodable β] in
private theorem everyEntry_spec {xs : List β} {p : List β → β → Bool} :
    everyEntry xs p = true ↔ ∀ k (hk : k < xs.length), p (xs.take k) xs[k] = true := by
  simp only [everyEntry, List.all_eq_true, List.mem_range]
  constructor <;> intro h k hk <;> simpa [List.getElem?_eq_getElem hk] using h k hk

private theorem take_comp {xs : σ → List β} {k : σ → ℕ}
    (hl : Computable xs) (hk : Computable k) : Computable (fun s => (xs s).take (k s)) := by
  have h := map (Primrec.list_range.to_comp.comp
      (Primrec.nat_min.to_comp.comp hk (Computable.list_length.comp hl)))
    (Computable.option_getD (Computable.list_getElem?.comp (hl.comp Computable.fst) Computable.snd)
      (Computable.const default)).to₂
  apply h.of_eq
  intro s
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    rw [List.getElem?_eq_getElem (by simp only [List.length_take] at hi'; exact hi'.trans_le (min_le_right ..))]
    rfl

private theorem everyEntry_comp {xs : σ → List β} {p : σ → List β × β → Bool}
    (hl : Computable xs) (hp : Computable₂ p) :
    Computable (fun s => everyEntry (xs s) fun prev x => p s (prev,x)) :=
  all (Primrec.list_range.to_comp.comp (Computable.list_length.comp hl))
    (hp.comp Computable.fst ((take_comp (hl.comp Computable.fst) Computable.snd).pair
      (Computable.option_getD (Computable.list_getElem?.comp (hl.comp Computable.fst) Computable.snd)
        (Computable.const default)))).to₂

abbrev QueryRule := ℕ → ℕ → Bool

def checkRound (A : ProperMembershipAlgorithm) (q : QueryRule)
    (history : List ProperMembershipRound) (r : ProperMembershipRound) : Bool :=
  everyEntry r.2.1 (fun prev qa =>
    decide (A (history, r.1, prev) = Sum.inl qa.1) && (qa.2 == q qa.1.1 qa.1.2)) &&
  decide (A (history,r.1,r.2.1) = Sum.inr r.2.2)

def checkRun (A : ProperMembershipAlgorithm) (q : QueryRule) (rs : List ProperMembershipRound) : Bool :=
  everyEntry rs (checkRound A q)

def rows (q : QueryRule) : LanguageFamily := fun i => {x | q i x = true}

private theorem answer_iff {q : QueryRule} {qa : AnsweredProperMembershipQuery} :
    qa.2 = q qa.1.1 qa.1.2 ↔ ProperMembershipAnswerCorrect (rows q) qa := by
  change _ ↔ (qa.2 = true ↔ q qa.1.1 qa.1.2 = true)
  cases qa.2 <;> cases q qa.1.1 qa.1.2 <;> simp

theorem checkRun_spec (A : ProperMembershipAlgorithm) (q : QueryRule) (rs : List ProperMembershipRound) :
    checkRun A q rs = true ↔ ProperMembershipExecutionValid A (rows q) (rs.map Prod.fst) rs := by
  simp only [checkRun, everyEntry_spec, checkRound, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  unfold ProperMembershipExecutionValid ExecutionValid RoundValid QueryTraceValid
  simp only [List.length_map, List.get_eq_getElem, List.getElem_map, true_and, answer_iff, eq_self]
  constructor
  · intro h k _ hk
    exact h k hk
  · intro h k hk
    exact h k hk hk

/-- The certificate checker is uniform in any computably supplied oracle table. -/
theorem checkRun_comp {A : ProperMembershipAlgorithm} (hA : Computable A)
    {q : σ → ProperMembershipQuery → Bool} (hq : Computable₂ q)
    {rs : σ → List ProperMembershipRound} (hr : Computable rs) :
    Computable (fun s => checkRun A (fun i x => q s (i,x)) (rs s)) := by
  apply everyEntry_comp (p := fun s z => checkRound A (fun i x => q s (i,x)) z.1 z.2) hr
  let D := σ × (List ProperMembershipRound × ProperMembershipRound)
  have hist : Computable (fun d : D => d.2.1) := Computable.fst.comp Computable.snd
  have rnd : Computable (fun d : D => d.2.2) := Computable.snd.comp Computable.snd
  have input := Computable.fst.comp rnd
  have trace := Computable.fst.comp (Computable.snd.comp rnd)
  have output := Computable.snd.comp (Computable.snd.comp rnd)
  have traceOK : Computable (fun d : D => everyEntry d.2.2.2.1
      fun prev (qa : AnsweredProperMembershipQuery) =>
        decide (A (d.2.1, d.2.2.1, prev) = Sum.inl qa.1) && (qa.2 == q d.1 qa.1)) := by
    apply everyEntry_comp (p := fun d z => decide (A (d.2.1,d.2.2.1,z.1) = Sum.inl z.2.1) &&
      (z.2.2 == q d.1 z.2.1)) trace
    let E := D × (List AnsweredProperMembershipQuery × AnsweredProperMembershipQuery)
    have prev : Computable (fun e : E => e.2.1) := Computable.fst.comp Computable.snd
    have qa : Computable (fun e : E => e.2.2) := Computable.snd.comp Computable.snd
    have action := hA.comp ((hist.comp Computable.fst).pair ((input.comp Computable.fst).pair prev))
    have ask : Computable (fun e : E => (Sum.inl e.2.2.1 : ProperMembershipAction)) := Computable.sumInl.comp (Computable.fst.comp qa)
    have ans := hq.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp qa)
    exact (Primrec.and.to_comp.comp (Primrec.eq.decide.to_comp.comp action ask)
      (Primrec.beq.to_comp.comp (Computable.snd.comp qa) ans)).to₂
  exact (Primrec.and.to_comp.comp traceOK (Primrec.eq.decide.to_comp.comp
    (hA.comp (hist.pair (input.pair trace))) (Computable.sumInr.comp output))).to₂

end GenLimit.Replay.ProperDiagonal
