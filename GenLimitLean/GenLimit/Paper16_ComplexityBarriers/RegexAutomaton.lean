import GenLimit.Paper16_ComplexityBarriers.FiniteAutomata
import Mathlib.Computability.RegularExpressions

/-! # A linear-state NFA for a regular expression

Partial derivatives share continuations. Each literal occurrence accounts
for at most one residual state, plus the original expression at the start. -/
namespace GenLimit.ComplexityBarriers.Automata
open RegularExpression
open scoped Classical
noncomputable section

def regexSize : RegularExpression α → ℕ
  | .zero | .epsilon | .char _ => 1
  | .plus r t | .comp r t => regexSize r + regexSize t + 1
  | .star r => regexSize r + 1

/-- Tokens in the paper's fully parenthesized grammar, including both delimiters
of a binary operation. Concatenation is written by juxtaposition. -/
def writtenSize : RegularExpression α → ℕ
  | .zero | .epsilon | .char _ => 1
  | .plus r t => writtenSize r + writtenSize t + 3
  | .comp r t => writtenSize r + writtenSize t + 2
  | .star r => writtenSize r + 1

theorem size_comparison (r : RegularExpression α) :
    regexSize r ≤ writtenSize r ∧ writtenSize r ≤ 3 * regexSize r := by
  induction r <;> simp only [regexSize,writtenSize] at * <;> omega

private def residuals : RegularExpression α → Finset (RegularExpression α)
  | .zero | .epsilon => ∅
  | .char _ => {1}
  | .plus r t => residuals r ∪ residuals t
  | .comp r t => (residuals r).image (· * t) ∪ residuals t
  | .star r => (residuals r).image (· * r.star)

private def stepRE : RegularExpression α → α → Finset (RegularExpression α)
  | .zero, _ | .epsilon, _ => ∅
  | .char b, a => if b = a then {1} else ∅
  | .plus r t, a => stepRE r a ∪ stepRE t a
  | .comp r t, a => (stepRE r a).image (· * t) ∪ (if r.matchEpsilon then stepRE t a else ∅)
  | .star r, a => (stepRE r a).image (· * r.star)

private theorem residual_card (r : RegularExpression α) : (residuals r).card ≤ regexSize r := by
  induction r with
  | zero | epsilon | char => simp [residuals,regexSize]
  | plus r t ir it => exact (Finset.card_union_le ..).trans (by change _ ≤ regexSize r + regexSize t + 1; omega)
  | comp r t ir it =>
    exact (Finset.card_union_le ..).trans ((Nat.add_le_add (Finset.card_image_le.trans ir) it).trans (Nat.le_succ _))
  | star r ir => exact Finset.card_image_le.trans (ir.trans (Nat.le_succ _))

private theorem step_subset (r : RegularExpression α) (a : α) : stepRE r a ⊆ residuals r := by
  induction r with
  | zero | epsilon => rfl
  | char b => by_cases h : b = a <;> simp [stepRE,residuals,h]
  | plus r t ir it => exact Finset.union_subset_union ir it
  | comp r t ir it =>
    apply Finset.union_subset_union (Finset.image_subset_image ir)
    split <;> first | exact it | exact Finset.empty_subset _
  | star r ir => exact Finset.image_subset_image ir

private theorem residual_closed (r : RegularExpression α) (a : α) :
    ∀ q ∈ residuals r, stepRE q a ⊆ residuals r := by
  induction r with
  | zero | epsilon => simp [residuals]
  | char b => simp [residuals,stepRE]
  | plus r t ir it =>
    rintro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact (ir q h).trans Finset.subset_union_left
    · exact (it q h).trans Finset.subset_union_right
  | comp r t ir it =>
    rintro q hq
    rcases Finset.mem_union.mp hq with h | h
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
      apply Finset.union_subset_union (Finset.image_subset_image (ir p hp))
      split <;> first | exact step_subset t a | exact Finset.empty_subset _
    · exact (it q h).trans Finset.subset_union_right
  | star r ir =>
    rintro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    apply Finset.union_subset (Finset.image_subset_image (ir p hp))
    split <;> first | exact step_subset (.star r) a | exact Finset.empty_subset _

private def langs (S : Finset (RegularExpression α)) : _root_.Language α := {w | ∃ r ∈ S, w ∈ r.matches'}

private theorem langs_union (S T : Finset (RegularExpression α)) : langs (S ∪ T) = langs S + langs T := by
  ext w; change (∃ r ∈ S ∪ T, w ∈ r.matches') ↔ _ ∨ _
  simp only [Finset.mem_union,langs,Set.mem_setOf_eq]; aesop

private theorem langs_mul (S : Finset (RegularExpression α)) (t) :
    langs (S.image (· * t)) = langs S * t.matches' := by
  ext w
  constructor
  · rintro ⟨q,hq,hw⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨u,hu,v,hv,rfl⟩ := Language.mem_mul.mp hw
    exact Language.mem_mul.mpr ⟨u,⟨p,hp,hu⟩,v,hv,rfl⟩
  · intro hw
    obtain ⟨u,⟨p,hp,hu⟩,v,hv,rfl⟩ := Language.mem_mul.mp hw
    exact ⟨p*t,Finset.mem_image_of_mem _ hp,Language.mem_mul.mpr ⟨u,hu,v,hv,rfl⟩⟩

private theorem langs_empty : langs (∅ : Finset (RegularExpression α)) = 0 := by
  ext w
  change (∃ r ∈ (∅ : Finset (RegularExpression α)), w ∈ r.matches') ↔ False
  simp
private theorem langs_one : langs ({1} : Finset (RegularExpression α)) = 1 := by
  ext w
  change (∃ r ∈ ({1} : Finset (RegularExpression α)), w ∈ r.matches') ↔ w ∈ (1 : _root_.Language α)
  simp only [Finset.mem_singleton,exists_eq_left]
  rfl

private theorem step_language (r : RegularExpression α) (a : α) :
    langs (stepRE r a) = (r.deriv a).matches' := by
  induction r with
  | zero | epsilon => exact langs_empty
  | char b =>
    by_cases h : b = a <;> simp [stepRE,RegularExpression.deriv,h,langs_empty,langs_one]
  | plus r t ir it => simpa only [stepRE,langs_union,ir,it] using (RegularExpression.matches'_add (r.deriv a) (t.deriv a)).symm
  | comp r t ir it =>
    change langs ((stepRE r a).image (· * t) ∪ _) = _
    rw [langs_union,langs_mul,ir]
    cases h : r.matchEpsilon <;> simp [RegularExpression.deriv, h,langs_empty,it,RegularExpression.matches'_mul]
  | star r ir => rw [stepRE,langs_mul,ir]; rfl

private theorem derivative_spec (r : RegularExpression α) (a : α) (w : List α) :
    a::w ∈ r.matches' ↔ ∃ q ∈ stepRE r a, w ∈ q.matches' := by
  change _ ↔ w ∈ langs (stepRE r a)
  rw [step_language,←RegularExpression.rmatch_iff_matches',←RegularExpression.rmatch_iff_matches']; rfl

private def fromState (M : NFA α σ) (q : σ) (w : List α) :=
  ∃ t ∈ M.accept, t ∈ M.evalFrom {q} w

private theorem fromState_cons (M : NFA α σ) (q : σ) (a : α) (w : List α) :
    fromState M q (a::w) ↔ ∃ r ∈ M.step q a, fromState M r w := by
  simp only [fromState,NFA.evalFrom_cons,NFA.stepSet_singleton,NFA.mem_evalFrom_iff_exists (S := M.step q a)]; aesop

theorem nfa_of_regex (r : RegularExpression α) :
    NFAAtMost (regexSize r + 1) r.matches' := by
  let S := insert r (residuals r)
  let e := S.equivFin
  let R := fun i ↦ (e.symm i).val
  let start := e ⟨r,Finset.mem_insert_self ..⟩
  let M : NFA α (Fin S.card) := ⟨fun i a ↦ {j | R j ∈ stepRE (R i) a}, {start}, {j | [] ∈ (R j).matches'}⟩
  have closed (i : Fin S.card) (a : α) : stepRE (R i) a ⊆ S := by
    have hi : R i ∈ S := (e.symm i).property
    rcases Finset.mem_insert.mp hi with hh | hh
    · rw [hh]; exact (step_subset r a).trans (Finset.subset_insert ..)
    · exact (residual_closed r a _ hh).trans (Finset.subset_insert ..)
  have run (w : List α) : ∀ i, fromState M i w ↔ w ∈ (R i).matches' := by
    induction w with
    | nil => intro i; simp [fromState,M]
    | cons a w ih =>
      intro i
      rw [fromState_cons,derivative_spec]
      constructor
      · rintro ⟨j,hj,hw⟩; exact ⟨R j,hj,(ih j).mp hw⟩
      · rintro ⟨q,hq,hw⟩
        let j := e ⟨q,closed i a hq⟩
        have he : R j = q := by simp [R,j]
        exact ⟨j,show R j ∈ stepRE (R i) a from he ▸ hq,(ih j).mpr (he ▸ hw)⟩
  refine ⟨S.card,(Finset.card_insert_le ..).trans (Nat.succ_le_succ (residual_card r)),M,?_⟩
  ext w
  change fromState M start w ↔ _
  simpa [R,start] using run w start

theorem regex_upper [Fintype α] (ha : 2 ≤ Fintype.card α) (F : Finset (Set (List α))) (s : ℕ)
    (hF : ∀ L ∈ F, ∃ r : RegularExpression α, r.matches' = L ∧ regexSize r ≤ s-1) :
    MGeneratable (F : Set (Set (List α))) ((Fintype.card α)^(s^F.card)) := by
  apply regular_upper ha F s
  intro L hL
  obtain ⟨r,rfl,hr⟩ := hF L hL
  obtain ⟨q,hq,M,hM⟩ := nfa_of_regex r
  have hpos : 0 < regexSize r := by cases r <;> simp [regexSize]
  exact ⟨q,by omega,M,hM⟩

end
end GenLimit.ComplexityBarriers.Automata
