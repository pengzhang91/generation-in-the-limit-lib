import GenLimit.Paper18_SafeLanguageGeneration.DiffEmpty
import Mathlib.Computability.PartrecCode

/-!
# Machine-code representation for Safe Generation Theorem 6.1

The paper states `DIFF-EMPTY` for pairs of infinite decidable languages but
does not specify how such pairs are supplied as finite machine inputs.  This
module instantiates the representation boundary isolated in `DiffEmpty.lean`.

A language is represented by a `Nat.Partrec.Code` whose total Boolean output
decides membership, and a problem instance is a pair of such codes.  Validity
is a promise: both codes are total Boolean deciders and both represented
languages are infinite.  Mathlib's `Code.curry` (the `S_n^m` theorem) compiles
each program code from the existing hard subclass to an actual pair of
language-decider codes.  Consequently no computable predicate can decide
difference emptiness on every valid pair.
-/

namespace GenLimit.SafeGeneration.DiffEmpty.MachineEncoding

open Encodable Denumerable
open Nat.Partrec

/-- A concrete finite input representation for two language deciders. -/
abbrev LanguagePairCode := Code × Code

/-- The language accepted by a partial-recursive code.  Valid language codes
below are required to terminate with a Boolean value on every input. -/
def codedLanguage (code : Code) : Set ℕ :=
  {n | Code.eval code n = Part.some 1}

/-- Operational validity of one language code: it terminates everywhere and
returns the encoding of a Boolean value. -/
def TotalBooleanDecider (code : Code) : Prop :=
  ∀ n, ∃ b : Bool, Code.eval code n = Part.some (encode b)

/-- Promise domain for the paper's inputs: two total Boolean deciders whose
accepted languages are both infinite. -/
def IsValidLanguagePair (pair : LanguagePairCode) : Prop :=
  TotalBooleanDecider pair.1 ∧
    TotalBooleanDecider pair.2 ∧
    (codedLanguage pair.1).Infinite ∧
    (codedLanguage pair.2).Infinite

/-- Difference emptiness for the concrete pair-of-program-codes
representation. -/
def CodedDiffEmpty (pair : LanguagePairCode) : Prop :=
  codedLanguage pair.1 \ codedLanguage pair.2 = ∅

/-! ## Adequacy of the representation -/

/-- Every computable predicate on `ℕ` is represented by a valid total Boolean
language-decider code.  This records that `codedLanguage` covers all recursive
languages, rather than merely the hard instances used below. -/
theorem computablePred_has_totalBooleanDeciderCode
    (p : ℕ → Prop) (hp : ComputablePred p) :
    ∃ code : Code,
      TotalBooleanDecider code ∧ codedLanguage code = {n | p n} := by
  classical
  letI : DecidablePred p := hp.choose
  have hdecide : Computable (fun n => decide (p n)) :=
    hp.choose_spec
  have houtput : Computable (fun n => encode (decide (p n))) :=
    Computable.encode.comp hdecide
  obtain ⟨code, hcode⟩ := Code.exists_code.mp houtput.partrec
  refine ⟨code, ?_, ?_⟩
  · intro n
    refine ⟨decide (p n), ?_⟩
    simpa using congrFun hcode n
  · ext n
    change Code.eval code n = Part.some 1 ↔ p n
    have heval :
        Code.eval code n = Part.some (encode (decide (p n))) := by
      simpa using congrFun hcode n
    rw [heval]
    by_cases h : p n <;> simp [h]

/-! ## A uniform code for the hard right-language deciders -/

/-- The total characteristic function of the existing hard right-language
family, with the program parameter and member packed into one natural. -/
def universalRightDecision (input : ℕ) : ℕ :=
  if input.unpair.2 % 2 = 0 ∨
      boundedHalts (ofNat Code input.unpair.1) (input.unpair.2 / 2) = false then
    1
  else
    0

theorem universalRightDecision_primrec :
    Primrec universalRightDecision := by
  have harguments :
      Primrec (fun input : ℕ =>
        (ofNat Code input.unpair.1, input.unpair.2)) :=
    ((Primrec.ofNat Code).comp
      (Primrec.fst.comp Primrec.unpair)).pair
        (Primrec.snd.comp Primrec.unpair)
  have hpredicate :
      PrimrecPred (fun input : ℕ =>
        input.unpair.2 % 2 = 0 ∨
          boundedHalts (ofNat Code input.unpair.1)
            (input.unpair.2 / 2) = false) :=
    (rightLanguage_uniform_primrec.comp harguments).of_eq (by
      intro input
      simp [rightLanguage])
  exact Primrec.ite hpredicate (Primrec.const 1) (Primrec.const 0)

theorem universalRightDecision_partrec :
    Nat.Partrec (fun input => Part.some (universalRightDecision input)) := by
  exact Nat.Partrec.of_primrec
    (Primrec.nat_iff.mp universalRightDecision_primrec)

/-- One fixed universal code for `universalRightDecision`. -/
noncomputable def universalRightCode : Code :=
  Classical.choose
    (Code.exists_code.mp universalRightDecision_partrec)

theorem eval_universalRightCode (input : ℕ) :
    Code.eval universalRightCode input =
      Part.some (universalRightDecision input) := by
  exact congrFun
    (Classical.choose_spec
      (Code.exists_code.mp universalRightDecision_partrec)) input

/-- Compile the parameter `c` into a total code deciding `rightLanguage c`.
The compiler itself is primitive recursive by `Code.primrec₂_curry`. -/
noncomputable def rightDeciderCode (c : Code) : Code :=
  Code.curry universalRightCode (encode c)

theorem rightDeciderCode_primrec :
    Primrec rightDeciderCode := by
  exact Code.primrec₂_curry.comp
    (Primrec.const universalRightCode) Primrec.encode

theorem rightDeciderCode_computable :
    Computable rightDeciderCode :=
  rightDeciderCode_primrec.to_comp

theorem eval_rightDeciderCode (c : Code) (n : ℕ) :
    Code.eval (rightDeciderCode c) n =
      Part.some (universalRightDecision (Nat.pair (encode c) n)) := by
  rw [rightDeciderCode, Code.eval_curry, eval_universalRightCode]

/-! ## Correctness and validity of the compiled pair -/

@[simp] theorem codedLanguage_const_one :
    codedLanguage (Code.const 1) = Set.univ := by
  ext n
  simp [codedLanguage]

theorem codedLanguage_rightDeciderCode (c : Code) :
    codedLanguage (rightDeciderCode c) = rightLanguage c := by
  ext n
  simp only [codedLanguage, Set.mem_setOf_eq, rightLanguage]
  rw [eval_rightDeciderCode]
  by_cases heven : n % 2 = 0 <;>
    cases hhalts : boundedHalts c (n / 2) <;>
      simp [universalRightDecision, heven, hhalts]

theorem const_one_totalBooleanDecider :
    TotalBooleanDecider (Code.const 1) := by
  intro n
  exact ⟨true, by simp⟩

theorem rightDeciderCode_totalBooleanDecider (c : Code) :
    TotalBooleanDecider (rightDeciderCode c) := by
  intro n
  by_cases hmem :
      n % 2 = 0 ∨ boundedHalts c (n / 2) = false
  · refine ⟨true, ?_⟩
    rw [eval_rightDeciderCode]
    simp [universalRightDecision, hmem]
  · refine ⟨false, ?_⟩
    rw [eval_rightDeciderCode]
    simp [universalRightDecision, hmem]

/-- The computable embedding of a halting-problem code into a concrete pair
of language-decider codes. -/
noncomputable def hardPairCode (c : Code) : LanguagePairCode :=
  (Code.const 1, rightDeciderCode c)

theorem hardPairCode_primrec : Primrec hardPairCode := by
  exact (Primrec.const (Code.const 1)).pair rightDeciderCode_primrec

theorem hardPairCode_computable : Computable hardPairCode :=
  hardPairCode_primrec.to_comp

theorem hardPairCode_valid (c : Code) :
    IsValidLanguagePair (hardPairCode c) := by
  refine
    ⟨const_one_totalBooleanDecider,
      rightDeciderCode_totalBooleanDecider c, ?_, ?_⟩
  · simpa [hardPairCode, leftLanguage] using leftLanguage_infinite
  · simpa [hardPairCode, codedLanguage_rightDeciderCode] using
      rightLanguage_infinite c

theorem hardPairCode_diffEmpty_iff (c : Code) :
    CodedDiffEmpty (hardPairCode c) ↔ DiffEmptyInstance c := by
  simp [CodedDiffEmpty, hardPairCode, DiffEmptyInstance,
    codedLanguage_rightDeciderCode, leftLanguage]

/-! ## Concrete machine-input form of Theorem 6.1 -/

/-- Theorem 6.1 for the conventional representation by pairs of total
Boolean partial-recursive codes.  Validity is necessarily a promise: an
arbitrary program code need not halt, return a Boolean value, or accept an
infinite language. -/
theorem theorem_6_1_machine_codes :
    ¬∃ P : LanguagePairCode → Prop,
      ComputablePred P ∧
        ∀ pair, IsValidLanguagePair pair →
          (P pair ↔ CodedDiffEmpty pair) := by
  simpa [CodedDiffEmpty] using
    no_computable_promise_decider_of_hard_embedding
      IsValidLanguagePair
      (fun pair : LanguagePairCode => codedLanguage pair.1)
      (fun pair : LanguagePairCode => codedLanguage pair.2)
      hardPairCode
      hardPairCode_computable
      hardPairCode_valid
      hardPairCode_diffEmpty_iff

end GenLimit.SafeGeneration.DiffEmpty.MachineEncoding
