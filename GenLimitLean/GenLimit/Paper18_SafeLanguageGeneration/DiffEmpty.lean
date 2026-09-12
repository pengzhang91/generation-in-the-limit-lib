import GenLimit.Paper18_SafeLanguageGeneration.Definitions
import Mathlib.Computability.Halting

/-!
# An encoded hard subclass for Safe Generation Theorem 6.1

Theorem 6.1 of Anastasopoulos--Ateniese--Kornaropoulos asserts that deciding
emptiness of the difference of two infinite decidable languages is
undecidable.  The source does not specify how a pair of arbitrary sets is
encoded as input to a Turing machine.  This module therefore states the
machine-level result on an explicit encoded hard subclass.

An input is a Mathlib partial-recursive program code `c`.  It uniformly
determines two decidable subsets of `ℕ`: the left language is `Set.univ`,
while the right language contains every even number and contains `2k + 1`
exactly while bounded evaluation has not witnessed that `c` halts on input
`0` by fuel `k`.  Both languages are infinite for every code, their
membership relation is uniformly primitive recursive, and their difference
is empty exactly when `c` does not halt.  Consequently even this restricted
`DIFF-EMPTY` predicate is not computable.

This module deliberately does **not** derive the printed Corollary 6.1.
The paper's own reduction distinguishes an empty difference from a singleton
difference, whereas its Definition 2 requires eventual bottom output in both
finite cases.  Moreover, eventual convergence alone supplies no computable
stabilization bound.  Thus the claimed safe-generation corollary needs a
different statement and reduction.
-/

namespace GenLimit.SafeGeneration.DiffEmpty

open Nat.Partrec

/-- Bounded evidence that program `c` halts on input `0`. -/
def boundedHalts (c : Code) (fuel : ℕ) : Bool :=
  (Code.evaln fuel c 0).isSome

/-- The left language in the encoded reduction. -/
def leftLanguage : Set ℕ := Set.univ

/-- The right language contains every even number.  An odd number `2k + 1`
is included exactly while the bounded evaluator has not halted by fuel `k`.
Thus this language is infinite for every program code. -/
def rightLanguage (c : Code) : Set ℕ :=
  {n | n % 2 = 0 ∨ ¬(boundedHalts c (n / 2) : Prop)}

/-- The restricted `DIFF-EMPTY` instance associated with a program code. -/
def DiffEmptyInstance (c : Code) : Prop :=
  leftLanguage \ rightLanguage c = ∅

/-- Bounded halting evidence is primitive recursive uniformly in the program
code and fuel. -/
theorem boundedHalts_uniform_primrec :
    Primrec (fun p : Code × ℕ => boundedHalts p.1 p.2) := by
  unfold boundedHalts
  exact Primrec.option_isSome.comp
    (Code.primrec_evaln.comp
      (((Primrec.snd (α := Code) (β := ℕ)).pair
          (Primrec.fst (α := Code) (β := ℕ))).pair
        (Primrec.const 0)))

/-- Computable form of `boundedHalts_uniform_primrec`. -/
theorem boundedHalts_uniform_computable :
    Computable (fun p : Code × ℕ => boundedHalts p.1 p.2) :=
  boundedHalts_uniform_primrec.to_comp

/-- Membership in the right language is primitive recursive uniformly in
the program code and candidate member. -/
theorem rightLanguage_uniform_primrec :
    PrimrecPred (fun p : Code × ℕ => p.2 ∈ rightLanguage p.1) := by
  have hmod :
      Primrec (fun p : Code × ℕ => p.2 % 2) :=
    Primrec.nat_mod.comp
      (Primrec.snd (α := Code) (β := ℕ))
      (Primrec.const 2)
  have heven :
      PrimrecPred (fun p : Code × ℕ => p.2 % 2 = 0) :=
    (Primrec.eq.comp
      hmod
      (Primrec.const 0))
  have hfuel :
      Primrec (fun p : Code × ℕ => p.2 / 2) :=
    Primrec.nat_div.comp
      (Primrec.snd (α := Code) (β := ℕ))
      (Primrec.const 2)
  have hhalts :
      PrimrecPred (fun p : Code × ℕ =>
        (boundedHalts p.1 (p.2 / 2) : Prop)) := by
    refine ⟨inferInstance, ?_⟩
    simpa using (boundedHalts_uniform_primrec.comp
      ((Primrec.fst (α := Code) (β := ℕ)).pair hfuel))
  exact (heven.or hhalts.not).of_eq (by
    intro p
    simp [rightLanguage])

/-- Computable form of `rightLanguage_uniform_primrec`. -/
theorem rightLanguage_uniform_computable :
    ComputablePred (fun p : Code × ℕ => p.2 ∈ rightLanguage p.1) :=
  rightLanguage_uniform_primrec.computablePred

/-- Every individual right language has decidable computable membership. -/
theorem rightLanguage_computable (c : Code) :
    ComputablePred (fun n => n ∈ rightLanguage c) := by
  exact (rightLanguage_uniform_primrec.comp
    ((Primrec.const c).pair Primrec.id)).computablePred

/-- The left language is infinite. -/
theorem leftLanguage_infinite : leftLanguage.Infinite := by
  simpa [leftLanguage] using
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)

/-- Every right language is infinite because it contains all even numbers. -/
theorem rightLanguage_infinite (c : Code) :
    (rightLanguage c).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab
    exact Nat.mul_left_cancel (by omega) hab
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨k, rfl⟩
  simp [rightLanguage]

/-- A program halts exactly when some bounded evaluation witnesses it. -/
theorem eval_dom_iff_exists_boundedHalts (c : Code) :
    (Code.eval c 0).Dom ↔ ∃ k, boundedHalts c k = true := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
    refine ⟨k, ?_⟩
    simpa [boundedHalts, Option.isSome_iff_exists] using
      (show (Code.evaln k c 0).isSome from
        Option.isSome_iff_exists.mpr ⟨x, hk⟩)
  · rintro ⟨k, hk⟩
    have hkSome : (Code.evaln k c 0).isSome := by
      simpa [boundedHalts] using hk
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hkSome
    exact Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound hx⟩

/-- The encoded set difference is empty exactly when the program does not
halt on input `0`. -/
theorem diffEmptyInstance_iff_not_dom (c : Code) :
    DiffEmptyInstance c ↔ ¬(Code.eval c 0).Dom := by
  constructor
  · intro hempty hdom
    obtain ⟨k, hk⟩ := (eval_dom_iff_exists_boundedHalts c).mp hdom
    have hmemLeft : 2 * k + 1 ∈ leftLanguage := by
      simp [leftLanguage]
    have hmemRight : 2 * k + 1 ∈ rightLanguage c := by
      have hsub : leftLanguage ⊆ rightLanguage c := by
        exact Set.diff_eq_empty.mp hempty
      exact hsub hmemLeft
    have hodd : (2 * k + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * k + 1) / 2 = k := by omega
    simp only [rightLanguage, Set.mem_setOf_eq, hodd, false_or, hdiv] at hmemRight
    exact hmemRight (by simpa [boundedHalts] using hk)
  · intro hnot
    apply Set.diff_eq_empty.mpr
    intro n _
    simp only [rightLanguage, Set.mem_setOf_eq]
    by_cases heven : n % 2 = 0
    · exact Or.inl heven
    · refine Or.inr ?_
      intro hbounded
      apply hnot
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hbounded
      exact Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound hx⟩

/-- Machine-level Theorem 6.1 on the explicit encoded hard subclass above.
No claim is made about an unspecified encoding of arbitrary set pairs. -/
theorem theorem_6_1_restricted :
    ¬ComputablePred DiffEmptyInstance := by
  intro hdiff
  have hnonhalting :
      ComputablePred (fun c : Code => ¬(Code.eval c 0).Dom) :=
    hdiff.of_eq diffEmptyInstance_iff_not_dom
  have hhalting :
      ComputablePred (fun c : Code => (Code.eval c 0).Dom) :=
    hnonhalting.not.of_eq (by simp)
  exact ComputablePred.halting_problem 0 hhalting

/-- Any concrete representation of language pairs inherits Theorem 6.1 as
soon as it admits a computable embedding of the explicit hard subclass.

This isolates the exact interface missing from the source's unrestricted
machine-input formulation: a representation type and a computable compiler
whose encoded difference-emptiness predicate agrees with
`DiffEmptyInstance`. -/
theorem diffEmpty_not_computable_of_hard_embedding
    {Rep : Type*} [Primcodable Rep]
    (left right : Rep → Set ℕ)
    (encode : Code → Rep)
    (hencode : Computable encode)
    (hcorrect :
      ∀ c,
        left (encode c) \ right (encode c) = ∅ ↔
          DiffEmptyInstance c) :
    ¬ComputablePred (fun r => left r \ right r = ∅) := by
  intro hdec
  apply theorem_6_1_restricted
  have hencoded :
      ComputablePred
        (fun c => left (encode c) \ right (encode c) = ∅) := by
    letI : DecidablePred
        (fun r : Rep => left r \ right r = ∅) :=
      Classical.decPred _
    letI : DecidablePred
        (fun c : Code => left (encode c) \ right (encode c) = ∅) :=
      Classical.decPred _
    exact (hdec.decide.comp hencode).computablePred
  exact hencoded.of_eq hcorrect

/-- Promise-problem form of the representation transport theorem.  Even if
a decider need only be correct on a designated class of valid encoded
infinite decidable language pairs, a computable hard embedding rules it out.
-/
theorem no_computable_promise_decider_of_hard_embedding
    {Rep : Type*} [Primcodable Rep]
    (Valid : Rep → Prop)
    (left right : Rep → Set ℕ)
    (encode : Code → Rep)
    (hencode : Computable encode)
    (hvalid : ∀ c, Valid (encode c))
    (hcorrect :
      ∀ c,
        left (encode c) \ right (encode c) = ∅ ↔
          DiffEmptyInstance c) :
    ¬∃ P : Rep → Prop,
      ComputablePred P ∧
        ∀ r, Valid r →
          (P r ↔ left r \ right r = ∅) := by
  rintro ⟨P, hP, hPcorrect⟩
  apply theorem_6_1_restricted
  have hencoded : ComputablePred (fun c => P (encode c)) := by
    letI : DecidablePred P := Classical.decPred _
    letI : DecidablePred (fun c => P (encode c)) :=
      Classical.decPred _
    exact (hP.decide.comp hencode).computablePred
  exact hencoded.of_eq fun c =>
    (hPcorrect (encode c) (hvalid c)).trans (hcorrect c)

end GenLimit.SafeGeneration.DiffEmpty
