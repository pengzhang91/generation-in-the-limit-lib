import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.ExhaustiveCharacterization
import GenLimit.Core.ClassGeneration
import Mathlib.Computability.DFA
import Mathlib.Data.List.FinRange

/-!
# Charikar--Pabbaraju Theorem 3 over a literal finite alphabet

The proof of overview Theorem 3 is written in the paper on the integer
universe and notes parenthetically that its arithmetic rays are regular after
encoding the integers over a finite alphabet.  This file closes that
representation boundary.

We use the two-symbol alphabet `Bool` and a signed-unary total decoding:
the empty word and words beginning in `false` represent nonnegative values;
a word `true :: tail` represents `-(tail.length+1)`.  The pullback of the
integer ray starting at `-i` is therefore

* every empty or `false`-headed word, and
* a `true`-headed word exactly when its tail has length less than `i`.

Each such language is recognized by the explicit finite DFA below.  These
regular ray languages have exactly the finite-tell-tale obstruction used in
the paper, so Proposition 6.1 yields the literal finite-alphabet form of
Theorem 3.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## The signed-unary ray and its DFA -/

/-- Pullback of the integer ray `{-i,-i+1,...}` under signed-unary decoding. -/
def signedUnaryRay (i : Nat) : Set (List Bool) :=
  {w | match w with
    | [] => True
    | false :: _ => True
    | true :: tail => tail.length < i}

@[simp] theorem nil_mem_signedUnaryRay (i : Nat) :
    [] ∈ signedUnaryRay i := by
  simp [signedUnaryRay]

@[simp] theorem false_cons_mem_signedUnaryRay
    (i : Nat) (tail : List Bool) :
    false :: tail ∈ signedUnaryRay i := by
  simp [signedUnaryRay]

@[simp] theorem true_cons_mem_signedUnaryRay_iff
    (i : Nat) (tail : List Bool) :
    true :: tail ∈ signedUnaryRay i ↔ tail.length < i := by
  rfl

/-- States of the finite automaton for `signedUnaryRay i`.  A negative state
records the number of symbols read after the initial `true`. -/
inductive SignedUnaryRayState (i : Nat)
  | start
  | positive
  | negative (seen : Fin i)
  | reject
deriving DecidableEq, Fintype

namespace SignedUnaryRayState

/-- One transition of the signed-unary ray automaton. -/
def step (i : Nat) : SignedUnaryRayState i → Bool → SignedUnaryRayState i
  | .start, false => .positive
  | .start, true => if h : 0 < i then .negative ⟨0, h⟩ else .reject
  | .positive, _ => .positive
  | .negative k, _ =>
      if h : k.val + 1 < i then .negative ⟨k.val + 1, h⟩ else .reject
  | .reject, _ => .reject

end SignedUnaryRayState

/-- Explicit finite DFA recognizing the ray language. -/
def signedUnaryRayDFA (i : Nat) : DFA Bool (SignedUnaryRayState i) where
  step := SignedUnaryRayState.step i
  start := .start
  accept := {q | q ≠ .reject}

private theorem evalFrom_cons
    (i : Nat) (q : SignedUnaryRayState i) (a : Bool) (w : List Bool) :
    (signedUnaryRayDFA i).evalFrom q (a :: w) =
      (signedUnaryRayDFA i).evalFrom
        ((signedUnaryRayDFA i).step q a) w := by
  rfl

@[simp] theorem signedUnaryRayDFA_evalFrom_positive
    (i : Nat) (w : List Bool) :
    (signedUnaryRayDFA i).evalFrom .positive w = .positive := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [evalFrom_cons]
      simpa [signedUnaryRayDFA, SignedUnaryRayState.step] using ih

@[simp] theorem signedUnaryRayDFA_evalFrom_reject
    (i : Nat) (w : List Bool) :
    (signedUnaryRayDFA i).evalFrom .reject w = .reject := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [evalFrom_cons]
      simpa [signedUnaryRayDFA, SignedUnaryRayState.step] using ih

/-- Evaluation from a negative state counts the remaining input until it
reaches the rejecting sink. -/
theorem signedUnaryRayDFA_evalFrom_negative
    (i : Nat) (k : Fin i) (w : List Bool) :
    (signedUnaryRayDFA i).evalFrom (.negative k) w =
      if h : k.val + w.length < i then
        .negative ⟨k.val + w.length, h⟩
      else .reject := by
  induction w generalizing k with
  | nil =>
      simp only [List.length_nil, Nat.add_zero]
      rw [dif_pos k.isLt]
      congr
  | cons a w ih =>
      rw [evalFrom_cons]
      change (signedUnaryRayDFA i).evalFrom
          (SignedUnaryRayState.step i (.negative k) a) w = _
      simp only [SignedUnaryRayState.step]
      by_cases hstep : k.val + 1 < i
      · rw [dif_pos hstep, ih]
        by_cases htotal : k.val + (a :: w).length < i
        · rw [dif_pos htotal]
          have hinner : (k.val + 1) + w.length < i := by
            simpa only [List.length_cons, Nat.add_assoc,
              Nat.add_comm 1 w.length] using htotal
          rw [dif_pos hinner]
          congr 1
          apply Fin.ext
          simp only [List.length_cons]
          omega
        · rw [dif_neg htotal]
          have hinner : ¬ (k.val + 1) + w.length < i := by
            intro h
            apply htotal
            simpa only [List.length_cons, Nat.add_assoc,
              Nat.add_comm 1 w.length] using h
          rw [dif_neg hinner]
      · rw [dif_neg hstep, signedUnaryRayDFA_evalFrom_reject]
        have htotal : ¬ k.val + (a :: w).length < i := by
          simp only [List.length_cons]
          omega
        rw [dif_neg htotal]

theorem signedUnaryRayDFA_accepts (i : Nat) :
    (signedUnaryRayDFA i).accepts = signedUnaryRay i := by
  ext w
  rw [DFA.mem_accepts]
  change (signedUnaryRayDFA i).evalFrom .start w ≠ .reject ↔
    w ∈ signedUnaryRay i
  cases w with
  | nil => simp [signedUnaryRay]
  | cons a tail =>
      rw [evalFrom_cons]
      change (signedUnaryRayDFA i).evalFrom
          (SignedUnaryRayState.step i .start a) tail ≠ .reject ↔ _
      cases a with
      | false =>
          rw [show SignedUnaryRayState.step i .start false = .positive by
            rfl]
          simp [signedUnaryRay]
      | true =>
          by_cases hi : 0 < i
          · rw [show SignedUnaryRayState.step i .start true =
                .negative ⟨0, hi⟩ by
              simp [SignedUnaryRayState.step, hi]]
            rw [signedUnaryRayDFA_evalFrom_negative]
            simp only [Nat.zero_add]
            by_cases hlen : tail.length < i
            · rw [dif_pos hlen]
              simp [signedUnaryRay, hlen]
            · rw [dif_neg hlen]
              simp [signedUnaryRay, hlen]
          · rw [show SignedUnaryRayState.step i .start true = .reject by
              simp [SignedUnaryRayState.step, hi]]
            have hi0 : i = 0 := Nat.eq_zero_of_not_pos hi
            subst i
            simp [signedUnaryRay]

/-- Every ray in the encoding is a regular language over the finite alphabet
`Bool`. -/
theorem signedUnaryRay_isRegular (i : Nat) :
    (_root_.Language.IsRegular (signedUnaryRay i)) := by
  exact ⟨SignedUnaryRayState i, inferInstance,
    signedUnaryRayDFA i, signedUnaryRayDFA_accepts i⟩

/-! ## The regular lower-bound collection -/

/-- The encoded collection consists of the full language and all signed-unary
rays. -/
def signedUnaryRayClass : Generic.LanguageClass (List Bool) :=
  {K | K = Set.univ ∨ ∃ i : Nat, K = signedUnaryRay i}

theorem signedUnaryRayClass_countable : signedUnaryRayClass.Countable := by
  let f : Option Nat → Set (List Bool)
    | none => Set.univ
    | some i => signedUnaryRay i
  have hEq : signedUnaryRayClass = Set.range f := by
    ext K
    constructor
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some i, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i => exact Or.inr ⟨i, rfl⟩
  rw [hEq]
  exact Set.countable_range f

theorem signedUnaryRayClass_regular
    {K : Set (List Bool)} (hK : K ∈ signedUnaryRayClass) :
    _root_.Language.IsRegular K := by
  rcases hK with rfl | ⟨i, rfl⟩
  · let M : DFA Bool (Fin 1) :=
      { step := fun q _ => q
        start := 0
        accept := Set.univ }
    refine ⟨Fin 1, inferInstance, M, ?_⟩
    ext w
    simp [M, DFA.accepts, DFA.acceptsFrom]
  · exact signedUnaryRay_isRegular i

theorem signedUnaryRay_infinite (i : Nat) :
    (signedUnaryRay i).Infinite := by
  let f : Nat → List Bool := fun n => false :: List.replicate n false
  have hf : Function.Injective f := by
    intro m n h
    have := congrArg List.length h
    simpa [f] using this
  have hrange : Set.range f ⊆ signedUnaryRay i := by
    rintro w ⟨n, rfl⟩
    simp [f]
  exact (Set.infinite_range_of_injective hf).mono hrange

theorem signedUnaryRayClass_languages_infinite
    (K : Set (List Bool)) (hK : K ∈ signedUnaryRayClass) : K.Infinite := by
  rcases hK with rfl | ⟨i, rfl⟩
  · exact Set.infinite_univ
  · exact signedUnaryRay_infinite i

private def wordLengthBound (T : Finset (List Bool)) : Nat :=
  T.sup List.length + 1

private theorem word_length_lt_bound
    (T : Finset (List Bool)) {w : List Bool} (hw : w ∈ T) :
    w.length < wordLengthBound T := by
  unfold wordLengthBound
  exact Nat.lt_succ_of_le (Finset.le_sup (f := List.length) hw)

theorem mem_signedUnaryRay_of_length_lt
    {i : Nat} {w : List Bool} (h : w.length < i) :
    w ∈ signedUnaryRay i := by
  cases w with
  | nil => simp
  | cons a tail =>
      cases a <;> simp only [false_cons_mem_signedUnaryRay,
        true_cons_mem_signedUnaryRay_iff]
      simp only [List.length_cons] at h
      omega

theorem signedUnaryRay_complement_infinite (i : Nat) :
    ((Set.univ : Set (List Bool)) \ signedUnaryRay i).Infinite := by
  let f : Nat → List Bool :=
    fun n => true :: List.replicate (i + n) false
  have hf : Function.Injective f := by
    intro m n h
    have := congrArg List.length h
    simpa [f] using this
  have hrange : Set.range f ⊆
      (Set.univ : Set (List Bool)) \ signedUnaryRay i := by
    rintro w ⟨n, rfl⟩
    constructor
    · trivial
    · simp [f]
  exact (Set.infinite_range_of_injective hf).mono hrange

/-- Every finite subset of the full language is contained in a proper regular
ray which omits infinitely many words.  This is equation (8) for the literal
finite-alphabet encoding. -/
theorem signedUnaryRayClass_no_finite_weak_telltale
    (T : Finset (List Bool)) :
    ∃ L' ∈ signedUnaryRayClass,
      (T : Set (List Bool)) ⊆ L' ∧
        L' ⊂ (Set.univ : Set (List Bool)) ∧
        ((Set.univ : Set (List Bool)) \ L').Infinite := by
  let i := wordLengthBound T
  refine ⟨signedUnaryRay i, Or.inr ⟨i, rfl⟩, ?_, ?_, ?_⟩
  · intro w hw
    exact mem_signedUnaryRay_of_length_lt (word_length_lt_bound T hw)
  · apply Set.ssubset_univ_iff.mpr
    exact (Set.ne_univ_iff_exists_notMem _).mpr
      ⟨true :: List.replicate i false, by simp [i]⟩
  · exact signedUnaryRay_complement_infinite i

theorem signedUnaryRayClass_not_weakAngluinExistence :
    ¬ WeakAngluinExistence signedUnaryRayClass := by
  intro hWeak
  obtain ⟨T, -, hTell⟩ := hWeak Set.univ (Or.inl rfl)
  obtain ⟨L', hL', hTL', hproper, hinfinite⟩ :=
    signedUnaryRayClass_no_finite_weak_telltale T
  exact hinfinite (hTell L' hL' hTL' hproper)

theorem signedUnaryRayClass_not_exhaustivelyGeneratable :
    ¬ ExhaustivelyGeneratable signedUnaryRayClass := by
  intro hGenerate
  exact signedUnaryRayClass_not_weakAngluinExistence
    (proposition6_1_exhaustive_necessary signedUnaryRayClass
      signedUnaryRayClass_languages_infinite hGenerate)

/-- Overview Theorem 3 with Section 2's standing infinitude assumption made
explicit in the witness. -/
theorem theorem3_finiteAlphabet_regular_exhaustive_generation_lower_bound_with_infinite_languages :
    ∃ C : Generic.LanguageClass (List Bool),
      C.Countable ∧
      Generic.UUS C ∧
      (∀ K, K ∈ C → _root_.Language.IsRegular K) ∧
      ¬ ExhaustivelyGeneratable C :=
  ⟨signedUnaryRayClass, signedUnaryRayClass_countable,
    signedUnaryRayClass_languages_infinite,
    (fun K hK => signedUnaryRayClass_regular (K := K) hK),
    signedUnaryRayClass_not_exhaustivelyGeneratable⟩

/-- Overview Theorem 3 exactly as printed, obtained by dropping the paper's
standing infinitude assumption from the explicit witness data. -/
theorem theorem3_finiteAlphabet_regular_exhaustive_generation_lower_bound :
    ∃ C : Generic.LanguageClass (List Bool),
      C.Countable ∧
      (∀ K, K ∈ C → _root_.Language.IsRegular K) ∧
      ¬ ExhaustivelyGeneratable C := by
  obtain ⟨C, hCountable, _hInfinite, hRegular, hLowerBound⟩ :=
    theorem3_finiteAlphabet_regular_exhaustive_generation_lower_bound_with_infinite_languages
  exact ⟨C, hCountable, hRegular, hLowerBound⟩

end GenLimit.CharikarPabbaraju
