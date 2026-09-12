import GenLimit.Paper18_SafeLanguageGeneration.Definitions
import Mathlib.Data.List.Infix

/-!
# Safe identification: a deterministic repair of Theorem 3.1

Definition 1 of Anastasopoulos--Ateniese--Kornaropoulos says to insert the
safe difference at a “random location” in the target family, but supplies no
probability law, quantifier over locations, or information model explaining
what the identifier knows about that location.  Its literal wording therefore
does not determine a proposition.

This module isolates the strongest deterministic content supported by the
source's phase proof:

* the candidate family is fixed before the identifier is quantified;
* every relevant safe difference is already extensionally represented in
  that fixed family, so no insertion operation is needed;
* correctness means that every eventual output names the right language,
  allowing different indices when the family has repetitions; and
* one fixed pair of countable families of infinite languages defeats every
  deterministic semantic identifier.

The three-track universe below is a countable relabeling of the source's
integer construction.  Its common harmful spine corresponds to the even
integers, its staged spine to successively exposed negative integers, and its
permanently safe spine to the positive odd integers.  The proof realizes the
finite-stopping and infinite-injury branches with one append-only labeled
stream and verifies its two tagged ranges exactly.

The result is intentionally named a repair: it proves a precise, stronger
fixed-family impossibility theorem, not a probabilistic interpretation of the
undefined “random location” sentence.
-/

namespace GenLimit.SafeGeneration.SafeIdentification

open GenLimit.Generic

/-- A three-track countable relabeling of the integer construction in the
source proof: common harmful points, successively revealed harmful points,
and permanently safe points. -/
abbrev Point := Sum ℕ (Sum ℕ ℕ)

def commonPoint (n : ℕ) : Point := Sum.inl n
def stagedPoint (n : ℕ) : Point := Sum.inr (Sum.inl n)
def safePoint (n : ℕ) : Point := Sum.inr (Sum.inr n)

def commonSpine : Set Point := Set.range commonPoint
def stagedSpine : Set Point := Set.range stagedPoint
def safeSpine : Set Point := Set.range safePoint

/-- The harmful language after exactly `a` staged points have been exposed. -/
def finiteHarmful (a : ℕ) : Set Point :=
  commonSpine ∪ {x | ∃ k < a, x = stagedPoint k}

/-- The limiting harmful language after every staged point is exposed. -/
def limitHarmful : Set Point :=
  commonSpine ∪ stagedSpine

/-- The corresponding safe difference after `a` exposures. -/
def tailSafe (a : ℕ) : Set Point :=
  safeSpine ∪ {x | ∃ k, a ≤ k ∧ x = stagedPoint k}

/-- The fixed candidate/target family.  Index `0` is the universal target,
index `1` is the limiting safe spine, and index `a+2` is `tailSafe a`. -/
def candidateFamily : Generic.LanguageFamily Point
  | 0 => Set.univ
  | 1 => safeSpine
  | a + 2 => tailSafe a

/-- The fixed harmful family.  Index `0` is the limiting harmful language,
and index `a+1` is the finite-stage language. -/
def harmfulFamily : Generic.LanguageFamily Point
  | 0 => limitHarmful
  | a + 1 => finiteHarmful a

abbrev SafeIdentifier (α : Type*) :=
  ∀ t : ℕ, (Fin t → Tagged α) → ℕ

def identifierOutput
    (M : SafeIdentifier α) (stream : Stream (Tagged α)) (t : ℕ) : ℕ :=
  M t fun i => stream i

/-- Deterministic repair of “insert at a random location”: the candidate
family is explicit and the safe difference is required to be represented. -/
def DifferenceRepresented
    (C : Generic.LanguageFamily α)
    (target harmful : Generic.Language α) : Prop :=
  ∃ i, C i = target \ harmful

/-- Extensional eventual correctness allows repeated indices for the same
language, exactly as the source definition's “an index `i` for which ...”. -/
def SafelyIdentifiesFrom
    (M : SafeIdentifier α) (C : Generic.LanguageFamily α)
    (target harmful : Generic.Language α)
    (stream : Stream (Tagged α)) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    C (identifierOutput M stream t) = target \ harmful

/-- Reindex an already fixed candidate family. -/
def reindexFamily
    (e : ℕ ≃ ℕ) (C : Generic.LanguageFamily α) :
    Generic.LanguageFamily α :=
  fun i => C (e i)

/-- Transport an identifier along the inverse reindexing. -/
def reindexIdentifier
    (e : ℕ ≃ ℕ) (M : SafeIdentifier α) :
    SafeIdentifier α :=
  fun t xs => e.symm (M t xs)

theorem reindexed_output_language
    (e : ℕ ≃ ℕ)
    (M : SafeIdentifier α)
    (C : Generic.LanguageFamily α)
    (stream : Stream (Tagged α))
    (t : ℕ) :
    reindexFamily e C
        (identifierOutput (reindexIdentifier e M) stream t) =
      C (identifierOutput M stream t) := by
  simp [reindexFamily, reindexIdentifier, identifierOutput]

/-- Merely moving the represented difference to another fixed index does
not change whether it is represented. -/
theorem differenceRepresented_reindex_iff
    (e : ℕ ≃ ℕ)
    (C : Generic.LanguageFamily α)
    (target harmful : Generic.Language α) :
    DifferenceRepresented (reindexFamily e C) target harmful ↔
      DifferenceRepresented C target harmful := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by
      simpa [reindexFamily] using hi⟩

/-- Extensional safe-identification success is equivariant under every fixed
permutation of an already-fixed candidate family, once the identifier is
transported with that permutation.  This diagnostic does not model inserting
a new language, hiding the realized permutation, or holding one learner
fixed; those readings require the probability, information, and success
semantics absent from the source. -/
theorem safelyIdentifiesFrom_reindex_iff
    (e : ℕ ≃ ℕ)
    (M : SafeIdentifier α)
    (C : Generic.LanguageFamily α)
    (target harmful : Generic.Language α)
    (stream : Stream (Tagged α)) :
    SafelyIdentifiesFrom (reindexIdentifier e M)
        (reindexFamily e C) target harmful stream ↔
      SafelyIdentifiesFrom M C target harmful stream := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht
    rw [← reindexed_output_language e M C stream t]
    exact hT t ht
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht
    rw [reindexed_output_language e M C stream t]
    exact hT t ht

theorem univ_diff_finiteHarmful (a : ℕ) :
    (Set.univ : Set Point) \ finiteHarmful a = tailSafe a := by
  ext x
  rcases x with n | (n | n)
  · simp [finiteHarmful, tailSafe, commonSpine, safeSpine,
      commonPoint, stagedPoint, safePoint]
  · simp only [Set.mem_diff, Set.mem_univ, true_and, finiteHarmful,
      tailSafe, commonSpine, safeSpine, commonPoint, stagedPoint, safePoint,
      Set.mem_union, Set.mem_range, Set.mem_setOf_eq]
    constructor
    · intro h
      right
      refine ⟨n, ?_, rfl⟩
      by_contra hna
      apply h
      right
      exact ⟨n, Nat.lt_of_not_ge hna, rfl⟩
    · rintro (_ | ⟨k, hak, hk⟩)
      · simp_all
      · cases hk
        intro h
        rcases h with h | ⟨j, hja, hj⟩
        · simp_all
        · cases hj
          omega
  · simp [finiteHarmful, tailSafe, commonSpine, safeSpine,
      commonPoint, stagedPoint, safePoint]

theorem univ_diff_limitHarmful :
    (Set.univ : Set Point) \ limitHarmful = safeSpine := by
  ext x
  rcases x with n | (n | n) <;>
    simp [limitHarmful, commonSpine, stagedSpine, safeSpine,
      commonPoint, stagedPoint, safePoint]

theorem candidate_tailSafe (a : ℕ) :
    candidateFamily (a + 2) = tailSafe a := by
  simp [candidateFamily]

theorem candidate_safeSpine :
    candidateFamily 1 = safeSpine := by
  simp [candidateFamily]

theorem candidate_univ :
    candidateFamily 0 = (Set.univ : Set Point) := by
  simp [candidateFamily]

theorem harmful_finite (a : ℕ) :
    harmfulFamily (a + 1) = finiteHarmful a := by
  simp [harmfulFamily]

theorem harmful_limit :
    harmfulFamily 0 = limitHarmful := by
  simp [harmfulFamily]

structure DiagonalState where
  phase : ℕ
  history : List (Tagged Point)

def frontBlock (n : ℕ) : List (Tagged Point) :=
  [(commonPoint n, true), (stagedPoint n, true), (safePoint n, true),
    (commonPoint n, false)]

noncomputable def nextState
    (M : SafeIdentifier Point) (n : ℕ) (s : DiagonalState) :
    DiagonalState := by
  classical
  let front := s.history ++ frontBlock n
  let guessed := candidateFamily (M front.length front.get)
  exact if guessed = tailSafe s.phase then
    ⟨s.phase + 1, front ++ [(stagedPoint s.phase, false)]⟩
  else
    ⟨s.phase, front ++ [(commonPoint 0, false)]⟩

noncomputable def diagonalState (M : SafeIdentifier Point) :
    ℕ → DiagonalState
  | 0 => ⟨0, []⟩
  | n + 1 => nextState M n (diagonalState M n)

noncomputable def stageFront (M : SafeIdentifier Point) (n : ℕ) :
    List (Tagged Point) :=
  (diagonalState M n).history ++ frontBlock n

theorem nextState_history_length
    (M : SafeIdentifier Point) (n : ℕ) (s : DiagonalState) :
    (nextState M n s).history.length = s.history.length + 5 := by
  classical
  simp only [nextState]
  split <;> simp [frontBlock]

theorem diagonalState_history_length
    (M : SafeIdentifier Point) (n : ℕ) :
    (diagonalState M n).history.length = 5 * n := by
  induction n with
  | zero => simp [diagonalState]
  | succ n ih =>
      rw [diagonalState, nextState_history_length, ih]
      omega

theorem nextState_history_prefix
    (M : SafeIdentifier Point) (n : ℕ) (s : DiagonalState) :
    s.history <+: (nextState M n s).history := by
  classical
  simp only [nextState]
  split <;> exact
    (s.history.prefix_append (frontBlock n)).trans
      ((s.history ++ frontBlock n).prefix_append _)

theorem diagonalState_history_prefix_succ
    (M : SafeIdentifier Point) (n : ℕ) :
    (diagonalState M n).history <+:
      (diagonalState M (n + 1)).history := by
  simpa [diagonalState] using
    nextState_history_prefix M n (diagonalState M n)

theorem diagonalState_history_prefix_of_le
    (M : SafeIdentifier Point) {a b : ℕ} (hab : a ≤ b) :
    (diagonalState M a).history <+: (diagonalState M b).history := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using
          diagonalState_history_prefix_succ M (a + d))

theorem get_eq_get_of_prefix
    {xs ys : List α} (hxy : xs <+: ys) (i : ℕ)
    (hi : i < xs.length) :
    xs.get ⟨i, hi⟩ =
      ys.get ⟨i, hi.trans_le hxy.length_le⟩ := by
  obtain ⟨zs, rfl⟩ := hxy
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact (List.getElem_append_left hi).symm

/-- The infinite stream induced by the append-only diagonal histories. -/
noncomputable def diagonalStream
    (M : SafeIdentifier Point) : Stream (Tagged Point) :=
  fun t =>
    let s := diagonalState M (t / 5 + 1)
    s.history.get ⟨t, by
      rw [diagonalState_history_length]
      exact Nat.lt_mul_div_succ t (by omega)⟩

theorem diagonalStream_eq_state_get
    (M : SafeIdentifier Point) {n t : ℕ} (ht : t < 5 * n) :
    diagonalStream M t =
      (diagonalState M n).history.get
        ⟨t, by simpa [diagonalState_history_length] using ht⟩ := by
  let q := t / 5 + 1
  have hq : q ≤ n := by
    dsimp [q]
    have : t / 5 < n := (Nat.div_lt_iff_lt_mul (by omega)).2 (by
      simpa [Nat.mul_comm] using ht)
    omega
  have hpre :=
    diagonalState_history_prefix_of_le M hq
  have htq : t < (diagonalState M q).history.length := by
    rw [diagonalState_history_length]
    exact Nat.lt_mul_div_succ t (by omega)
  rw [diagonalStream]
  exact get_eq_get_of_prefix hpre t htq

theorem stageFront_length
    (M : SafeIdentifier Point) (n : ℕ) :
    (stageFront M n).length = 5 * n + 4 := by
  simp [stageFront, diagonalState_history_length, frontBlock]

theorem stageFront_prefix_next
    (M : SafeIdentifier Point) (n : ℕ) :
    stageFront M n <+: (diagonalState M (n + 1)).history := by
  classical
  simp only [diagonalState, nextState, stageFront]
  split <;> exact List.prefix_append _ _

theorem diagonalStream_stageFront_get
    (M : SafeIdentifier Point) (n : ℕ)
    (i : Fin (stageFront M n).length) :
    diagonalStream M i = (stageFront M n).get i := by
  have hlt : (i : ℕ) < 5 * (n + 1) := by
    have hi := i.isLt
    have hlen := stageFront_length M n
    omega
  rw [diagonalStream_eq_state_get M hlt]
  have hpre := stageFront_prefix_next M n
  exact (get_eq_get_of_prefix hpre i i.isLt).symm

theorem identifierOutput_stage
    (M : SafeIdentifier Point) (n : ℕ) :
    identifierOutput M (diagonalStream M) (5 * n + 4) =
      M (stageFront M n).length (stageFront M n).get := by
  rw [← stageFront_length M n]
  unfold identifierOutput
  congr 1
  funext i
  exact diagonalStream_stageFront_get M n i

theorem phase_succ_eq_or
    (M : SafeIdentifier Point) (n : ℕ) :
    (diagonalState M (n + 1)).phase =
        (diagonalState M n).phase + 1 ∨
      (diagonalState M (n + 1)).phase =
        (diagonalState M n).phase := by
  classical
  simp only [diagonalState, nextState]
  split <;> simp_all

theorem phase_mono_succ
    (M : SafeIdentifier Point) (n : ℕ) :
    (diagonalState M n).phase ≤
      (diagonalState M (n + 1)).phase := by
  rcases phase_succ_eq_or M n with h | h <;> omega

theorem phase_mono
    (M : SafeIdentifier Point) :
    Monotone (fun n => (diagonalState M n).phase) :=
  monotone_nat_of_le_succ (phase_mono_succ M)

theorem phase_le_stage
    (M : SafeIdentifier Point) (n : ℕ) :
    (diagonalState M n).phase ≤ n := by
  induction n with
  | zero => simp [diagonalState]
  | succ n ih =>
      rcases phase_succ_eq_or M n with h | h <;> omega

theorem stage_guess_eq_tail_iff_increment
    (M : SafeIdentifier Point) (n : ℕ) :
    candidateFamily
          (M (stageFront M n).length (stageFront M n).get) =
        tailSafe (diagonalState M n).phase ↔
      (diagonalState M (n + 1)).phase =
        (diagonalState M n).phase + 1 := by
  classical
  simp only [stageFront, diagonalState, nextState]
  split <;> simp_all

theorem stage_output_eq_tail_iff_increment
    (M : SafeIdentifier Point) (n : ℕ) :
    candidateFamily
          (identifierOutput M (diagonalStream M) (5 * n + 4)) =
        tailSafe (diagonalState M n).phase ↔
      (diagonalState M (n + 1)).phase =
        (diagonalState M n).phase + 1 := by
  rw [identifierOutput_stage]
  exact stage_guess_eq_tail_iff_increment M n

theorem tailSafe_ne_safeSpine (a : ℕ) :
    tailSafe a ≠ safeSpine := by
  intro h
  have hmem : stagedPoint a ∈ tailSafe a := by
    right
    exact ⟨a, le_rfl, rfl⟩
  rw [h] at hmem
  rcases hmem with ⟨k, hk⟩
  simp [stagedPoint, safePoint] at hk

theorem exists_lt_succ_iff (P : ℕ → Prop) (n : ℕ) :
    (∃ k < n + 1, P k) ↔ (∃ k < n, P k) ∨ P n := by
  constructor
  · rintro ⟨k, hk, hPk⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact Or.inl ⟨k, hk, hPk⟩
    · exact Or.inr hPk
  · rintro (⟨k, hk, hPk⟩ | hPn)
    · exact ⟨k, hk.step, hPk⟩
    · exact ⟨n, Nat.lt_succ_self n, hPn⟩

theorem state_history_true_iff
    (M : SafeIdentifier Point) (n : ℕ) (x : Point) :
    (x, true) ∈ (diagonalState M n).history ↔
      ∃ k < n,
        x = commonPoint k ∨ x = stagedPoint k ∨ x = safePoint k := by
  classical
  induction n with
  | zero => simp [diagonalState]
  | succ n ih =>
      rw [diagonalState]
      simp only [nextState]
      split
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
          Prod.mk.injEq, Bool.true_eq_false, and_false, or_false,
          frontBlock, ih]
        simp only [and_true]
        rw [exists_lt_succ_iff]
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
          Prod.mk.injEq, Bool.true_eq_false, and_false, or_false,
          frontBlock, ih]
        simp only [and_true]
        rw [exists_lt_succ_iff]

theorem state_history_false_iff
    (M : SafeIdentifier Point) (n : ℕ) (x : Point) :
    (x, false) ∈ (diagonalState M n).history ↔
      (∃ k < n, x = commonPoint k) ∨
      (∃ k < (diagonalState M n).phase, x = stagedPoint k) := by
  classical
  induction n with
  | zero => simp [diagonalState]
  | succ n ih =>
      rw [diagonalState]
      simp only [nextState]
      split
      · rename_i htrigger
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
          Prod.mk.injEq, Bool.false_eq_true,
          and_false, false_or, or_false, frontBlock, ih]
        simp only [and_true]
        constructor
        · intro h
          rcases h with ((hC | hS) | hCN) | hSP
          · left
            obtain ⟨k, hk, hx⟩ := hC
            exact ⟨k, hk.step, hx⟩
          · right
            obtain ⟨k, hk, hx⟩ := hS
            exact ⟨k, hk.step, hx⟩
          · left
            exact ⟨n, Nat.lt_succ_self n, hCN⟩
          · right
            exact ⟨(diagonalState M n).phase,
              Nat.lt_succ_self _, hSP⟩
        · rintro (h | h)
          · rw [exists_lt_succ_iff] at h
            rcases h with h | h
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inl (Or.inr h)
          · rw [exists_lt_succ_iff] at h
            rcases h with h | h
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inr h
      · rename_i htrigger
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
          Prod.mk.injEq, Bool.false_eq_true,
          and_false, false_or, or_false, frontBlock, ih]
        simp only [and_true]
        constructor
        · intro h
          rcases h with ((hC | hS) | hCN) | hC0
          · left
            obtain ⟨k, hk, hx⟩ := hC
            exact ⟨k, hk.step, hx⟩
          · exact Or.inr hS
          · left
            exact ⟨n, Nat.lt_succ_self n, hCN⟩
          · left
            exact ⟨0, Nat.zero_lt_succ n, hC0⟩
        · rintro (h | h)
          · rw [exists_lt_succ_iff] at h
            rcases h with h | h
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl (Or.inr h))

theorem mem_diagonal_taggedRange_iff
    (M : SafeIdentifier Point) (b : Bool) (x : Point) :
    x ∈ taggedRange (diagonalStream M) b ↔
      ∃ n, (x, b) ∈ (diagonalState M n).history := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t / 5 + 1, ?_⟩
    have hmem :
        (diagonalState M (t / 5 + 1)).history.get
            ⟨t, by
              rw [diagonalState_history_length]
              exact Nat.lt_mul_div_succ t (by omega)⟩ ∈
          (diagonalState M (t / 5 + 1)).history :=
      List.get_mem _ _
    rw [← ht]
    simpa only [diagonalStream] using hmem
  · rintro ⟨n, hn⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hn
    refine ⟨i, ?_⟩
    have hlt : (i : ℕ) < 5 * n := by
      have hiLt := i.isLt
      have hlen := diagonalState_history_length M n
      omega
    rw [diagonalStream_eq_state_get M hlt]
    exact hi

theorem diagonal_true_range
    (M : SafeIdentifier Point) :
    taggedRange (diagonalStream M) true = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_diagonal_taggedRange_iff]
  rcases x with n | (n | n)
  · refine ⟨n + 1, (state_history_true_iff M (n + 1) _).2 ?_⟩
    exact ⟨n, by omega, Or.inl rfl⟩
  · refine ⟨n + 1, (state_history_true_iff M (n + 1) _).2 ?_⟩
    exact ⟨n, by omega, Or.inr (Or.inl rfl)⟩
  · refine ⟨n + 1, (state_history_true_iff M (n + 1) _).2 ?_⟩
    exact ⟨n, by omega, Or.inr (Or.inr rfl)⟩

theorem diagonal_false_range_of_eventually_phase
    (M : SafeIdentifier Point) (a N : ℕ)
    (hphase : ∀ n, N ≤ n → (diagonalState M n).phase = a) :
    taggedRange (diagonalStream M) false = finiteHarmful a := by
  ext x
  rw [mem_diagonal_taggedRange_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [state_history_false_iff] at hn
    rcases hn with ⟨k, hkn, rfl⟩ | ⟨k, hkp, rfl⟩
    · exact Or.inl ⟨k, rfl⟩
    · apply Or.inr
      refine ⟨k, ?_, rfl⟩
      by_cases hnN : n ≤ N
      · have hp_le :
            (diagonalState M n).phase ≤
              (diagonalState M N).phase :=
          phase_mono M hnN
        rw [hphase N le_rfl] at hp_le
        omega
      · rw [hphase n (by omega)] at hkp
        exact hkp
  · intro hx
    rcases hx with ⟨k, rfl⟩ | ⟨k, hka, rfl⟩
    · refine ⟨k + 1, (state_history_false_iff M (k + 1) _).2 ?_⟩
      exact Or.inl ⟨k, by omega, rfl⟩
    · let n := max N (k + 1)
      refine ⟨n, (state_history_false_iff M n _).2 ?_⟩
      apply Or.inr
      refine ⟨k, ?_, rfl⟩
      rw [hphase n (Nat.le_max_left _ _)]
      exact hka

theorem diagonal_false_range_of_unbounded_phase
    (M : SafeIdentifier Point)
    (hunbounded :
      ¬ ∃ c, ∀ n, (diagonalState M n).phase ≤ c) :
    taggedRange (diagonalStream M) false = limitHarmful := by
  ext x
  rw [mem_diagonal_taggedRange_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [state_history_false_iff] at hn
    rcases hn with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · refine ⟨k + 1, (state_history_false_iff M (k + 1) _).2 ?_⟩
      exact Or.inl ⟨k, by omega, rfl⟩
    · have hex : ∃ n, k < (diagonalState M n).phase := by
        by_contra h
        push_neg at h
        exact hunbounded ⟨k, h⟩
      obtain ⟨n, hn⟩ := hex
      exact ⟨n, (state_history_false_iff M n _).2
        (Or.inr ⟨k, hn, rfl⟩)⟩

theorem commonPoint_injective : Function.Injective commonPoint := by
  intro a b h
  exact Sum.inl.inj h

theorem safePoint_injective : Function.Injective safePoint := by
  intro a b h
  exact Sum.inr.inj (Sum.inr.inj h)

theorem commonSpine_infinite : commonSpine.Infinite := by
  exact Set.infinite_range_of_injective commonPoint_injective

theorem safeSpine_infinite : safeSpine.Infinite := by
  exact Set.infinite_range_of_injective safePoint_injective

theorem tailSafe_infinite (a : ℕ) : (tailSafe a).Infinite :=
  safeSpine_infinite.mono Set.subset_union_left

theorem finiteHarmful_infinite (a : ℕ) :
    (finiteHarmful a).Infinite :=
  commonSpine_infinite.mono Set.subset_union_left

theorem limitHarmful_infinite : limitHarmful.Infinite :=
  commonSpine_infinite.mono Set.subset_union_left

theorem candidateFamily_infinite (i : ℕ) :
    (candidateFamily i).Infinite := by
  rcases i with _ | i
  · rw [candidate_univ]
    exact commonSpine_infinite.mono (Set.subset_univ _)
  · rcases i with _ | a
    · simpa [candidateFamily] using safeSpine_infinite
    · simpa [candidateFamily] using tailSafe_infinite a

theorem harmfulFamily_infinite (j : ℕ) :
    (harmfulFamily j).Infinite := by
  rcases j with _ | a
  · simpa [harmfulFamily] using limitHarmful_infinite
  · simpa [harmfulFamily] using finiteHarmful_infinite a

theorem every_safe_difference_represented (j : ℕ) :
    DifferenceRepresented candidateFamily
      (candidateFamily 0) (harmfulFamily j) := by
  cases j with
  | zero =>
      refine ⟨1, ?_⟩
      rw [candidate_safeSpine, candidate_univ, harmful_limit,
        univ_diff_limitHarmful]
  | succ a =>
      refine ⟨a + 2, ?_⟩
      rw [candidate_tailSafe, candidate_univ, harmful_finite,
        univ_diff_finiteHarmful]

/-- Source-faithful deterministic repair of Theorem 3.1.

One fixed pair of countable indexed families of infinite languages defeats
every deterministic semantic safe identifier.  The true language is always
the same universal member.  Every possible safe difference is already
represented in the fixed candidate family, so the undefined “random
location” insertion is replaced by an explicit extensional representation
condition and no probability semantics is assumed. -/
theorem theorem_3_1_deterministic_repair :
    (∀ i, (candidateFamily i).Infinite) ∧
    (∀ j, (harmfulFamily j).Infinite) ∧
    (∀ j, DifferenceRepresented candidateFamily
      (candidateFamily 0) (harmfulFamily j)) ∧
    ∀ M : SafeIdentifier Point,
      ∃ j, DifferenceRepresented candidateFamily
          (candidateFamily 0) (harmfulFamily j) ∧
        LabeledPresents (diagonalStream M)
          (candidateFamily 0) (harmfulFamily j) ∧
        ¬ SafelyIdentifiesFrom M candidateFamily
          (candidateFamily 0) (harmfulFamily j) (diagonalStream M) := by
  refine ⟨candidateFamily_infinite, harmfulFamily_infinite,
    every_safe_difference_represented, ?_⟩
  intro M
  by_cases hbounded :
      ∃ c, ∀ n, (diagonalState M n).phase ≤ c
  · obtain ⟨c, hc⟩ := hbounded
    obtain ⟨a, N, hphase⟩ :=
      converges_of_monotone_of_bounded (phase_mono M) hc
    refine ⟨a + 1, every_safe_difference_represented (a + 1), ?_, ?_⟩
    · constructor
      · rw [candidate_univ]
        exact diagonal_true_range M
      · rw [harmful_finite]
        exact diagonal_false_range_of_eventually_phase M a N hphase
    · intro hidentifies
      obtain ⟨T, hT⟩ := hidentifies
      let n := max N T
      have hnN : N ≤ n := Nat.le_max_left _ _
      have hnT : T ≤ n := Nat.le_max_right _ _
      have hcorrect :=
        hT (5 * n + 4) (by omega)
      rw [candidate_univ, harmful_finite,
        univ_diff_finiteHarmful] at hcorrect
      have hpn : (diagonalState M n).phase = a := hphase n hnN
      have hinc :
          (diagonalState M (n + 1)).phase =
            (diagonalState M n).phase + 1 :=
        (stage_output_eq_tail_iff_increment M n).mp (by
          simpa [hpn] using hcorrect)
      have hpnext :
          (diagonalState M (n + 1)).phase = a :=
        hphase (n + 1) (by omega)
      omega
  · refine ⟨0, every_safe_difference_represented 0, ?_, ?_⟩
    · constructor
      · rw [candidate_univ]
        exact diagonal_true_range M
      · rw [harmful_limit]
        exact diagonal_false_range_of_unbounded_phase M hbounded
    · intro hidentifies
      obtain ⟨T, hT⟩ := hidentifies
      have hnoIncrement :
          ∀ n, T ≤ n →
            (diagonalState M (n + 1)).phase =
              (diagonalState M n).phase := by
        intro n hn
        have hcorrect :=
          hT (5 * n + 4) (by omega)
        rw [candidate_univ, harmful_limit,
          univ_diff_limitHarmful] at hcorrect
        have hnot :
            ¬ candidateFamily
                (identifierOutput M (diagonalStream M) (5 * n + 4)) =
              tailSafe (diagonalState M n).phase := by
          intro htail
          apply tailSafe_ne_safeSpine (diagonalState M n).phase
          exact htail.symm.trans hcorrect
        rcases phase_succ_eq_or M n with hinc | hsame
        · exact False.elim
            (hnot ((stage_output_eq_tail_iff_increment M n).2 hinc))
        · exact hsame
      have hconstant :
          ∀ d, (diagonalState M (T + d)).phase =
            (diagonalState M T).phase := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
            rw [Nat.add_succ]
            exact (hnoIncrement (T + d) (by omega)).trans ih
      apply hbounded
      refine ⟨(diagonalState M T).phase, ?_⟩
      intro n
      by_cases hn : n ≤ T
      · exact phase_mono M hn
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (by omega : T ≤ n)
        rw [hconstant]

end GenLimit.SafeGeneration.SafeIdentification
