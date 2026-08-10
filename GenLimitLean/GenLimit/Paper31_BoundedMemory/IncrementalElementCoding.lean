import GenLimit.Paper31_BoundedMemory.IncrementalIdentification
import Mathlib.Data.Set.Finite.Lattice

/-!
# Incremental element coding

This module formalizes the Appendix coding-compilation construction of
Kleinberg--Mehrotra--Saberi--Velegkas.  It allocates globally disjoint,
infinite, cofinal coding cells inside a finite family of infinite languages,
uses the previous generated element to encode the exact observed history,
and compiles eventual one-sided approximate identification into fresh
element generation.

The source works on its canonical countable universe; this development uses
`ℕ` and nonempty finite families indexed by `Fin (N + 1)`.  The construction
is deliberately semantic and noncomputable.  It asserts no oracle, bit-cost,
or running-time bound, in accord with the source's explicit open computational
and representation questions.
-/

namespace GenLimit.BoundedMemory

open Function

section Codebook

variable {N : ℕ}

/-- A code request stores the current language index, the full finite
history, and an arbitrary salt used to obtain infinitely many codewords for
the same history. -/
abbrev ElementCodeRequest (N : ℕ) :=
  Fin (N + 1) × List ℕ × ℕ

def defaultElementCodeRequest : ElementCodeRequest N :=
  ((0 : Fin (N + 1)), [], 0)

/-- Decode a natural-number request code, using a harmless default off the
range of the canonical `Encodable` coding. -/
def elementCodeRequestAt (r : ℕ) : ElementCodeRequest N :=
  (Encodable.decode r).getD defaultElementCodeRequest

@[simp]
theorem elementCodeRequestAt_encode
    (q : ElementCodeRequest N) :
    elementCodeRequestAt (Encodable.encode q) = q := by
  simp [elementCodeRequestAt, Encodable.encodek]

/-- At stage `r`, choose a point in the requested language which is outside
all earlier choices and above `r`. -/
noncomputable def freshElementCode
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (r : ℕ) (used : Finset ℕ) : ℕ :=
  Classical.choose <|
    (hInfinite (elementCodeRequestAt r).1).exists_notMem_finset
      (used ∪ Finset.range (r + 1))

theorem freshElementCode_mem
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (r : ℕ) (used : Finset ℕ) :
    freshElementCode langs hInfinite r used ∈
      langs (elementCodeRequestAt r).1 :=
  (Classical.choose_spec <|
    (hInfinite (elementCodeRequestAt r).1).exists_notMem_finset
      (used ∪ Finset.range (r + 1))).1

theorem freshElementCode_not_mem
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (r : ℕ) (used : Finset ℕ) :
    freshElementCode langs hInfinite r used ∉ used := by
  have h :=
    (Classical.choose_spec <|
      (hInfinite (elementCodeRequestAt r).1).exists_notMem_finset
        (used ∪ Finset.range (r + 1))).2
  exact fun hmem => h (Finset.mem_union_left _ hmem)

theorem freshElementCode_gt
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (r : ℕ) (used : Finset ℕ) :
    r < freshElementCode langs hInfinite r used := by
  have h :=
    (Classical.choose_spec <|
      (hInfinite (elementCodeRequestAt r).1).exists_notMem_finset
        (used ∪ Finset.range (r + 1))).2
  have hnot :
      freshElementCode langs hInfinite r used ∉ Finset.range (r + 1) :=
    fun hmem => h (Finset.mem_union_right _ hmem)
  simp only [Finset.mem_range, not_lt] at hnot
  omega

/-- The finite set of codewords allocated before stage `r`. -/
noncomputable def elementCodeUsed
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite) :
    ℕ → Finset ℕ
  | 0 => ∅
  | r + 1 =>
      insert
        (freshElementCode langs hInfinite r
          (elementCodeUsed langs hInfinite r))
        (elementCodeUsed langs hInfinite r)

/-- The globally fresh codeword allocated to request-code stage `r`. -/
noncomputable def elementCodewordAt
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (r : ℕ) : ℕ :=
  freshElementCode langs hInfinite r
    (elementCodeUsed langs hInfinite r)

theorem elementCodewordAt_mem
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (r : ℕ) :
    elementCodewordAt langs hInfinite r ∈
      langs (elementCodeRequestAt r).1 :=
  freshElementCode_mem langs hInfinite r _

theorem elementCodewordAt_not_used
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (r : ℕ) :
    elementCodewordAt langs hInfinite r ∉
      elementCodeUsed langs hInfinite r :=
  freshElementCode_not_mem langs hInfinite r _

theorem elementCodewordAt_gt
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (r : ℕ) :
    r < elementCodewordAt langs hInfinite r :=
  freshElementCode_gt langs hInfinite r _

theorem elementCodeUsed_mono
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    {r s : ℕ} (hrs : r ≤ s) :
    elementCodeUsed langs hInfinite r ⊆
      elementCodeUsed langs hInfinite s := by
  induction s with
  | zero =>
      have : r = 0 := by omega
      subst r
      exact Finset.Subset.rfl
  | succ s ih =>
      by_cases hEq : r = s + 1
      · subst r
        exact Finset.Subset.rfl
      · have hrs' : r ≤ s := by omega
        exact (ih hrs').trans (by
          intro x hx
          simp [elementCodeUsed, hx])

theorem earlier_elementCodeword_used
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    {r s : ℕ} (hrs : r < s) :
    elementCodewordAt langs hInfinite r ∈
      elementCodeUsed langs hInfinite s := by
  have hnext :
      elementCodewordAt langs hInfinite r ∈
        elementCodeUsed langs hInfinite (r + 1) := by
    simp [elementCodeUsed, elementCodewordAt]
  exact elementCodeUsed_mono langs hInfinite (by omega) hnext

theorem elementCodewordAt_injective
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite) :
    Injective (elementCodewordAt langs hInfinite) := by
  intro r s hrs
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (elementCodewordAt_not_used langs hInfinite s)
      (hrs ▸ earlier_elementCodeword_used langs hInfinite hlt)
  · exact (elementCodewordAt_not_used langs hInfinite r)
      (hrs.symm ▸ earlier_elementCodeword_used langs hInfinite hgt)

/-- The codeword for `(language index, exact finite history, salt)`. -/
noncomputable def elementCode
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) (history : List ℕ) (salt : ℕ) : ℕ :=
  elementCodewordAt langs hInfinite
    (Encodable.encode (i, history, salt))

theorem elementCode_mem
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) (history : List ℕ) (salt : ℕ) :
    elementCode langs hInfinite i history salt ∈ langs i := by
  have h :=
    elementCodewordAt_mem langs hInfinite
      (Encodable.encode ((i, history, salt) : ElementCodeRequest N))
  have hrequest :
      elementCodeRequestAt
          (Encodable.encode ((i, history, salt) : ElementCodeRequest N)) =
        (i, history, salt) :=
    elementCodeRequestAt_encode (i, history, salt)
  rw [hrequest] at h
  exact h

theorem elementCode_triple_injective
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite) :
    Injective
      (fun q : ElementCodeRequest N =>
        elementCode langs hInfinite q.1 q.2.1 q.2.2) := by
  intro q r hqr
  apply Encodable.encode_injective
  exact elementCodewordAt_injective langs hInfinite hqr

theorem elementCode_salt_injective
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) (history : List ℕ) :
    Injective (elementCode langs hInfinite i history) := by
  intro m n hmn
  have htriple :
      (i, history, m) = (i, history, n) :=
    elementCode_triple_injective langs hInfinite hmn
  exact congrArg (fun q : ElementCodeRequest N => q.2.2) htriple

/-- For a fixed language and fixed encoded history, varying the salt yields
codewords cofinal in the canonical order on `ℕ`. -/
theorem exists_elementCode_gt
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) (history : List ℕ) (bound : ℕ) :
    ∃ salt, bound < elementCode langs hInfinite i history salt := by
  have hRange :
      (Set.range (elementCode langs hInfinite i history)).Infinite :=
    Set.infinite_range_of_injective
      (elementCode_salt_injective langs hInfinite i history)
  obtain ⟨x, hxRange, hxOutside⟩ :=
    hRange.exists_notMem_finset (Finset.range (bound + 1))
  obtain ⟨salt, rfl⟩ := hxRange
  refine ⟨salt, ?_⟩
  simp only [Finset.mem_range, not_lt] at hxOutside
  omega

/-- The least salt producing a codeword above `bound`. -/
noncomputable def nextElementCodeSalt
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) (history : List ℕ) (bound : ℕ) : ℕ :=
  Nat.find (exists_elementCode_gt langs hInfinite i history bound)

theorem nextElementCode_gt
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) (history : List ℕ) (bound : ℕ) :
    bound <
      elementCode langs hInfinite i history
        (nextElementCodeSalt langs hInfinite i history bound) :=
  Nat.find_spec (exists_elementCode_gt langs hInfinite i history bound)

/-- The `i`th disjoint cofinal coding cell from the appendix. -/
def elementCodingCell
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) : Set ℕ :=
  Set.range (elementCode langs hInfinite i [])

theorem elementCodingCell_infinite
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) :
    (elementCodingCell langs hInfinite i).Infinite :=
  Set.infinite_range_of_injective
    (elementCode_salt_injective langs hInfinite i [])

theorem elementCodingCell_subset
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) :
    elementCodingCell langs hInfinite i ⊆ langs i := by
  rintro x ⟨salt, rfl⟩
  exact elementCode_mem langs hInfinite i [] salt

theorem elementCodingCell_pairwiseDisjoint
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite) :
    ∀ ⦃i j : Fin (N + 1)⦄, i ≠ j →
      Disjoint
        (elementCodingCell langs hInfinite i)
        (elementCodingCell langs hInfinite j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  obtain ⟨m, hm⟩ := hxi
  obtain ⟨n, hn⟩ := hxj
  have htriple :
      (i, [], m) = (j, [], n) :=
    elementCode_triple_injective langs hInfinite (hm.trans hn.symm)
  exact hij (congrArg (fun q : ElementCodeRequest N => q.1) htriple)

theorem elementCodingCell_cofinal
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) (x : ℕ) :
    ∃ y ∈ elementCodingCell langs hInfinite i, x < y := by
  obtain ⟨salt, hsalt⟩ :=
    exists_elementCode_gt langs hInfinite i [] x
  exact ⟨elementCode langs hInfinite i [] salt, ⟨salt, rfl⟩, hsalt⟩

/-- Lemma A.3: every finite family of infinite languages admits pairwise
disjoint infinite cofinal coding cells contained in the corresponding
languages. -/
theorem lemma_A_3
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite) :
    ∃ cells : Fin (N + 1) → Set ℕ,
      (∀ i, (cells i).Infinite ∧ cells i ⊆ langs i) ∧
      Pairwise (Disjoint on cells) ∧
      ∀ i x, ∃ y ∈ cells i, x < y := by
  refine ⟨elementCodingCell langs hInfinite, ?_, ?_, ?_⟩
  · intro i
    exact
      ⟨elementCodingCell_infinite langs hInfinite i,
        elementCodingCell_subset langs hInfinite i⟩
  · exact elementCodingCell_pairwiseDisjoint langs hInfinite
  · exact elementCodingCell_cofinal langs hInfinite

end Codebook

section CodingCompilation

variable {N : ℕ}

/-- The first `t` examples, in chronological order. -/
def elementHistoryPrefix (stream : ℕ → ℕ) (t : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin t => stream i)

@[simp]
theorem elementHistoryPrefix_zero (stream : ℕ → ℕ) :
    elementHistoryPrefix stream 0 = [] := by
  simp [elementHistoryPrefix]

theorem elementHistoryPrefix_succ (stream : ℕ → ℕ) (t : ℕ) :
    elementHistoryPrefix stream (t + 1) =
      elementHistoryPrefix stream t ++ [stream t] := by
  simpa [elementHistoryPrefix] using
    (List.ofFn_succ'
      (fun i : Fin (t + 1) => stream i))

/-- An unrestricted full-information learner returning a family index. -/
abbrev FullInformationIndexLearner (N : ℕ) :=
  List ℕ → Fin (N + 1)

/-- The exact one-sided premise of the paper's coding-compilation theorem. -/
def EventuallyAlmostContainedHypotheses
    (langs : Fin (N + 1) → Set ℕ)
    (M : FullInformationIndexLearner N) : Prop :=
  ∀ target stream,
    GenLimit.Generic.Presents stream (langs target) →
      ∃ T, ∀ t, T ≤ t →
        AlmostContained
          (langs (M (elementHistoryPrefix stream t)))
          (langs target)

/-- Success of an incremental element-based generator on one target run.
The state after `t` inputs must eventually be a fresh target element. -/
def IncrementalElementGeneratesRun
    (target : Set ℕ)
    (G : IncrementalLearner ℕ ℕ)
    (initial : ℕ) (stream : ℕ → ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    incrementalRun G initial stream t ∈
      target \ Set.range (fun s : Fin t => stream s)

/-- A finite family admits one incremental element generator that works for
every target and every exact presentation. -/
def IncrementallyElementGenerable
    (langs : Fin (N + 1) → Set ℕ) : Prop :=
  ∃ G : IncrementalLearner ℕ ℕ, ∃ initial,
    ∀ target stream,
      GenLimit.Generic.Presents stream (langs target) →
        IncrementalElementGeneratesRun
          (langs target) G initial stream

/-- Read the request represented by a valid codeword.  Its behavior on
non-codewords is arbitrary, exactly as in the source proof. -/
noncomputable def decodeElementCode
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite) :
    ℕ → ElementCodeRequest N :=
  Function.invFun
    (fun q : ElementCodeRequest N =>
      elementCode langs hInfinite q.1 q.2.1 q.2.2)

@[simp]
theorem decodeElementCode_code
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (i : Fin (N + 1)) (history : List ℕ) (salt : ℕ) :
    decodeElementCode langs hInfinite
        (elementCode langs hInfinite i history salt) =
      (i, history, salt) := by
  exact Function.leftInverse_invFun
    (elementCode_triple_injective langs hInfinite)
    (i, history, salt)

/-- Compile a full-history learner into a last-output element generator.
The output is selected above both the preceding output and current datum. -/
noncomputable def codingCompiledGenerator
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N) :
    IncrementalLearner ℕ ℕ :=
  fun state x =>
    let old := decodeElementCode langs hInfinite state
    let history := old.2.1 ++ [x]
    let index := M history
    let salt :=
      nextElementCodeSalt langs hInfinite index history (max state x)
    elementCode langs hInfinite index history salt

noncomputable def codingCompiledInitial
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N) : ℕ :=
  elementCode langs hInfinite (M []) [] 0

theorem codingCompiledGenerator_gt_state
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N)
    (state x : ℕ) :
    state < codingCompiledGenerator langs hInfinite M state x := by
  have h :=
    nextElementCode_gt langs hInfinite
      (M ((decodeElementCode langs hInfinite state).2.1 ++ [x]))
      ((decodeElementCode langs hInfinite state).2.1 ++ [x])
      (max state x)
  simpa [codingCompiledGenerator] using
    (lt_of_le_of_lt (Nat.le_max_left state x) h)

theorem codingCompiledGenerator_gt_input
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N)
    (state x : ℕ) :
    x < codingCompiledGenerator langs hInfinite M state x := by
  have h :=
    nextElementCode_gt langs hInfinite
      (M ((decodeElementCode langs hInfinite state).2.1 ++ [x]))
      ((decodeElementCode langs hInfinite state).2.1 ++ [x])
      (max state x)
  simpa [codingCompiledGenerator] using
    (lt_of_le_of_lt (Nat.le_max_right state x) h)

/-- Along an intended run, the current output losslessly records the exact
prefix and the full-information learner's current hypothesis. -/
theorem codingCompiled_run_is_code
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N)
    (stream : ℕ → ℕ) :
    ∀ t, ∃ salt,
      incrementalRun
          (codingCompiledGenerator langs hInfinite M)
          (codingCompiledInitial langs hInfinite M)
          stream t =
        elementCode langs hInfinite
          (M (elementHistoryPrefix stream t))
          (elementHistoryPrefix stream t) salt := by
  intro t
  induction t with
  | zero =>
      exact ⟨0, by
        simp [codingCompiledInitial]⟩
  | succ t ih =>
      obtain ⟨salt, ih⟩ := ih
      refine ⟨
        nextElementCodeSalt langs hInfinite
          (M (elementHistoryPrefix stream t ++ [stream t]))
          (elementHistoryPrefix stream t ++ [stream t])
          (max
            (elementCode langs hInfinite
              (M (elementHistoryPrefix stream t))
              (elementHistoryPrefix stream t) salt)
            (stream t)),
        ?_⟩
      rw [incrementalRun_succ, ih]
      simp only [codingCompiledGenerator, decodeElementCode_code]
      rw [elementHistoryPrefix_succ]

/-- Every earlier input is strictly below the current output. -/
theorem codingCompiled_run_gt_seen
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N)
    (stream : ℕ → ℕ) :
    ∀ {t s}, s < t →
      stream s <
        incrementalRun
          (codingCompiledGenerator langs hInfinite M)
          (codingCompiledInitial langs hInfinite M)
          stream t := by
  intro t
  induction t with
  | zero =>
      intro s hs
      omega
  | succ t ih =>
      intro s hs
      rw [incrementalRun_succ]
      by_cases hst : s = t
      · subst s
        exact codingCompiledGenerator_gt_input
          langs hInfinite M _ _
      · have hlt : s < t := by omega
        exact (ih hlt).trans
          (codingCompiledGenerator_gt_state langs hInfinite M _ _)

theorem codingCompiled_run_fresh
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N)
    (stream : ℕ → ℕ) (t : ℕ) :
    incrementalRun
        (codingCompiledGenerator langs hInfinite M)
        (codingCompiledInitial langs hInfinite M)
        stream t ∉
      Set.range (fun s : Fin t => stream s) := by
  rintro ⟨s, hs⟩
  have hlt :=
    codingCompiled_run_gt_seen langs hInfinite M stream s.isLt
  exact (Nat.ne_of_lt hlt) hs

/-- The output after `t` updates is at least `t`; this supplies a simple
escape bound for every finite set of bad codewords. -/
theorem codingCompiled_time_le_run
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N)
    (stream : ℕ → ℕ) :
    ∀ t, t ≤
      incrementalRun
        (codingCompiledGenerator langs hInfinite M)
        (codingCompiledInitial langs hInfinite M)
        stream t := by
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
      rw [incrementalRun_succ]
      have hstep :=
        codingCompiledGenerator_gt_state langs hInfinite M
          (incrementalRun
            (codingCompiledGenerator langs hInfinite M)
            (codingCompiledInitial langs hInfinite M)
            stream t)
          (stream t)
      omega

/-- The finite union of all one-sided hypothesis errors that can matter for
the fixed target. -/
noncomputable def elementCodingBadSet
    (langs : Fin (N + 1) → Set ℕ)
    (target : Fin (N + 1)) : Set ℕ := by
  classical
  exact
    ⋃ i : Fin (N + 1),
      if AlmostContained (langs i) (langs target) then
        langs i \ langs target
      else
        ∅

theorem elementCodingBadSet_finite
    (langs : Fin (N + 1) → Set ℕ)
    (target : Fin (N + 1)) :
    (elementCodingBadSet langs target).Finite := by
  classical
  unfold elementCodingBadSet
  apply Set.finite_iUnion
  intro i
  by_cases h : AlmostContained (langs i) (langs target)
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    exact Set.finite_empty

theorem mem_elementCodingBadSet
    (langs : Fin (N + 1) → Set ℕ)
    (target i : Fin (N + 1)) {x : ℕ}
    (hAlmost : AlmostContained (langs i) (langs target))
    (hx : x ∈ langs i \ langs target) :
    x ∈ elementCodingBadSet langs target := by
  classical
  unfold elementCodingBadSet
  rw [Set.mem_iUnion]
  exact ⟨i, by simp [hAlmost, hx]⟩

/-- Appendix theorem, Coding compilation: an unrestricted learner whose
hypotheses are eventually almost contained in the target compiles to an
incremental element-based generator. -/
theorem incremental_coding_compilation
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (M : FullInformationIndexLearner N)
    (hM : EventuallyAlmostContainedHypotheses langs M) :
    IncrementallyElementGenerable langs := by
  let G := codingCompiledGenerator langs hInfinite M
  let initial := codingCompiledInitial langs hInfinite M
  refine ⟨G, initial, ?_⟩
  intro target stream hP
  obtain ⟨T₀, hT₀⟩ := hM target stream hP
  have hBadFinite := elementCodingBadSet_finite langs target
  obtain ⟨bound, hbound⟩ := hBadFinite.bddAbove
  refine ⟨max T₀ (bound + 1), ?_⟩
  intro t ht
  have ht₀ : T₀ ≤ t := (Nat.le_max_left _ _).trans ht
  have hboundt : bound < t := by
    have : bound + 1 ≤ t := (Nat.le_max_right _ _).trans ht
    omega
  obtain ⟨salt, hrun⟩ :=
    codingCompiled_run_is_code langs hInfinite M stream t
  have hlang :
      incrementalRun G initial stream t ∈
        langs (M (elementHistoryPrefix stream t)) := by
    simpa [G, initial, hrun] using
      elementCode_mem langs hInfinite
        (M (elementHistoryPrefix stream t))
        (elementHistoryPrefix stream t) salt
  have htarget :
      incrementalRun G initial stream t ∈ langs target := by
    by_contra hnot
    have hbad :
        incrementalRun G initial stream t ∈
          elementCodingBadSet langs target :=
      mem_elementCodingBadSet langs target
        (M (elementHistoryPrefix stream t))
        (hT₀ t ht₀) ⟨hlang, hnot⟩
    have hle : incrementalRun G initial stream t ≤ bound :=
      hbound hbad
    have htime : t ≤ incrementalRun G initial stream t := by
      simpa [G, initial] using
        codingCompiled_time_le_run langs hInfinite M stream t
    omega
  refine ⟨htarget, ?_⟩
  simpa [G, initial] using
    codingCompiled_run_fresh langs hInfinite M stream t

/-- Regard an incremental learner as an unrestricted learner by replaying
the finite history from its initial state. -/
def incrementalLearnerOnHistory
    {α ι : Type*}
    (learner : IncrementalLearner α ι) (initial : ι) :
    List α → ι :=
  fun history => history.foldl learner initial

theorem incrementalLearnerOnHistory_prefix
    {α ι : Type*}
    (learner : IncrementalLearner α ι) (initial : ι)
    (stream : ℕ → α) :
    ∀ t,
      incrementalLearnerOnHistory learner initial
          (List.ofFn (fun i : Fin t => stream i)) =
        incrementalRun learner initial stream t := by
  intro t
  induction t with
  | zero =>
      simp [incrementalLearnerOnHistory]
  | succ t ih =>
      rw [List.ofFn_succ']
      have hfold :
          (List.ofFn (fun i : Fin t => stream i)).foldl learner initial =
            incrementalRun learner initial stream t := by
        simpa [incrementalLearnerOnHistory] using ih
      simp [incrementalLearnerOnHistory, hfold]

/-- Approximate identification supplies the one-sided premise needed by the
coding compiler. -/
theorem incremental_element_generation_of_approximate_identification
    (langs : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (langs i).Infinite)
    (hApprox : IncrementallyApproximatelyIdentifiable langs) :
    IncrementallyElementGenerable langs := by
  obtain ⟨learner, initial, hLearner⟩ := hApprox
  let M : FullInformationIndexLearner N :=
    incrementalLearnerOnHistory learner initial
  apply incremental_coding_compilation langs hInfinite M
  intro target stream hP
  obtain ⟨T, hT⟩ := hLearner target stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have hApproxAt := hT t ht
  have hReplay :
      M (elementHistoryPrefix stream t) =
        incrementalRun learner initial stream t := by
    simpa [M, elementHistoryPrefix] using
      incrementalLearnerOnHistory_prefix learner initial stream t
  rw [hReplay]
  exact hApproxAt.1

/-- Element-generation depends only on the represented finite collection,
not on its indexing. -/
theorem incrementallyElementGenerable_of_range_eq
    {langs raw : Fin (N + 1) → Set ℕ}
    (hRange : Set.range langs = Set.range raw)
    (hGen : IncrementallyElementGenerable langs) :
    IncrementallyElementGenerable raw := by
  obtain ⟨G, initial, hG⟩ := hGen
  refine ⟨G, initial, ?_⟩
  intro target stream hP
  have hRawMem : raw target ∈ Set.range raw := ⟨target, rfl⟩
  rw [← hRange] at hRawMem
  obtain ⟨i, hi⟩ := hRawMem
  have hP' : GenLimit.Generic.Presents stream (langs i) := by
    simpa [hi] using hP
  have hRun := hG i stream hP'
  simpa [hi] using hRun

/-- Appendix theorem: every nonempty finite collection of infinite
languages admits an incremental element-based generator. -/
theorem incremental_element_generation
    (raw : Fin (N + 1) → Set ℕ)
    (hInfinite : ∀ i, (raw i).Infinite) :
    IncrementallyElementGenerable raw := by
  obtain ⟨langs, hRange, hApprox⟩ :=
    theorem_5_2 raw hInfinite
  have hLangsInfinite : ∀ i, (langs i).Infinite := by
    intro i
    have hMem : langs i ∈ Set.range langs := ⟨i, rfl⟩
    rw [hRange] at hMem
    obtain ⟨j, hj⟩ := hMem
    simpa [hj] using hInfinite j
  apply incrementallyElementGenerable_of_range_eq hRange
  exact
    incremental_element_generation_of_approximate_identification
      langs hLangsInfinite hApprox

end CodingCompilation

end GenLimit.BoundedMemory
