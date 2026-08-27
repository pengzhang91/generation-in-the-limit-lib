import GenLimit.Paper15_PartialEnumeration.AlgorithmOneRun
import GenLimit.Paper15_PartialEnumeration.OrderedOccurrences
import GenLimit.Core.OrderedDensity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# The Section 3 warm-up priority-list run

This file gives an executable mathematical state machine for the priority
list and token construction preceding Lemma 3.2.  In particular, the state
records every string already used by either player, so "unused" and the
largest string used so far are well-defined even when the adversary repeats
an input.

The paper's downward-transition token assignment is commented out in the
pinned v1 source.  `algorithmOneAggressiveGuess` uses token `2` there: the
commented formula is `2 (j-i)`, and the preceding paragraph says that this
transition advances from position `i` to `i+1`.  The incomparable branch is
parameterized by `IncomparableChoice`; this isolates the source's separate
choice of a common predecessor without making Lemma 3.2 depend on how that
finite-time choice is implemented.

The main proof below does not assume that an invalid legacy queue somehow
vanishes.  It proves this.  A legacy string `x` that remained queued forever
would force an infinite injective tail of outputs into the finite interval
`{0, ..., x}`, a contradiction.  This is the missing compactness step in the
paper's proof of Lemma 3.2.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration
namespace WarmupPriority

/-- One aggressive action: guess an infinite language and spend a finite
number of tokens beyond its first member above the current used maximum. -/
structure AggressiveGuess where
  language : Language
  infinite : language.Infinite
  token : ℕ

/-- The first member of an infinite language strictly above `bound`. -/
noncomputable def nextAbove
    (L : Language) (hL : L.Infinite) (bound : ℕ) : ℕ := by
  classical
  exact Nat.find (hL.exists_gt bound)

theorem nextAbove_spec
    (L : Language) (hL : L.Infinite) (bound : ℕ) :
    nextAbove L hL bound ∈ L ∧ bound < nextAbove L hL bound := by
  classical
  exact Nat.find_spec (hL.exists_gt bound)

/-- Starting with the first language member above `bound`, advance `token`
more times.  Thus token zero still inserts through the paper's `w'`. -/
noncomputable def tokenCutoff
    (L : Language) (hL : L.Infinite) (bound : ℕ) : ℕ → ℕ
  | 0 => nextAbove L hL bound
  | token + 1 =>
      nextAbove L hL (tokenCutoff L hL bound token)

theorem tokenCutoff_mem
    (L : Language) (hL : L.Infinite) (bound token : ℕ) :
    tokenCutoff L hL bound token ∈ L := by
  induction token with
  | zero => exact (nextAbove_spec L hL bound).1
  | succ token _ =>
      exact
        (nextAbove_spec L hL
          (tokenCutoff L hL bound token)).1

theorem bound_lt_tokenCutoff
    (L : Language) (hL : L.Infinite) (bound token : ℕ) :
    bound < tokenCutoff L hL bound token := by
  induction token with
  | zero => exact (nextAbove_spec L hL bound).2
  | succ token ih =>
      exact ih.trans
        (nextAbove_spec L hL
          (tokenCutoff L hL bound token)).2

/-- All unused guessed-language strings through `w'` and the next `token`
guessed-language strings. -/
noncomputable def tokenWindow
    (guess : AggressiveGuess)
    (used : Finset ℕ) (hused : used.Nonempty) : Finset ℕ := by
  classical
  exact
    (Finset.range
      (tokenCutoff guess.language guess.infinite
        (used.max' hused) guess.token + 1)).filter
      fun x => x ∈ guess.language ∧ x ∉ used

@[simp] theorem mem_tokenWindow
    {guess : AggressiveGuess}
    {used : Finset ℕ} {hused : used.Nonempty} {x : ℕ} :
    x ∈ tokenWindow guess used hused ↔
      x ≤ tokenCutoff guess.language guess.infinite
          (used.max' hused) guess.token ∧
        x ∈ guess.language ∧ x ∉ used := by
  classical
  simp [tokenWindow, Nat.lt_succ_iff]

/-- The endpoint of a token window is fresh because it lies strictly above
the largest used string. -/
theorem tokenCutoff_not_mem_used
    (guess : AggressiveGuess)
    (used : Finset ℕ) (hused : used.Nonempty) :
    tokenCutoff guess.language guess.infinite
        (used.max' hused) guess.token ∉ used := by
  intro hmem
  have hle := Finset.le_max' used _ hmem
  have hlt := bound_lt_tokenCutoff guess.language guess.infinite
    (used.max' hused) guess.token
  omega

/-- Every aggressive insertion is nonempty: its cutoff itself is inserted. -/
theorem tokenCutoff_mem_tokenWindow
    (guess : AggressiveGuess)
    (used : Finset ℕ) (hused : used.Nonempty) :
    tokenCutoff guess.language guess.infinite
        (used.max' hused) guess.token ∈
      tokenWindow guess used hused := by
  exact mem_tokenWindow.mpr
    ⟨le_rfl, tokenCutoff_mem guess.language guess.infinite
      (used.max' hused) guess.token,
      tokenCutoff_not_mem_used guess used hused⟩

/-- State immediately before one adversary/generator round. -/
structure State where
  /-- Every earlier adversary input and generator output. -/
  used : Finset ℕ
  /-- Unused strings retaining priority from aggressive guesses. -/
  queue : Finset ℕ
  /-- The preceding generator output, absent only initially. -/
  previousOutput : Option ℕ

def State.initial : State := ⟨∅, ∅, none⟩

/-- Purge all used strings and, when aggressive, insert the finite token
window. -/
noncomputable def priorityAtStep
    (state : State) (input : ℕ)
    (guess : Option AggressiveGuess) : Finset ℕ := by
  classical
  let usedNow := insert input state.used
  let oldQueue := state.queue \ usedNow
  exact
    match guess with
    | none => oldQueue
    | some aggressive =>
        oldQueue ∪
          tokenWindow aggressive usedNow
            ⟨input, Finset.mem_insert_self input state.used⟩

/-- Candidate condition for the next generator output. -/
def OutputCandidate
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (x : ℕ) : Prop :=
  x ∉ used ∧ (x ∈ preferred ∨ x ∈ current)

theorem outputCandidate_exists
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hCurrent : current.Infinite) :
    ∃ x, OutputCandidate preferred current used x := by
  obtain ⟨x, hxCurrent, hxFresh⟩ :=
    hCurrent.exists_notMem_finset used
  exact ⟨x, hxFresh, Or.inr hxCurrent⟩

/-- The least unused member of the priority queue union the current
identified language.  This is the comparison rule in Cases 2 and 5. -/
noncomputable def leastOutput
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hCurrent : current.Infinite) : ℕ := by
  classical
  exact Nat.find (outputCandidate_exists preferred current used hCurrent)

theorem leastOutput_spec
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hCurrent : current.Infinite) :
    OutputCandidate preferred current used
      (leastOutput preferred current used hCurrent) := by
  classical
  exact Nat.find_spec
    (outputCandidate_exists preferred current used hCurrent)

theorem leastOutput_min
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hCurrent : current.Infinite)
    {x : ℕ} (hx : OutputCandidate preferred current used x) :
    leastOutput preferred current used hCurrent ≤ x := by
  classical
  exact Nat.find_min'
    (outputCandidate_exists preferred current used hCurrent) hx

/-- The output emitted by one normalized warm-up step. -/
noncomputable def emittedAtStep
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (guess : Option AggressiveGuess) : ℕ :=
  leastOutput (priorityAtStep state input guess) current
    (insert input state.used) hCurrent

/-- One normalized warm-up step. -/
noncomputable def step
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (guess : Option AggressiveGuess) : State := by
  classical
  let usedNow := insert input state.used
  let preferred := priorityAtStep state input guess
  let output := leastOutput preferred current usedNow hCurrent
  exact ⟨insert output usedNow, preferred.erase output, some output⟩

theorem emittedAtStep_fresh
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (guess : Option AggressiveGuess) :
    emittedAtStep state input current hCurrent guess ∉
      insert input state.used :=
  (leastOutput_spec (priorityAtStep state input guess) current
    (insert input state.used) hCurrent).1

theorem emittedAtStep_mem_priority_or_current
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (guess : Option AggressiveGuess) :
    emittedAtStep state input current hCurrent guess ∈
        priorityAtStep state input guess ∨
      emittedAtStep state input current hCurrent guess ∈ current :=
  (leastOutput_spec (priorityAtStep state input guess) current
    (insert input state.used) hCurrent).2

theorem mem_priorityAtStep_fresh
    (state : State) (input : ℕ)
    (guess : Option AggressiveGuess) {x : ℕ}
    (hx : x ∈ priorityAtStep state input guess) :
    x ∉ insert input state.used := by
  classical
  cases guess with
  | none =>
      have hxOld : x ∈ state.queue \ insert input state.used := by
        simpa [priorityAtStep] using hx
      exact (Finset.mem_sdiff.mp hxOld).2
  | some aggressive =>
      have hxParts :
          x ∈ state.queue \ insert input state.used ∨
            x ∈ tokenWindow aggressive (insert input state.used)
              ⟨input, Finset.mem_insert_self input state.used⟩ := by
        simpa [priorityAtStep] using hx
      rcases hxParts with hxOld | hxNew
      · exact (Finset.mem_sdiff.mp hxOld).2
      · exact (mem_tokenWindow.mp hxNew).2.2

theorem tokenWindow_subset_priorityAtStep
    (state : State) (input : ℕ)
    (aggressive : AggressiveGuess) :
    ↑(tokenWindow aggressive (insert input state.used)
        ⟨input, Finset.mem_insert_self input state.used⟩) ⊆
      ↑(priorityAtStep state input (some aggressive)) := by
  classical
  intro x hx
  simp only [priorityAtStep]
  exact Finset.mem_union_right _ hx

theorem emittedAtStep_le_candidate
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (guess : Option AggressiveGuess) {x : ℕ}
    (hxFresh : x ∉ insert input state.used)
    (hxAvailable :
      x ∈ priorityAtStep state input guess ∨ x ∈ current) :
    emittedAtStep state input current hCurrent guess ≤ x :=
  leastOutput_min (priorityAtStep state input guess) current
    (insert input state.used) hCurrent ⟨hxFresh, hxAvailable⟩

/-- Membership in the next queue witnesses that the current output was no
larger.  This is the operational fact used to drain legacy queue entries. -/
theorem emittedAtStep_le_of_mem_step_queue
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (guess : Option AggressiveGuess) {x : ℕ}
    (hx : x ∈ (step state input current hCurrent guess).queue) :
    emittedAtStep state input current hCurrent guess ≤ x := by
  have hxPriority : x ∈ priorityAtStep state input guess := by
    change
      x ∈
        (priorityAtStep state input guess).erase
          (emittedAtStep state input current hCurrent guess) at hx
    exact (Finset.mem_erase.mp hx).2
  exact emittedAtStep_le_candidate state input current hCurrent guess
    (mem_priorityAtStep_fresh state input guess hxPriority)
    (Or.inl hxPriority)

/-- On an aggressive round whose guessed language contains the current
identified set, the normalized least-union rule really does emit from the
priority list, exactly as the source instructs. -/
theorem emittedAtStep_mem_priority_of_aggressive_superset
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (aggressive : AggressiveGuess)
    (hSubset : current ⊆ aggressive.language) :
    emittedAtStep state input current hCurrent (some aggressive) ∈
      priorityAtStep state input (some aggressive) := by
  let usedNow := insert input state.used
  have husedNow : usedNow.Nonempty :=
    ⟨input, Finset.mem_insert_self input state.used⟩
  let cutoff := tokenCutoff aggressive.language aggressive.infinite
    (usedNow.max' husedNow) aggressive.token
  have hCutoffWindow :
      cutoff ∈ tokenWindow aggressive usedNow husedNow := by
    exact tokenCutoff_mem_tokenWindow aggressive usedNow husedNow
  have hCutoffPriority :
      cutoff ∈ priorityAtStep state input (some aggressive) := by
    exact tokenWindow_subset_priorityAtStep state input aggressive
      (by simpa [usedNow] using hCutoffWindow)
  have hOutputLe :
      emittedAtStep state input current hCurrent (some aggressive) ≤
        cutoff :=
    emittedAtStep_le_candidate state input current hCurrent
      (some aggressive)
      (mem_priorityAtStep_fresh state input (some aggressive)
        hCutoffPriority)
      (Or.inl hCutoffPriority)
  rcases emittedAtStep_mem_priority_or_current state input current
      hCurrent (some aggressive) with hPriority | hCurrentMem
  · exact hPriority
  · apply tokenWindow_subset_priorityAtStep state input aggressive
    apply mem_tokenWindow.mpr
    refine ⟨?_, hSubset hCurrentMem, ?_⟩
    · simpa [cutoff, usedNow] using hOutputLe
    · exact emittedAtStep_fresh state input current hCurrent
        (some aggressive)

/-- The queue and used set are disjoint after every step. -/
theorem step_queue_fresh
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (guess : Option AggressiveGuess) :
    Disjoint (step state input current hCurrent guess).queue
      (step state input current hCurrent guess).used := by
  classical
  rw [Finset.disjoint_left]
  intro x hxQueue hxUsed
  change
    x ∈
      (priorityAtStep state input guess).erase
        (emittedAtStep state input current hCurrent guess) at hxQueue
  change
    x ∈ insert
      (emittedAtStep state input current hCurrent guess)
      (insert input state.used) at hxUsed
  rcases Finset.mem_erase.mp hxQueue with ⟨hxNe, hxPriority⟩
  rcases Finset.mem_insert.mp hxUsed with hxOutput | hxUsedNow
  · exact hxNe hxOutput
  · exact
      (mem_priorityAtStep_fresh state input guess hxPriority) hxUsedNow

/-! ## Recursive execution -/

/-- State immediately before round `t`. -/
noncomputable def runState
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess) : ℕ → State
  | 0 => State.initial
  | t + 1 =>
      step (runState input current hCurrent guess t)
        (input t) (current t) (hCurrent t) (guess t)

/-- The emitted output sequence of a recursive warm-up run. -/
noncomputable def runOutput
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess) (t : ℕ) : ℕ :=
  emittedAtStep (runState input current hCurrent guess t)
    (input t) (current t) (hCurrent t) (guess t)

@[simp] theorem runState_zero
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess) :
    runState input current hCurrent guess 0 = State.initial := rfl

@[simp] theorem runState_succ
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess) (t : ℕ) :
    runState input current hCurrent guess (t + 1) =
      step (runState input current hCurrent guess t)
        (input t) (current t) (hCurrent t) (guess t) := rfl

theorem runOutput_fresh
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess) (t : ℕ) :
    runOutput input current hCurrent guess t ∉
      insert (input t) (runState input current hCurrent guess t).used :=
  emittedAtStep_fresh
    (runState input current hCurrent guess t)
    (input t) (current t) (hCurrent t) (guess t)

/-- In a reachable run, `used` consists exactly of earlier adversary inputs
and earlier generator outputs. -/
theorem mem_runState_used_iff
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess) (t x : ℕ) :
    x ∈ (runState input current hCurrent guess t).used ↔
      (∃ s, s < t ∧ input s = x) ∨
        ∃ s, s < t ∧ runOutput input current hCurrent guess s = x := by
  induction t with
  | zero => simp [runState, State.initial]
  | succ t ih =>
      rw [runState_succ]
      change
        x ∈ insert
            (runOutput input current hCurrent guess t)
            (insert (input t)
              (runState input current hCurrent guess t).used) ↔
          (∃ s, s < t + 1 ∧ input s = x) ∨
            ∃ s, s < t + 1 ∧
              runOutput input current hCurrent guess s = x
      simp only [Finset.mem_insert]
      constructor
      · rintro (houtput | hinput | hold)
        · exact Or.inr ⟨t, Nat.lt_succ_self t, houtput.symm⟩
        · exact Or.inl ⟨t, Nat.lt_succ_self t, hinput.symm⟩
        · rcases ih.mp hold with
            ⟨s, hs, hvalue⟩ | ⟨s, hs, hvalue⟩
          · exact Or.inl ⟨s, hs.trans_le (Nat.le_succ t), hvalue⟩
          · exact Or.inr ⟨s, hs.trans_le (Nat.le_succ t), hvalue⟩
      · rintro (⟨s, hs, hvalue⟩ | ⟨s, hs, hvalue⟩)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
          · exact Or.inr (Or.inr
              (ih.mpr (Or.inl ⟨s, hs, hvalue⟩)))
          · exact Or.inr (Or.inl hvalue.symm)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
          · exact Or.inr (Or.inr
              (ih.mpr (Or.inr ⟨s, hs, hvalue⟩)))
          · exact Or.inl hvalue.symm

/-- The generator never repeats an output. -/
theorem runOutput_injective
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess) :
    Function.Injective (runOutput input current hCurrent guess) := by
  intro s t heq
  rcases lt_trichotomy s t with hst | hst | hst
  · have hused :
        runOutput input current hCurrent guess s ∈
          (runState input current hCurrent guess t).used :=
      (mem_runState_used_iff input current hCurrent guess t _).mpr
        (Or.inr ⟨s, hst, rfl⟩)
    have hfresh := runOutput_fresh input current hCurrent guess t
    exfalso
    apply hfresh
    exact Finset.mem_insert.mpr
      (Or.inr (by simpa [heq] using hused))
  · exact hst
  · have hused :
        runOutput input current hCurrent guess t ∈
          (runState input current hCurrent guess s).used :=
      (mem_runState_used_iff input current hCurrent guess s _).mpr
        (Or.inr ⟨t, hst, rfl⟩)
    have hfresh := runOutput_fresh input current hCurrent guess s
    exfalso
    apply hfresh
    exact Finset.mem_insert.mpr
      (Or.inr (by simpa [heq] using hused))

theorem runOutput_le_of_mem_next_queue
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess) (t x : ℕ)
    (hx : x ∈ (runState input current hCurrent guess (t + 1)).queue) :
    runOutput input current hCurrent guess t ≤ x := by
  exact emittedAtStep_le_of_mem_step_queue
    (runState input current hCurrent guess t)
    (input t) (current t) (hCurrent t) (guess t)
    (by simpa using hx)

/-! ## The legacy-queue drainage argument -/

/-- Once all new aggressive guesses are target-valid, an invalid string in
the next queue must already have been in the preceding queue. -/
theorem invalid_queue_member_origin
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess)
    (K : Language) (T t x : ℕ)
    (hGuessValid :
      ∀ u, T ≤ u → ∀ aggressive,
        guess u = some aggressive → aggressive.language ⊆ K)
    (ht : T ≤ t) (hxK : x ∉ K)
    (hxNext :
      x ∈ (runState input current hCurrent guess (t + 1)).queue) :
    x ∈ (runState input current hCurrent guess t).queue := by
  have hxPriority :
      x ∈ priorityAtStep
        (runState input current hCurrent guess t) (input t) (guess t) := by
    change
      x ∈
        (priorityAtStep
          (runState input current hCurrent guess t)
          (input t) (guess t)).erase
          (runOutput input current hCurrent guess t) at hxNext
    exact (Finset.mem_erase.mp hxNext).2
  classical
  cases hguess : guess t with
  | none =>
      have hxOld :
          x ∈ (runState input current hCurrent guess t).queue \
            insert (input t)
              (runState input current hCurrent guess t).used := by
        simpa [priorityAtStep, hguess] using hxPriority
      exact (Finset.mem_sdiff.mp hxOld).1
  | some aggressive =>
      have hxParts :
          x ∈ (runState input current hCurrent guess t).queue \
              insert (input t)
                (runState input current hCurrent guess t).used ∨
            x ∈ tokenWindow aggressive
              (insert (input t)
                (runState input current hCurrent guess t).used)
              ⟨input t,
                Finset.mem_insert_self (input t)
                  (runState input current hCurrent guess t).used⟩ := by
        simpa [priorityAtStep, hguess] using hxPriority
      rcases hxParts with hxOld | hxNew
      · exact (Finset.mem_sdiff.mp hxOld).1
      · exfalso
        apply hxK
        exact hGuessValid t ht aggressive hguess
          (mem_tokenWindow.mp hxNew).2.1

/-- Invalid queue membership propagates backward to the validity threshold. -/
theorem invalid_queue_member_backward
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess)
    (K : Language) (T x : ℕ)
    (hGuessValid :
      ∀ u, T ≤ u → ∀ aggressive,
        guess u = some aggressive → aggressive.language ⊆ K)
    (hxK : x ∉ K) {s t : ℕ}
    (hTs : T ≤ s) (hst : s ≤ t)
    (hx : x ∈ (runState input current hCurrent guess t).queue) :
    x ∈ (runState input current hCurrent guess s).queue := by
  induction t, hst using Nat.le_induction with
  | base => exact hx
  | @succ t hst ih =>
      apply ih
      exact invalid_queue_member_origin input current hCurrent guess
        K T t x hGuessValid (le_trans hTs hst) hxK hx

/-- Every target-invalid queue entry is eventually absent.  This is not a
fairness assumption: least-output priority plus output injectivity proves it. -/
theorem invalid_queue_member_eventually_absent
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess)
    (K : Language) (T x : ℕ)
    (hGuessValid :
      ∀ u, T ≤ u → ∀ aggressive,
        guess u = some aggressive → aggressive.language ⊆ K)
    (hxK : x ∉ K) :
    ∃ U, ∀ t, U ≤ t →
      x ∉ (runState input current hCurrent guess t).queue := by
  classical
  by_contra hNo
  push_neg at hNo
  have hAlways :
      ∀ n,
        x ∈ (runState input current hCurrent guess (T + n)).queue := by
    intro n
    obtain ⟨t, ht, hxt⟩ := hNo (T + n)
    exact invalid_queue_member_backward input current hCurrent guess
      K T x hGuessValid hxK (by omega) ht hxt
  let tailOutput : ℕ → ℕ :=
    fun n => runOutput input current hCurrent guess (T + n)
  have hTailInjective : Function.Injective tailOutput := by
    intro a b hab
    apply Nat.add_left_cancel
    exact runOutput_injective input current hCurrent guess hab
  have hTailBound : Set.range tailOutput ⊆ Set.Iic x := by
    rintro y ⟨n, rfl⟩
    exact runOutput_le_of_mem_next_queue
      input current hCurrent guess (T + n) x
      (by simpa [Nat.add_assoc] using hAlways (n + 1))
  have hTailInfinite : (Set.range tailOutput).Infinite :=
    Set.infinite_range_of_injective hTailInjective
  exact hTailInfinite ((Set.finite_Iic x).subset hTailBound)

/-- If the old queue and the current aggressive guess are target-valid,
then the updated priority queue is target-valid. -/
theorem priorityAtStep_subset
    (state : State) (input : ℕ)
    (guess : Option AggressiveGuess) (K : Language)
    (hQueue : ↑state.queue ⊆ K)
    (hGuess : ∀ aggressive, guess = some aggressive →
      aggressive.language ⊆ K) :
    ↑(priorityAtStep state input guess) ⊆ K := by
  classical
  intro x hx
  cases hguess : guess with
  | none =>
      have hxOld : x ∈ state.queue \ insert input state.used := by
        simpa [priorityAtStep, hguess] using hx
      exact hQueue (Finset.mem_sdiff.mp hxOld).1
  | some aggressive =>
      have hxParts :
          x ∈ state.queue \ insert input state.used ∨
            x ∈ tokenWindow aggressive (insert input state.used)
              ⟨input, Finset.mem_insert_self input state.used⟩ := by
        simpa [priorityAtStep, hguess] using hx
      rcases hxParts with hxOld | hxNew
      · exact hQueue (Finset.mem_sdiff.mp hxOld).1
      · exact hGuess aggressive hguess
          (mem_tokenWindow.mp hxNew).2.1

/-- Finitely many invalid legacy entries can be cleared uniformly. -/
theorem runQueue_eventually_subset
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess)
    (K : Language) (T : ℕ)
    (hGuessValid :
      ∀ u, T ≤ u → ∀ aggressive,
        guess u = some aggressive → aggressive.language ⊆ K) :
    ∃ U, T ≤ U ∧ ∀ t, U ≤ t →
      ↑(runState input current hCurrent guess t).queue ⊆ K := by
  classical
  let legacyBad : Finset ℕ :=
    (runState input current hCurrent guess T).queue.filter
      fun x => x ∉ K
  have hUniform :
      ∀ S : Finset ℕ, (∀ x ∈ S, x ∉ K) →
        ∃ U, ∀ t, U ≤ t → ∀ x ∈ S,
          x ∉ (runState input current hCurrent guess t).queue := by
    intro S hBad
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨0, by simp⟩
    | @insert x S hxS ih =>
        have hxK : x ∉ K :=
          hBad x (Finset.mem_insert_self x S)
        have hSBad : ∀ y ∈ S, y ∉ K := by
          intro y hy
          exact hBad y (Finset.mem_insert_of_mem hy)
        obtain ⟨Ux, hUx⟩ :=
          invalid_queue_member_eventually_absent
            input current hCurrent guess K T x hGuessValid hxK
        obtain ⟨US, hUS⟩ := ih hSBad
        refine ⟨max Ux US, ?_⟩
        intro t ht y hy
        rcases Finset.mem_insert.mp hy with rfl | hyS
        · exact hUx t (le_trans (Nat.le_max_left _ _) ht)
        · exact hUS t (le_trans (Nat.le_max_right _ _) ht) y hyS
  have hLegacyBad : ∀ x ∈ legacyBad, x ∉ K := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  obtain ⟨U₀, hU₀⟩ := hUniform legacyBad hLegacyBad
  let U := max T U₀
  refine ⟨U, Nat.le_max_left _ _, ?_⟩
  intro t ht x hxQueue
  by_contra hxK
  have hxAtT :
      x ∈ (runState input current hCurrent guess T).queue :=
    invalid_queue_member_backward input current hCurrent guess
      K T x hGuessValid hxK (le_rfl) (le_trans (Nat.le_max_left _ _) ht)
      hxQueue
  have hxLegacy : x ∈ legacyBad := by
    exact Finset.mem_filter.mpr ⟨hxAtT, hxK⟩
  exact hU₀ t (le_trans (Nat.le_max_right _ _) ht) x hxLegacy hxQueue

/-- Generic Lemma 3.2 engine: eventual validity of current identified sets
and aggressive guesses implies eventual validity of actual emitted outputs. -/
theorem runOutput_eventually_mem
    (input : ℕ → ℕ) (current : ℕ → Language)
    (hCurrent : ∀ t, (current t).Infinite)
    (guess : ℕ → Option AggressiveGuess)
    (K : Language) (T : ℕ)
    (hCurrentValid : ∀ t, T ≤ t → current t ⊆ K)
    (hGuessValid :
      ∀ t, T ≤ t → ∀ aggressive,
        guess t = some aggressive → aggressive.language ⊆ K) :
    ∃ U, ∀ t, U ≤ t →
      runOutput input current hCurrent guess t ∈ K := by
  obtain ⟨U, hTU, hQueue⟩ :=
    runQueue_eventually_subset input current hCurrent guess
      K T hGuessValid
  refine ⟨U, ?_⟩
  intro t ht
  rcases emittedAtStep_mem_priority_or_current
      (runState input current hCurrent guess t)
      (input t) (current t) (hCurrent t) (guess t) with
    hPriority | hCurrentMem
  · exact priorityAtStep_subset
      (runState input current hCurrent guess t) (input t) (guess t) K
      (hQueue t ht)
      (fun aggressive hEq =>
        hGuessValid t (le_trans hTU ht) aggressive hEq)
      hPriority
  · exact hCurrentValid t (le_trans hTU ht) hCurrentMem

/-! ## Wiring to the concrete Algorithm 1 run -/

/-- The source separately selects a common predecessor in the incomparable
transition branch.  Lemma 2.5 says that branch occurs only finitely often,
so Lemma 3.2 is valid for every such finite-prefix choice. -/
abbrev IncomparableChoice := ℕ → Option AggressiveGuess

/-- Old-chain positions which denote a positive common predecessor of both
identified chain positions.  All quantification is over finite prefixes. -/
noncomputable def commonPredecessorOldIndices
    (old new : IdentifiedIntersectionState) : Finset ℕ := by
  classical
  exact
    (Finset.range (old.chosenIndex + 1)).filter fun i =>
      0 < i ∧
        ∃ j, 0 < j ∧ j ≤ new.chosenIndex ∧
          old.chain i = new.chain j

@[simp] theorem mem_commonPredecessorOldIndices
    {old new : IdentifiedIntersectionState} {i : ℕ} :
    i ∈ commonPredecessorOldIndices old new ↔
      0 < i ∧ i ≤ old.chosenIndex ∧
        ∃ j, 0 < j ∧ j ≤ new.chosenIndex ∧
          old.chain i = new.chain j := by
  classical
  simp only [commonPredecessorOldIndices, Finset.mem_filter,
    Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hiLe, hiPos, hj⟩
    exact ⟨hiPos, hiLe, hj⟩
  · rintro ⟨hiPos, hiLe, hj⟩
    exact ⟨hiLe, hiPos, hj⟩

/-- The deepest old-chain position representing a common predecessor. -/
noncomputable def commonPredecessorOldIndex
    (old new : IdentifiedIntersectionState)
    (h : (commonPredecessorOldIndices old new).Nonempty) : ℕ :=
  (commonPredecessorOldIndices old new).max' h

theorem commonPredecessorOldIndex_mem
    (old new : IdentifiedIntersectionState)
    (h : (commonPredecessorOldIndices old new).Nonempty) :
    commonPredecessorOldIndex old new h ∈
      commonPredecessorOldIndices old new :=
  Finset.max'_mem _ h

theorem commonPredecessorOldIndex_is_deepest
    (old new : IdentifiedIntersectionState)
    (h : (commonPredecessorOldIndices old new).Nonempty)
    {i : ℕ} (hi : i ∈ commonPredecessorOldIndices old new) :
    i ≤ commonPredecessorOldIndex old new h :=
  Finset.le_max' _ _ hi

theorem commonPredecessorNewIndex_exists
    (old new : IdentifiedIntersectionState)
    (h : (commonPredecessorOldIndices old new).Nonempty) :
    ∃ j, 0 < j ∧ j ≤ new.chosenIndex ∧
      old.chain (commonPredecessorOldIndex old new h) = new.chain j :=
  (mem_commonPredecessorOldIndices.mp
    (commonPredecessorOldIndex_mem old new h)).2.2

/-- A matching position in the new chain for the selected common set. -/
noncomputable def commonPredecessorNewIndex
    (old new : IdentifiedIntersectionState)
    (h : (commonPredecessorOldIndices old new).Nonempty) : ℕ := by
  classical
  exact Nat.find (commonPredecessorNewIndex_exists old new h)

theorem commonPredecessorNewIndex_spec
    (old new : IdentifiedIntersectionState)
    (h : (commonPredecessorOldIndices old new).Nonempty) :
    0 < commonPredecessorNewIndex old new h ∧
      commonPredecessorNewIndex old new h ≤ new.chosenIndex ∧
      old.chain (commonPredecessorOldIndex old new h) =
        new.chain (commonPredecessorNewIndex old new h) := by
  classical
  exact Nat.find_spec (commonPredecessorNewIndex_exists old new h)

/-- The source's incomparable-branch choice.  The maximal old position is
minimal under set inclusion because each chain is descending.  Its token is
twice the distance from the matching new-chain position to the new cursor. -/
noncomputable def commonPredecessorGuess
    (old new : IdentifiedIntersectionState)
    (hOldInfinite : old.identified.Infinite) : Option AggressiveGuess := by
  classical
  if h : (commonPredecessorOldIndices old new).Nonempty then
    let i := commonPredecessorOldIndex old new h
    let j := commonPredecessorNewIndex old new h
    have hiLe : i ≤ old.chosenIndex :=
      (mem_commonPredecessorOldIndices.mp
        (commonPredecessorOldIndex_mem old new h)).2.1
    exact some
      ⟨old.chain i,
        hOldInfinite.mono (old.descending hiLe),
        2 * (new.chosenIndex - j)⟩
  else
    exact none

/-- A selected incomparable fallback is a common superset of both current
identified sets, and is minimal among all common predecessor positions in
the old chain. -/
theorem commonPredecessorGuess_spec
    (old new : IdentifiedIntersectionState)
    (hOldInfinite : old.identified.Infinite)
    (aggressive : AggressiveGuess)
    (hGuess : commonPredecessorGuess old new hOldInfinite = some aggressive) :
    old.identified ⊆ aggressive.language ∧
      new.identified ⊆ aggressive.language ∧
      ∃ h : (commonPredecessorOldIndices old new).Nonempty,
        aggressive.language =
            old.chain (commonPredecessorOldIndex old new h) ∧
          aggressive.token =
            2 * (new.chosenIndex - commonPredecessorNewIndex old new h) ∧
          ∀ i, i ∈ commonPredecessorOldIndices old new →
            aggressive.language ⊆ old.chain i := by
  classical
  unfold commonPredecessorGuess at hGuess
  split at hGuess
  · rename_i h
    let i := commonPredecessorOldIndex old new h
    let j := commonPredecessorNewIndex old new h
    have hiData := mem_commonPredecessorOldIndices.mp
      (commonPredecessorOldIndex_mem old new h)
    have hjData := commonPredecessorNewIndex_spec old new h
    cases hGuess
    refine ⟨old.descending hiData.2.1, ?_, ⟨h, rfl, rfl, ?_⟩⟩
    · change
        new.identified ⊆
          old.chain (commonPredecessorOldIndex old new h)
      rw [hjData.2.2]
      exact new.descending hjData.2.1
    · intro k hk
      exact old.descending
        (commonPredecessorOldIndex_is_deepest old new h hk)
  · simp at hGuess

/-- A normalized common-predecessor choice for every incomparable transition
of the concrete Algorithm 1 trace.  It is source-motivated rather than a
literal transcription because the implementation uses raw stuttering chain
positions. -/
noncomputable def sourceIncomparableChoice
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite) : IncomparableChoice :=
  fun t =>
    commonPredecessorGuess
      (algorithmOneState C stream t)
      (algorithmOneState C stream (t + 1))
      (algorithmOne_identified_infinite hLanguagesInfinite t)

/-- Source Cases 2--5, driven by the concrete `algorithmOneState` run.

* equal identified sets: no aggressive guess;
* strict downward move: guess the old set with repaired token `2`;
* strict upward move: guess the new set with source token `2`;
* incomparable move: use the independently supplied source choice.
-/
noncomputable def algorithmOneAggressiveGuess
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) (t : ℕ) :
    Option AggressiveGuess := by
  classical
  let old := (algorithmOneState C stream t).identified
  let new := (algorithmOneState C stream (t + 1)).identified
  exact
    if hEq : new = old then none
    else if hDown : new ⊆ old then
      some ⟨old, algorithmOne_identified_infinite
        hLanguagesInfinite t, 2⟩
    else if hUp : old ⊆ new then
      some ⟨new, algorithmOne_identified_infinite
        hLanguagesInfinite (t + 1), 2⟩
    else incomparable t

/-- At a comparable transition whose endpoints are target-valid, every
aggressive set selected by the concrete schedule is target-valid.  The
arbitrary incomparable-prefix choice is unreachable in these hypotheses. -/
theorem algorithmOneAggressiveGuess_subset_of_comparable
    {C : LanguageFamily} {stream : ℕ → ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice)
    (K : Language) (t : ℕ)
    (hOld : (algorithmOneState C stream t).identified ⊆ K)
    (hNew :
      (algorithmOneState C stream (t + 1)).identified ⊆ K)
    (hComparable :
      (algorithmOneState C stream t).identified ⊆
          (algorithmOneState C stream (t + 1)).identified ∨
        (algorithmOneState C stream (t + 1)).identified ⊆
          (algorithmOneState C stream t).identified)
    (aggressive : AggressiveGuess)
    (hGuess :
      algorithmOneAggressiveGuess C stream hLanguagesInfinite
        incomparable t = some aggressive) :
    aggressive.language ⊆ K := by
  classical
  simp only [algorithmOneAggressiveGuess] at hGuess
  split at hGuess
  · simp at hGuess
  · split at hGuess
    · cases hGuess
      exact hOld
    · split at hGuess
      · cases hGuess
        exact hNew
      · rcases hComparable with hUp | hDown
        · contradiction
        · contradiction

/-- In the eventual comparable regime, every aggressive set contains the
current identified language.  Consequently the normalized least-union
selector agrees with the source's instruction to output from the priority
list on aggressive rounds. -/
theorem algorithmOneAggressiveGuess_superset_of_current
    {C : LanguageFamily} {stream : ℕ → ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) (t : ℕ)
    (hComparable :
      (algorithmOneState C stream t).identified ⊆
          (algorithmOneState C stream (t + 1)).identified ∨
        (algorithmOneState C stream (t + 1)).identified ⊆
          (algorithmOneState C stream t).identified)
    (aggressive : AggressiveGuess)
    (hGuess :
      algorithmOneAggressiveGuess C stream hLanguagesInfinite
        incomparable t = some aggressive) :
    (algorithmOneState C stream t).identified ⊆
      aggressive.language := by
  classical
  let old := (algorithmOneState C stream t).identified
  let new := (algorithmOneState C stream (t + 1)).identified
  change old ⊆ aggressive.language
  change
    (if hEq : new = old then none
      else if hDown : new ⊆ old then
        some ⟨old, algorithmOne_identified_infinite
          hLanguagesInfinite t, 2⟩
      else if hUp : old ⊆ new then
        some ⟨new, algorithmOne_identified_infinite
          hLanguagesInfinite (t + 1), 2⟩
      else incomparable t) = some aggressive at hGuess
  by_cases hEq : new = old
  · simp [hEq] at hGuess
  by_cases hDown : new ⊆ old
  · simp [hEq, hDown] at hGuess
    cases hGuess
    exact Set.Subset.rfl
  by_cases hUp : old ⊆ new
  · simp [hEq, hDown, hUp] at hGuess
    cases hGuess
    exact hUp
  rcases hComparable with hOldNew | hNewOld
  · exact (hUp hOldNew).elim
  · exact (hDown hNewOld).elim

/-- The concrete priority-list state immediately before round `t`. -/
noncomputable def algorithmOneWarmupState
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) : ℕ → State :=
  runState stream
    (fun t => (algorithmOneState C stream t).identified)
    (algorithmOne_identified_infinite hLanguagesInfinite)
    (algorithmOneAggressiveGuess C stream hLanguagesInfinite incomparable)

/-- The actual output sequence of the Section 3 warm-up state machine. -/
noncomputable def algorithmOneWarmupOutput
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) : ℕ → ℕ :=
  runOutput stream
    (fun t => (algorithmOneState C stream t).identified)
    (algorithmOne_identified_infinite hLanguagesInfinite)
    (algorithmOneAggressiveGuess C stream hLanguagesInfinite incomparable)

/-- Normalized/repaired warm-up state, including the minimal common
predecessor choice on incomparable transitions and the explicit downward
token-`2` repair of the commented-out source assignment. -/
noncomputable def sourceWarmupState
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite) : ℕ → State :=
  algorithmOneWarmupState C stream hLanguagesInfinite
    (sourceIncomparableChoice C stream hLanguagesInfinite)

/-- Output sequence of the normalized/repaired warm-up state machine. -/
noncomputable def sourceWarmupOutput
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite) : ℕ → ℕ :=
  algorithmOneWarmupOutput C stream hLanguagesInfinite
    (sourceIncomparableChoice C stream hLanguagesInfinite)

/-- The concrete warm-up run never repeats a generator output. -/
theorem algorithmOneWarmupOutput_injective
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) :
    Function.Injective
      (algorithmOneWarmupOutput C stream hLanguagesInfinite incomparable) :=
  runOutput_injective stream
    (fun t => (algorithmOneState C stream t).identified)
    (algorithmOne_identified_infinite hLanguagesInfinite)
    (algorithmOneAggressiveGuess C stream hLanguagesInfinite incomparable)

/-- On every comparable aggressive round, the concrete output is genuinely
drawn from the updated priority list. -/
theorem algorithmOneWarmupOutput_mem_priority_of_comparable_aggressive
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) (t : ℕ)
    (hComparable :
      (algorithmOneState C stream t).identified ⊆
          (algorithmOneState C stream (t + 1)).identified ∨
        (algorithmOneState C stream (t + 1)).identified ⊆
          (algorithmOneState C stream t).identified)
    (aggressive : AggressiveGuess)
    (hGuess :
      algorithmOneAggressiveGuess C stream hLanguagesInfinite
        incomparable t = some aggressive) :
    algorithmOneWarmupOutput C stream hLanguagesInfinite incomparable t ∈
      priorityAtStep
        (algorithmOneWarmupState C stream hLanguagesInfinite incomparable t)
        (stream t) (some aggressive) := by
  have hSubset := algorithmOneAggressiveGuess_superset_of_current
    hLanguagesInfinite incomparable t hComparable aggressive hGuess
  have hPriority := emittedAtStep_mem_priority_of_aggressive_superset
    (algorithmOneWarmupState C stream hLanguagesInfinite incomparable t)
    (stream t) (algorithmOneState C stream t).identified
    (algorithmOne_identified_infinite hLanguagesInfinite t)
    aggressive hSubset
  change
    emittedAtStep
      (algorithmOneWarmupState C stream hLanguagesInfinite incomparable t)
      (stream t) (algorithmOneState C stream t).identified
      (algorithmOne_identified_infinite hLanguagesInfinite t)
      (algorithmOneAggressiveGuess C stream hLanguagesInfinite
        incomparable t) ∈
      priorityAtStep
        (algorithmOneWarmupState C stream hLanguagesInfinite incomparable t)
        (stream t) (some aggressive)
  rw [hGuess]
  exact hPriority

/-- At every round the output is distinct from the current and every earlier
adversary input. -/
theorem algorithmOneWarmupOutput_not_mem_sample_succ
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) (t : ℕ) :
    algorithmOneWarmupOutput C stream hLanguagesInfinite incomparable t ∉
      sample stream (t + 1) := by
  intro hSample
  obtain ⟨s, hs, hValue⟩ := mem_sample_iff.mp hSample
  have hFresh := runOutput_fresh stream
    (fun u => (algorithmOneState C stream u).identified)
    (algorithmOne_identified_infinite hLanguagesInfinite)
    (algorithmOneAggressiveGuess C stream hLanguagesInfinite incomparable) t
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with hst | rfl
  · apply hFresh
    apply Finset.mem_insert.mpr
    apply Or.inr
    apply (mem_runState_used_iff stream
      (fun u => (algorithmOneState C stream u).identified)
      (algorithmOne_identified_infinite hLanguagesInfinite)
      (algorithmOneAggressiveGuess C stream hLanguagesInfinite incomparable)
      t _).mpr
    exact Or.inl ⟨s, hst, hValue⟩
  · apply hFresh
    exact Finset.mem_insert.mpr (Or.inl hValue.symm)

/-- Lemma 3.2 for the concrete Algorithm 1 selector and the real priority
run: after a finite time every emitted string belongs to the target
language.  No queue-clearance or fairness premise is assumed. -/
theorem lemma_3_2_eventual_validity
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z)
    (incomparable : IncomparableChoice) :
    ∃ T, ∀ t, T ≤ t →
      algorithmOneWarmupOutput C stream hLanguagesInfinite
        incomparable t ∈ C z := by
  obtain ⟨Tvalid, hValid⟩ :=
    algorithmOne_eventually_valid hP hE hEz
  obtain ⟨Tcompare, hCompare⟩ :=
    algorithmOne_eventually_comparable (z := z) hP hE
  let T := max Tvalid Tcompare
  have hCurrentValid :
      ∀ t, T ≤ t →
        (algorithmOneState C stream t).identified ⊆ C z := by
    intro t ht
    exact hValid t (le_trans (Nat.le_max_left _ _) ht)
  have hGuessValid :
      ∀ t, T ≤ t → ∀ aggressive,
        algorithmOneAggressiveGuess C stream hLanguagesInfinite
            incomparable t = some aggressive →
          aggressive.language ⊆ C z := by
    intro t ht aggressive hGuess
    apply algorithmOneAggressiveGuess_subset_of_comparable
      hLanguagesInfinite incomparable (C z) t
    · exact hCurrentValid t ht
    · exact hCurrentValid (t + 1) (by omega)
    · exact hCompare t
        (le_trans (Nat.le_max_right _ _) ht)
    · exact hGuess
  simpa [algorithmOneWarmupOutput] using
    runOutput_eventually_mem stream
      (fun t => (algorithmOneState C stream t).identified)
      (algorithmOne_identified_infinite hLanguagesInfinite)
      (algorithmOneAggressiveGuess C stream hLanguagesInfinite incomparable)
      (C z) T hCurrentValid hGuessValid

/-- Lemma 3.2 specialized to the normalized minimal-common-predecessor run
with the downward token-`2` repair. -/
theorem lemma_3_2_sourceWarmupOutput
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    ∃ T, ∀ t, T ≤ t →
      sourceWarmupOutput C stream hLanguagesInfinite t ∈ C z := by
  simpa [sourceWarmupOutput] using
    lemma_3_2_eventual_validity hLanguagesInfinite hP hE hEz
      (sourceIncomparableChoice C stream hLanguagesInfinite)

/-! ## The ordering bridge used at the start of the Lemma 3.4 charging proof -/

/-- Any unused member of the current identified set upper-bounds the least
warm-up output. -/
theorem algorithmOneWarmupOutput_le_of_available
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) (t x : ℕ)
    (hAvailable :
      x ∉ insert (stream t)
        (algorithmOneWarmupState C stream hLanguagesInfinite
          incomparable t).used)
    (hMem : x ∈ (algorithmOneState C stream t).identified) :
    algorithmOneWarmupOutput C stream hLanguagesInfinite
        incomparable t ≤ x := by
  exact emittedAtStep_le_candidate
    (algorithmOneWarmupState C stream hLanguagesInfinite incomparable t)
    (stream t) (algorithmOneState C stream t).identified
    (algorithmOne_identified_infinite hLanguagesInfinite t)
    (algorithmOneAggressiveGuess C stream hLanguagesInfinite incomparable t)
    hAvailable (Or.inr hMem)

/-- If the next adversary input is still unused and belongs to the current
identified set, the current least output is no larger. -/
theorem algorithmOneWarmupOutput_le_next_input_of_available
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) (t : ℕ)
    (hAvailable :
      stream (t + 1) ∉ insert (stream t)
        (algorithmOneWarmupState C stream hLanguagesInfinite
          incomparable t).used)
    (hMem :
      stream (t + 1) ∈
        (algorithmOneState C stream t).identified) :
    algorithmOneWarmupOutput C stream hLanguagesInfinite
        incomparable t ≤ stream (t + 1) := by
  exact algorithmOneWarmupOutput_le_of_available C stream
    hLanguagesInfinite incomparable t (stream (t + 1)) hAvailable hMem

/-- Source-facing form of the same bridge.  A first-occurrence input which
never appears in the output range is available at the preceding round. -/
theorem algorithmOneWarmupOutput_le_next_input_of_first_occurrence
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (incomparable : IncomparableChoice) (t : ℕ)
    (hFirst : ∀ s, s < t + 1 → stream s ≠ stream (t + 1))
    (hNotOutput :
      stream (t + 1) ∉
        Set.range
          (algorithmOneWarmupOutput C stream hLanguagesInfinite
            incomparable))
    (hMem :
      stream (t + 1) ∈
        (algorithmOneState C stream t).identified) :
    algorithmOneWarmupOutput C stream hLanguagesInfinite
        incomparable t ≤ stream (t + 1) := by
  apply algorithmOneWarmupOutput_le_next_input_of_available
    C stream hLanguagesInfinite incomparable t
  · intro hUsed
    rcases Finset.mem_insert.mp hUsed with hCurrent | hEarlier
    · exact hFirst t (Nat.lt_succ_self t) hCurrent.symm
    · rcases (mem_runState_used_iff stream
          (fun u => (algorithmOneState C stream u).identified)
          (algorithmOne_identified_infinite hLanguagesInfinite)
          (algorithmOneAggressiveGuess C stream hLanguagesInfinite
            incomparable) t _).mp hEarlier with
        ⟨s, hs, hValue⟩ | ⟨s, hs, hValue⟩
      · exact hFirst s (by omega) hValue
      · apply hNotOutput
        exact ⟨s, by
          simpa [algorithmOneWarmupOutput] using hValue⟩
  · exact hMem

/-! ## Canonical latest returns -/

/-!
This layer deliberately does **not** assert that every source-bad input has a
prior return.  The positive-reset rule can jump to a chain position more than
one level below the current cursor, so "the run was full twice" alone does not
show that a later reset target was ever selected.  Even when a prior equal
state exists, it may be the occurrence round itself (the next theorem makes
that precise), whereas the charging argument needs a strictly earlier round
at which the input is still unused.  These are mathematical/source invariants,
not Lean proof-engineering omissions.
-/

/-- Earlier post-cutoff rounds carrying the same identified set as round
`t`.  This finite set makes the source's "largest such time" literal. -/
noncomputable def returnTimes
    (identified : ℕ → Language) (cutoff t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter fun s =>
    cutoff ≤ s ∧ identified s = identified t

@[simp] theorem mem_returnTimes
    {identified : ℕ → Language} {cutoff t s : ℕ} :
    s ∈ returnTimes identified cutoff t ↔
      cutoff ≤ s ∧ s < t ∧ identified s = identified t := by
  classical
  simp only [returnTimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hst, hcutoff, hState⟩
    exact ⟨hcutoff, hst, hState⟩
  · rintro ⟨hcutoff, hst, hState⟩
    exact ⟨hst, hcutoff, hState⟩

/-- There is an earlier occurrence of the same identified set after the
chosen cutoff. -/
def HasPriorReturn
    (identified : ℕ → Language) (cutoff t : ℕ) : Prop :=
  ∃ s, cutoff ≤ s ∧ s < t ∧ identified s = identified t

theorem returnTimes_nonempty_iff
    (identified : ℕ → Language) (cutoff t : ℕ) :
    (returnTimes identified cutoff t).Nonempty ↔
      HasPriorReturn identified cutoff t := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, mem_returnTimes.mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, mem_returnTimes.mpr hs⟩

/-- The source's latest-return map, totalized to `cutoff` when no prior
return exists. -/
noncomputable def latestReturn
    (identified : ℕ → Language) (cutoff t : ℕ) : ℕ := by
  classical
  exact if h : (returnTimes identified cutoff t).Nonempty then
    (returnTimes identified cutoff t).max' h
  else cutoff

theorem latestReturn_spec
    {identified : ℕ → Language} {cutoff t : ℕ}
    (h : HasPriorReturn identified cutoff t) :
    cutoff ≤ latestReturn identified cutoff t ∧
      latestReturn identified cutoff t < t ∧
      identified (latestReturn identified cutoff t) = identified t := by
  classical
  have hNonempty : (returnTimes identified cutoff t).Nonempty :=
    (returnTimes_nonempty_iff identified cutoff t).mpr h
  rw [latestReturn, dif_pos hNonempty]
  exact mem_returnTimes.mp (Finset.max'_mem _ hNonempty)

theorem latestReturn_greatest
    {identified : ℕ → Language} {cutoff t s : ℕ}
    (h : HasPriorReturn identified cutoff t)
    (hs : cutoff ≤ s ∧ s < t ∧ identified s = identified t) :
    s ≤ latestReturn identified cutoff t := by
  classical
  have hNonempty : (returnTimes identified cutoff t).Nonempty :=
    (returnTimes_nonempty_iff identified cutoff t).mpr h
  rw [latestReturn, dif_pos hNonempty]
  exact Finset.le_max' _ _ (mem_returnTimes.mpr hs)

/-- If the state is unchanged across an observation, the latest return to
the post-observation state is the observation round itself.  Thus a theorem
which needs a *strictly pre-observation* return cannot follow from mere prior
return existence. -/
theorem latestReturn_succ_eq_of_eq
    (identified : ℕ → Language) {cutoff t : ℕ}
    (hcutoff : cutoff ≤ t)
    (hEq : identified t = identified (t + 1)) :
    latestReturn identified cutoff (t + 1) = t := by
  have hHas : HasPriorReturn identified cutoff (t + 1) :=
    ⟨t, hcutoff, Nat.lt_succ_self t, hEq⟩
  have hLower : t ≤ latestReturn identified cutoff (t + 1) :=
    latestReturn_greatest hHas
      ⟨hcutoff, Nat.lt_succ_self t, hEq⟩
  have hUpper : latestReturn identified cutoff (t + 1) < t + 1 :=
    (latestReturn_spec hHas).2.1
  omega

/-- Latest return times are injective on rounds which possess a prior
return.  If two later rounds had the same latest return, their identified
sets would agree, making the earlier round a still later return for the
later one. -/
theorem latestReturn_injectiveOn
    (identified : ℕ → Language) (cutoff : ℕ) :
    Set.InjOn (latestReturn identified cutoff)
      {t | HasPriorReturn identified cutoff t} := by
  intro a ha b hb hReturn
  change HasPriorReturn identified cutoff a at ha
  change HasPriorReturn identified cutoff b at hb
  rcases lt_trichotomy a b with hab | hab | hba
  · have haSpec := latestReturn_spec ha
    have hbSpec := latestReturn_spec hb
    have hState : identified a = identified b := by
      calc
        identified a =
            identified (latestReturn identified cutoff a) :=
          haSpec.2.2.symm
        _ = identified (latestReturn identified cutoff b) := by
          rw [hReturn]
        _ = identified b := hbSpec.2.2
    have haCutoff : cutoff ≤ a :=
      le_trans haSpec.1 (Nat.le_of_lt haSpec.2.1)
    have haLeReturn : a ≤ latestReturn identified cutoff b :=
      latestReturn_greatest hb ⟨haCutoff, hab, hState⟩
    have hReturnLt : latestReturn identified cutoff b < a := by
      rw [← hReturn]
      exact haSpec.2.1
    exfalso
    omega
  · exact hab
  · have haSpec := latestReturn_spec ha
    have hbSpec := latestReturn_spec hb
    have hState : identified b = identified a := by
      calc
        identified b =
            identified (latestReturn identified cutoff b) :=
          hbSpec.2.2.symm
        _ = identified (latestReturn identified cutoff a) := by
          rw [hReturn]
        _ = identified a := haSpec.2.2
    have hbCutoff : cutoff ≤ b :=
      le_trans hbSpec.1 (Nat.le_of_lt hbSpec.2.1)
    have hbLeReturn : b ≤ latestReturn identified cutoff a :=
      latestReturn_greatest ha ⟨hbCutoff, hba, hState⟩
    have hReturnLt : latestReturn identified cutoff a < b := by
      rw [hReturn]
      exact hbSpec.2.1
    exfalso
    omega

/-! ## Canonical late-occurrence charges -/

/-- Every observed sample point belongs to every identified consistency
intersection at that time. -/
theorem sample_subset_algorithmOne_identified
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) :
    ↑(sample stream t) ⊆ (algorithmOneState C stream t).identified := by
  intro x hx
  change
    ∀ i, i < algorithmOneChosen C stream t →
      Consistent C stream t i → x ∈ C i
  intro i _ hConsistent
  exact hConsistent hx

/-- Canonical occurrence round of target-order position `i` at or after a
cutoff. -/
noncomputable def orderedOccurrenceTime
    (stream : ℕ → ℕ) (K : OrderedLanguage)
    (cutoff i : ℕ) : ℕ :=
  firstOccurrenceAtOrAfter stream cutoff (K.enumeration i)

/-- Identified state immediately after the canonical occurrence is added to
the consistency sample. -/
noncomputable def postOccurrenceStateTime
    (stream : ℕ → ℕ) (K : OrderedLanguage)
    (cutoff i : ℕ) : ℕ :=
  orderedOccurrenceTime stream K cutoff i + 1

/-- Latest earlier return to the post-occurrence identified set. -/
noncomputable def sourceLatestReturnTime
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (K : OrderedLanguage) (cutoff i : ℕ) : ℕ :=
  latestReturn
    (fun t => (algorithmOneState C stream t).identified)
    cutoff (postOccurrenceStateTime stream K cutoff i)

/-- Output charged at the canonical latest return. -/
noncomputable def sourceLatestReturnCharge
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff i : ℕ) : ℕ :=
  sourceWarmupOutput C stream hLanguagesInfinite
    (sourceLatestReturnTime C stream K cutoff i)

/-- Exact domain on which the source's latest-return charge is justified.

The last field is the causal requirement missing from the displayed proof:
the selected return must precede the input's occurrence round, not merely
the post-occurrence state time. -/
structure LateReturnEligibleRank
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff i : ℕ) : Prop where
  occurs :
    OccursAtOrAfter stream cutoff (K.enumeration i)
  unseenAtCutoff :
    K.enumeration i ∉ sample stream cutoff
  missedByOutput :
    K.enumeration i ∉
      Set.range (sourceWarmupOutput C stream hLanguagesInfinite)
  hasReturn :
    HasPriorReturn
      (fun t => (algorithmOneState C stream t).identified)
      cutoff (postOccurrenceStateTime stream K cutoff i)
  returnBeforeOccurrence :
    sourceLatestReturnTime C stream K cutoff i <
      orderedOccurrenceTime stream K cutoff i

theorem sourceLatestReturnCharge_mem_output
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff i : ℕ) :
    sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i ∈
      Set.range (sourceWarmupOutput C stream hLanguagesInfinite) :=
  ⟨sourceLatestReturnTime C stream K cutoff i, rfl⟩

/-- The corrected latest-return charge is injective on its actual domain.
This composes canonical occurrence injectivity, latest-return injectivity,
and output freshness; repetitions in the presentation are harmless. -/
theorem sourceLatestReturnCharge_injectiveOn
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff : ℕ) :
    Set.InjOn
      (sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff)
      {i | LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i} := by
  intro i hi j hj hCharge
  change LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i at hi
  change LateReturnEligibleRank C stream hLanguagesInfinite K cutoff j at hj
  have hReturn :
      sourceLatestReturnTime C stream K cutoff i =
        sourceLatestReturnTime C stream K cutoff j := by
    apply algorithmOneWarmupOutput_injective C stream hLanguagesInfinite
      (sourceIncomparableChoice C stream hLanguagesInfinite)
    simpa [sourceLatestReturnCharge, sourceWarmupOutput] using hCharge
  have hPost :
      postOccurrenceStateTime stream K cutoff i =
        postOccurrenceStateTime stream K cutoff j := by
    apply latestReturn_injectiveOn
      (fun t => (algorithmOneState C stream t).identified) cutoff
    · exact hi.hasReturn
    · exact hj.hasReturn
    · exact hReturn
  have hOccurrence :
      orderedOccurrenceTime stream K cutoff i =
        orderedOccurrenceTime stream K cutoff j := by
    simpa [postOccurrenceStateTime] using
      Nat.add_right_cancel hPost
  have hValue : K.enumeration i = K.enumeration j := by
    apply firstOccurrenceAtOrAfter_injectiveOn stream cutoff
    · exact hi.occurs
    · exact hj.occurs
    · exact hOccurrence
  exact K.enumeration_injective hValue

/-- The corrected latest-return charge lies strictly before its input in the
ambient universal order.  The proof uses only the actual priority-run state:
canonical first occurrence makes the input unused at the strict earlier
return, equality of identified sets makes it available, and least output
does the rest. -/
theorem sourceLatestReturnCharge_lt
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff i : ℕ)
    (hi : LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i) :
    sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i <
      K.enumeration i := by
  let x := K.enumeration i
  let occurrence := orderedOccurrenceTime stream K cutoff i
  let returnTime := sourceLatestReturnTime C stream K cutoff i
  have hOccurrenceSpec :
      cutoff ≤ occurrence ∧ stream occurrence = x := by
    simpa [occurrence, x, orderedOccurrenceTime] using
      firstOccurrenceAtOrAfter_spec hi.occurs
  have hReturnSpec :
      cutoff ≤ returnTime ∧ returnTime < occurrence + 1 ∧
        (algorithmOneState C stream returnTime).identified =
          (algorithmOneState C stream (occurrence + 1)).identified := by
    simpa [returnTime, occurrence, sourceLatestReturnTime,
      postOccurrenceStateTime] using latestReturn_spec hi.hasReturn
  have hxSample : x ∈ sample stream (occurrence + 1) := by
    rw [← hOccurrenceSpec.2]
    exact value_mem_sample (Nat.lt_succ_self occurrence)
  have hxPost :
      x ∈ (algorithmOneState C stream (occurrence + 1)).identified :=
    sample_subset_algorithmOne_identified C stream (occurrence + 1)
      hxSample
  have hxReturn :
      x ∈ (algorithmOneState C stream returnTime).identified := by
    rw [hReturnSpec.2.2]
    exact hxPost
  have hReturnBefore : returnTime < occurrence := by
    simpa [returnTime, occurrence] using hi.returnBeforeOccurrence
  have hxAvailable :
      x ∉ insert (stream returnTime)
        (sourceWarmupState C stream hLanguagesInfinite returnTime).used := by
    intro hxUsed
    rcases Finset.mem_insert.mp hxUsed with hxCurrent | hxEarlier
    · have hFirstLe : occurrence ≤ returnTime := by
        simpa [occurrence, x, orderedOccurrenceTime] using
          firstOccurrenceAtOrAfter_minimal hReturnSpec.1 hxCurrent.symm
      omega
    · have hUsedCases :
          (∃ u, u < returnTime ∧ stream u = x) ∨
            ∃ u, u < returnTime ∧
              sourceWarmupOutput C stream hLanguagesInfinite u = x := by
        simpa [sourceWarmupState, sourceWarmupOutput,
          algorithmOneWarmupState, algorithmOneWarmupOutput] using
          (mem_runState_used_iff stream
            (fun u => (algorithmOneState C stream u).identified)
            (algorithmOne_identified_infinite hLanguagesInfinite)
            (algorithmOneAggressiveGuess C stream hLanguagesInfinite
              (sourceIncomparableChoice C stream hLanguagesInfinite))
            returnTime x).mp hxEarlier
      rcases hUsedCases with ⟨u, hu, hValue⟩ | ⟨u, hu, hValue⟩
      · by_cases huCutoff : u < cutoff
        · exact hi.unseenAtCutoff
            (mem_sample_iff.mpr ⟨u, huCutoff, hValue⟩)
        · have hFirstLe : occurrence ≤ u := by
            simpa [occurrence, x, orderedOccurrenceTime] using
              firstOccurrenceAtOrAfter_minimal
                (Nat.le_of_not_gt huCutoff) hValue
          omega
      · apply hi.missedByOutput
        exact ⟨u, hValue⟩
  have hLe :
      sourceWarmupOutput C stream hLanguagesInfinite returnTime ≤ x := by
    exact algorithmOneWarmupOutput_le_of_available C stream
      hLanguagesInfinite
      (sourceIncomparableChoice C stream hLanguagesInfinite)
      returnTime x hxAvailable hxReturn
  have hNe :
      sourceWarmupOutput C stream hLanguagesInfinite returnTime ≠ x := by
    intro hEq
    exact hi.missedByOutput ⟨returnTime, hEq⟩
  change sourceWarmupOutput C stream hLanguagesInfinite returnTime < x
  omega

/-! ## Target-order rank form of the latest-return charge -/

/-- Totalized inverse of the target ordering.  On carrier values this is the
shared `orderedPosition`; outside the carrier it is zero. -/
noncomputable def carrierRank (K : OrderedLanguage) (x : ℕ) : ℕ := by
  classical
  exact if hx : x ∈ K.carrier then
    DensityMeasures.FiniteRankFallback.orderedPosition K x hx
  else 0

theorem enumeration_carrierRank_of_mem
    (K : OrderedLanguage) {x : ℕ} (hx : x ∈ K.carrier) :
    K.enumeration (carrierRank K x) = x := by
  classical
  rw [carrierRank, dif_pos hx]
  exact
    DensityMeasures.FiniteRankFallback.enumeration_orderedPosition K x hx

@[simp] theorem carrierRank_enumeration
    (K : OrderedLanguage) (i : ℕ) :
    carrierRank K (K.enumeration i) = i := by
  have hx : K.enumeration i ∈ K.carrier := by
    rw [← K.range_enumeration]
    exact ⟨i, rfl⟩
  apply K.enumeration_injective
  exact enumeration_carrierRank_of_mem K hx

/-- Ambient strict order on carrier values transfers to strict target-rank
order. -/
theorem carrierRank_lt_of_lt
    (K : OrderedLanguage)
    (hOrder :
      DensityMeasures.FiniteRankFallback.InheritsAmbientOrder K)
    {x y : ℕ} (hx : x ∈ K.carrier) (hy : y ∈ K.carrier)
    (hxy : x < y) :
    carrierRank K x < carrierRank K y := by
  by_contra hnot
  have hyx : carrierRank K y ≤ carrierRank K x :=
    Nat.le_of_not_gt hnot
  have hValues := hOrder.monotone hyx
  rw [enumeration_carrierRank_of_mem K hy,
    enumeration_carrierRank_of_mem K hx] at hValues
  omega

/-- Rank of the actual output selected by the latest-return charge. -/
noncomputable def sourceLatestReturnChargeRank
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff i : ℕ) : ℕ :=
  carrierRank K
    (sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i)

/-- Eventual target validity at the same cutoff supplies carrier membership
for every eligible charge, because its return time is no earlier than that
cutoff. -/
theorem sourceLatestReturnCharge_mem_carrier_of_valid
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff i : ℕ)
    (hi : LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i)
    (hValid : ∀ t, cutoff ≤ t →
      sourceWarmupOutput C stream hLanguagesInfinite t ∈ K.carrier) :
    sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i ∈
      K.carrier := by
  apply hValid (sourceLatestReturnTime C stream K cutoff i)
  exact (latestReturn_spec hi.hasReturn).1

/-- The charged rank denotes an actual output. -/
theorem enumeration_sourceLatestReturnChargeRank_mem_output
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff i : ℕ)
    (hCarrier :
      sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i ∈
        K.carrier) :
    K.enumeration
        (sourceLatestReturnChargeRank C stream hLanguagesInfinite
          K cutoff i) ∈
      Set.range (sourceWarmupOutput C stream hLanguagesInfinite) := by
  rw [sourceLatestReturnChargeRank,
    enumeration_carrierRank_of_mem K hCarrier]
  exact sourceLatestReturnCharge_mem_output
    C stream hLanguagesInfinite K cutoff i

/-- Carrier conversion preserves injectivity of the latest-return charge. -/
theorem sourceLatestReturnChargeRank_injectiveOn
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage) (cutoff : ℕ)
    (hCarrier : ∀ i,
      LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i →
        sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i ∈
          K.carrier) :
    Set.InjOn
      (sourceLatestReturnChargeRank C stream hLanguagesInfinite K cutoff)
      {i | LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i} := by
  intro i hi j hj hRanks
  change LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i at hi
  change LateReturnEligibleRank C stream hLanguagesInfinite K cutoff j at hj
  apply sourceLatestReturnCharge_injectiveOn
    C stream hLanguagesInfinite K cutoff hi hj
  calc
    sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i =
        K.enumeration
          (sourceLatestReturnChargeRank C stream hLanguagesInfinite
            K cutoff i) :=
      (enumeration_carrierRank_of_mem K (hCarrier i hi)).symm
    _ = K.enumeration
          (sourceLatestReturnChargeRank C stream hLanguagesInfinite
            K cutoff j) := congrArg K.enumeration hRanks
    _ = sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff j :=
      enumeration_carrierRank_of_mem K (hCarrier j hj)

/-- Under the paper's universal-order convention, the charged output rank
is strictly below the input rank. -/
theorem sourceLatestReturnChargeRank_lt
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage)
    (hOrder :
      DensityMeasures.FiniteRankFallback.InheritsAmbientOrder K)
    (cutoff i : ℕ)
    (hi : LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i)
    (hCarrier :
      sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i ∈
        K.carrier) :
    sourceLatestReturnChargeRank C stream hLanguagesInfinite K cutoff i < i := by
  have hInputCarrier : K.enumeration i ∈ K.carrier := by
    rw [← K.range_enumeration]
    exact ⟨i, rfl⟩
  have hRanks := carrierRank_lt_of_lt K hOrder hCarrier hInputCarrier
    (sourceLatestReturnCharge_lt C stream hLanguagesInfinite K cutoff i hi)
  simpa [sourceLatestReturnChargeRank] using hRanks

/-- The bad-charge half of `WarmupChargeCertificate`, factored out so the
dynamic construction can be checked without importing the later accounting
module.  Its four fields match that certificate's exception and bad-charge
fields definitionally. -/
structure WarmupBadChargeFragment
    (K : OrderedLanguage) (output bad : Language) where
  exceptionRanks : Finset ℕ
  badCharge : ℕ → ℕ
  badCharge_output :
    ∀ i : ℕ, K.enumeration i ∈ bad →
      i ∉ exceptionRanks →
        K.enumeration (badCharge i) ∈ output
  badCharge_le_succ :
    ∀ i : ℕ, K.enumeration i ∈ bad →
      i ∉ exceptionRanks → badCharge i ≤ i + 1
  badCharge_injective :
    Set.InjOn badCharge
      ({i | K.enumeration i ∈ bad} \ (exceptionRanks : Set ℕ))

/-- Conditional bad-charge fragment produced by the normalized warm-up run.

`hCovered` is exactly the remaining mathematical obligation: every
nonexceptional bad input must possess the strict pre-observation return
encoded by `LateReturnEligibleRank`.  All output, order, and injectivity
fields then follow from the concrete run. -/
noncomputable def sourceLatestReturnBadChargeFragment
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (hLanguagesInfinite : ∀ i, (C i).Infinite)
    (K : OrderedLanguage)
    (hOrder :
      DensityMeasures.FiniteRankFallback.InheritsAmbientOrder K)
    (cutoff : ℕ) (bad : Language) (exceptions : Finset ℕ)
    (hValid : ∀ t, cutoff ≤ t →
      sourceWarmupOutput C stream hLanguagesInfinite t ∈ K.carrier)
    (hCovered : ∀ i, K.enumeration i ∈ bad →
      i ∉ exceptions →
        LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i) :
    WarmupBadChargeFragment K
      (Set.range (sourceWarmupOutput C stream hLanguagesInfinite)) bad := by
  classical
  let charge :=
    sourceLatestReturnChargeRank C stream hLanguagesInfinite K cutoff
  have hCarrier : ∀ i,
      LateReturnEligibleRank C stream hLanguagesInfinite K cutoff i →
        sourceLatestReturnCharge C stream hLanguagesInfinite K cutoff i ∈
          K.carrier := by
    intro i hi
    exact sourceLatestReturnCharge_mem_carrier_of_valid
      C stream hLanguagesInfinite K cutoff i hi hValid
  refine
    { exceptionRanks := exceptions
      badCharge := charge
      badCharge_output := ?_
      badCharge_le_succ := ?_
      badCharge_injective := ?_ }
  · intro i hiBad hiException
    have hi := hCovered i hiBad hiException
    exact enumeration_sourceLatestReturnChargeRank_mem_output
      C stream hLanguagesInfinite K cutoff i (hCarrier i hi)
  · intro i hiBad hiException
    have hi := hCovered i hiBad hiException
    have hlt := sourceLatestReturnChargeRank_lt
      C stream hLanguagesInfinite K hOrder cutoff i hi (hCarrier i hi)
    dsimp only [charge]
    omega
  · apply (sourceLatestReturnChargeRank_injectiveOn
      C stream hLanguagesInfinite K cutoff hCarrier).mono
    intro i hi
    exact hCovered i hi.1 hi.2

/-! ## The exact causal obstruction in the source proof -/

/-- With input-first purging, membership of the current input in the current
identified language does not imply that the output is at most that input.
Already from the empty state and the universal identified language, input
zero is purged and the least legal output is one. -/
theorem emittedAtStep_initial_univ_zero_eq_one :
    emittedAtStep State.initial 0 (Set.univ : Language)
      Set.infinite_univ none = 1 := by
  have hFresh := emittedAtStep_fresh State.initial 0
    (Set.univ : Language) Set.infinite_univ none
  have hNeZero :
      emittedAtStep State.initial 0 (Set.univ : Language)
        Set.infinite_univ none ≠ 0 := by
    intro hEq
    apply hFresh
    rw [hEq]
    simp [State.initial]
  have hLeOne :
      emittedAtStep State.initial 0 (Set.univ : Language)
        Set.infinite_univ none ≤ 1 := by
    apply emittedAtStep_le_candidate State.initial 0
      (Set.univ : Language) Set.infinite_univ none
    · simp [State.initial]
    · exact Or.inr (Set.mem_univ 1)
  omega

/-- Consequently the key informal implication used at the start of Lemma
3.4 is false for the well-posed input-first state machine without an earlier
availability/causality invariant. -/
theorem current_input_mem_does_not_force_output_le :
    0 ∈ (Set.univ : Language) ∧
      ¬ emittedAtStep State.initial 0 (Set.univ : Language)
          Set.infinite_univ none ≤ 0 := by
  constructor
  · exact Set.mem_univ 0
  · rw [emittedAtStep_initial_univ_zero_eq_one]
    omega

end WarmupPriority
end PartialEnumeration
end KleinbergWei
end GenLimit
