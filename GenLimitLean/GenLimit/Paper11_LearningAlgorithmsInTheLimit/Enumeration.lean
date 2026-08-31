import GenLimit.Paper11_LearningAlgorithmsInTheLimit.Definitions
import Mathlib.Data.Finset.Max

/-!
# Uniform learning by enumeration

This file formalizes the finite-injury argument shared by Theorems 12, 14,
and 16.  The executable learner below receives only a finite observation
history.  It does not receive the target, its index, the future stream, or a
proof identifying a correct representation.

At history length `t`, the learner checks the first `t + 1` candidates and
returns the least one consistent with the history.  This bounded search is a
total Lean function.  If some candidate is consistent with the whole stream,
the search eventually includes the least such candidate and permanently
rejects its finitely many predecessors.
-/

namespace GenLimit.LearningAlgorithmsLimit

/-- A candidate fits every observation in a finite ordered history. -/
def HistoryConsistent
    (fits : ℕ → Info → Prop) (history : List Info) (candidate : ℕ) : Prop :=
  List.Forall (fits candidate) history

/-- A candidate fits every observation strictly before time `t`. -/
def PrefixConsistent
    (fits : ℕ → Info → Prop) (stream : ℕ → Info)
    (t candidate : ℕ) : Prop :=
  ∀ n : Fin t, fits candidate (stream n)

/-- A candidate fits the complete infinite observation stream. -/
def StreamConsistent
    (fits : ℕ → Info → Prop) (stream : ℕ → Info)
    (candidate : ℕ) : Prop :=
  ∀ n, fits candidate (stream n)

theorem historyConsistent_textPrefix_iff
    (fits : ℕ → Info → Prop) (stream : ℕ → Info) (t candidate : ℕ) :
    HistoryConsistent fits (GenLimit.textPrefix stream t) candidate ↔
      PrefixConsistent fits stream t candidate := by
  constructor
  · intro h n
    rw [HistoryConsistent, List.forall_iff_forall_mem] at h
    exact h (stream n)
      (GenLimit.mem_textPrefix_iff.mpr ⟨n, n.isLt, rfl⟩)
  · intro h
    rw [HistoryConsistent, List.forall_iff_forall_mem]
    intro observation hobservation
    obtain ⟨n, hn, rfl⟩ :=
      GenLimit.mem_textPrefix_iff.mp hobservation
    exact h ⟨n, hn⟩

instance historyConsistentDecidable
    (fits : ℕ → Info → Prop) [DecidableRel fits]
    (history : List Info) :
    DecidablePred (HistoryConsistent fits history) :=
  fun candidate => by
    unfold HistoryConsistent
    infer_instance

theorem prefixConsistent_of_streamConsistent
    {fits : ℕ → Info → Prop} {stream : ℕ → Info}
    {t candidate : ℕ}
    (h : StreamConsistent fits stream candidate) :
    PrefixConsistent fits stream t candidate := by
  intro n
  exact h n

theorem prefixConsistent_mono
    {fits : ℕ → Info → Prop} {stream : ℕ → Info}
    {s t candidate : ℕ} (hst : s ≤ t)
    (h : PrefixConsistent fits stream t candidate) :
    PrefixConsistent fits stream s candidate := by
  intro n
  exact h ⟨n, lt_of_lt_of_le n.isLt hst⟩

/-- Candidates inspected by the total search at the current history length. -/
def admissibleCandidates
    (fits : ℕ → Info → Prop) [DecidableRel fits]
    (history : List Info) : Finset ℕ :=
  (Finset.range (history.length + 1)).filter
    (HistoryConsistent fits history)

@[simp] theorem mem_admissibleCandidates_iff
    (fits : ℕ → Info → Prop) [DecidableRel fits]
    (history : List Info) (candidate : ℕ) :
    candidate ∈ admissibleCandidates fits history ↔
      candidate ≤ history.length ∧
        HistoryConsistent fits history candidate := by
  simp [admissibleCandidates, Nat.lt_succ_iff]

/-- A uniform executable learner.  The fallback value is used only while no
candidate within the current finite search bound fits the history. -/
def enumerationLearner
    (fits : ℕ → Info → Prop) [DecidableRel fits] :
    GenLimit.Learner Info ℕ :=
  fun history =>
    let candidates := admissibleCandidates fits history
    if h : candidates.Nonempty then candidates.min' h else 0

theorem enumerationLearner_eq_of_least
    (fits : ℕ → Info → Prop) [DecidableRel fits]
    (history : List Info) (k : ℕ)
    (hkBound : k ≤ history.length)
    (hkConsistent : HistoryConsistent fits history k)
    (hLeast : ∀ i, i < k → ¬HistoryConsistent fits history i) :
    enumerationLearner fits history = k := by
  let candidates := admissibleCandidates fits history
  have hkMem : k ∈ candidates := by
    exact (mem_admissibleCandidates_iff fits history k).2
      ⟨hkBound, hkConsistent⟩
  have hnonempty : candidates.Nonempty := ⟨k, hkMem⟩
  change (if h : candidates.Nonempty then candidates.min' h else 0) = k
  rw [dif_pos hnonempty]
  apply Nat.le_antisymm
  · exact Finset.min'_le candidates k hkMem
  · by_contra hnot
    have hlt : candidates.min' hnonempty < k := Nat.lt_of_not_ge hnot
    have hminMem : candidates.min' hnonempty ∈ candidates :=
      Finset.min'_mem candidates hnonempty
    exact hLeast _ hlt
      ((mem_admissibleCandidates_iff fits history _).1 hminMem).2

/-- A finite set of lower-index candidates that fail somewhere on the full
stream is rejected by one common finite prefix. -/
theorem finite_predecessors_eventually_rejected
    (fits : ℕ → Info → Prop) (stream : ℕ → Info) (k : ℕ)
    (hwrong : ∀ i, i < k → ¬StreamConsistent fits stream i) :
    ∃ t₀, ∀ i, i < k →
      ¬PrefixConsistent fits stream t₀ i := by
  classical
  induction k with
  | zero =>
      exact ⟨0, by omega⟩
  | succ k ih =>
      have hwrongPrev : ∀ i, i < k →
          ¬StreamConsistent fits stream i := by
        intro i hi
        exact hwrong i (Nat.lt.step hi)
      obtain ⟨t, ht⟩ := ih hwrongPrev
      have hknot : ¬StreamConsistent fits stream k :=
        hwrong k (Nat.lt_succ_self k)
      rw [StreamConsistent] at hknot
      push_neg at hknot
      obtain ⟨n, hn⟩ := hknot
      refine ⟨max t (n + 1), ?_⟩
      intro i hi hconsistent
      by_cases hik : i < k
      · exact ht i hik
          (prefixConsistent_mono (Nat.le_max_left _ _) hconsistent)
      · have hieq : i = k := by omega
        subst i
        exact hn (hconsistent ⟨n, by
          exact lt_of_lt_of_le (Nat.lt_succ_self n)
            (Nat.le_max_right t (n + 1))⟩)

/-- Once a least stream-consistent candidate exists, the uniform bounded
search stabilizes to it. -/
theorem enumeration_stabilizes_to_least
    (fits : ℕ → Info → Prop) [DecidableRel fits]
    (stream : ℕ → Info) (k : ℕ)
    (hk : StreamConsistent fits stream k)
    (hleast : ∀ i, i < k → ¬StreamConsistent fits stream i) :
    GenLimit.StabilizesTo
      (fun t => enumerationLearner fits (GenLimit.textPrefix stream t)) k := by
  obtain ⟨t₀, hrejected⟩ :=
    finite_predecessors_eventually_rejected fits stream k hleast
  refine ⟨max k t₀, ?_⟩
  intro t htt
  apply enumerationLearner_eq_of_least fits _ k
  · simpa using (Nat.le_max_left k t₀).trans htt
  · exact historyConsistent_textPrefix_iff fits stream t k |>.2
      (prefixConsistent_of_streamConsistent hk)
  · intro i hi hconsistent
    apply hrejected i hi
    exact prefixConsistent_mono ((Nat.le_max_right k t₀).trans htt)
      ((historyConsistent_textPrefix_iff fits stream t i).1 hconsistent)

/-- Target-independent enumeration identifies the first candidate fitting the
entire information stream whenever such a candidate exists. -/
theorem enumeration_identifies_first_consistent
    (fits : ℕ → Info → Prop) [DecidableRel fits]
    (stream : ℕ → Info)
    (hexists : ∃ candidate, StreamConsistent fits stream candidate) :
    ∃ candidate, StreamConsistent fits stream candidate ∧
      GenLimit.StabilizesTo
        (fun t => enumerationLearner fits (GenLimit.textPrefix stream t))
        candidate := by
  classical
  let k := Nat.find hexists
  refine ⟨k, Nat.find_spec hexists, ?_⟩
  apply enumeration_stabilizes_to_least fits stream k (Nat.find_spec hexists)
  intro i hi
  exact Nat.find_min hexists hi

/-- A labeled input-output observation used by the semantic enumeration
specialization. -/
structure LabeledObservation (Input Output : Type*) where
  input : Input
  value : Option Output

def labeledFits
    (semantics : ℕ → Input → Option Output)
    (candidate : ℕ) (observation : LabeledObservation Input Output) : Prop :=
  semantics candidate observation.input = observation.value

instance labeledFitsDecidableRel
    [DecidableEq Output]
    (semantics : ℕ → Input → Option Output) :
    DecidableRel (labeledFits semantics) :=
  fun _ _ => by
    unfold labeledFits
    infer_instance

def labeledStream
    (target : Input → Option Output) (stream : ℕ → Input) :
    ℕ → LabeledObservation Input Output :=
  fun n => ⟨stream n, target (stream n)⟩

/-- The uniform learner specialized to ordinary labeled observations. -/
def labeledEnumerationLearner
    [DecidableEq Output]
    (semantics : ℕ → Input → Option Output) :
    GenLimit.Learner (LabeledObservation Input Output) ℕ :=
  enumerationLearner (labeledFits semantics)

theorem streamConsistent_labeled_iff_correctOn
    (semantics : ℕ → Input → Option Output)
    (target : Input → Option Output)
    (stream : ℕ → Input) (source : Set Input)
    (hcover : Covers stream source) (candidate : ℕ) :
    StreamConsistent (labeledFits semantics)
        (labeledStream target stream) candidate ↔
      CorrectOn semantics target source candidate := by
  constructor
  · intro h x hx
    obtain ⟨n, rfl⟩ := covers_exists_eq hcover hx
    exact h n
  · intro h n
    exact h (stream n) (covers_stream_mem hcover n)

/-- The full uniform semantic enumeration theorem.  The existence proof for a
correct index is used only in the convergence proof; it is not an argument to
the executable learner. -/
theorem enumeration_learnsInLimit
    [DecidableEq Output]
    (semantics : ℕ → Input → Option Output)
    (target : Input → Option Output)
    (stream : ℕ → Input) (source : Set Input)
    (hcover : Covers stream source)
    (hexists : ∃ candidate, CorrectOn semantics target source candidate) :
    LearnsInLimit
      (labeledEnumerationLearner semantics)
      (labeledStream target stream)
      semantics target source := by
  have hexistsStream :
      ∃ candidate, StreamConsistent (labeledFits semantics)
        (labeledStream target stream) candidate := by
    simpa only [streamConsistent_labeled_iff_correctOn
      semantics target stream source hcover] using hexists
  obtain ⟨candidate, hconsistent, hstable⟩ :=
    enumeration_identifies_first_consistent
      (labeledFits semantics) (labeledStream target stream) hexistsStream
  exact ⟨candidate,
    (streamConsistent_labeled_iff_correctOn
      semantics target stream source hcover candidate).1 hconsistent,
    hstable⟩

end GenLimit.LearningAlgorithmsLimit
