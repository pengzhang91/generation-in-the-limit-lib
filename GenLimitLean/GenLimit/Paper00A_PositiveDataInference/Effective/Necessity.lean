import GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency
import GenLimit.Paper00A_PositiveDataInference.Effective.Stabilization
import GenLimit.Paper00A_PositiveDataInference.Semantic.Necessity

/-!
# Effective necessity of Angluin's Condition 1

This file proves the necessity direction of Angluin's Theorem 1.  Together with
the imported sufficiency direction, it assembles the full biconditional.

The computable tell-tale enumerator uses finite, decidable approximations to
syntactic locking histories.  At stage `s` it selects the least encoded
target-consistent history that survives every extension test of code below
`s`.  A genuine syntactic locking history exists by the usual diagonal
argument, so the least provisional candidate eventually becomes constant.
Consequently the union of all candidate contents is finite and contains a
locking history, while the stage procedure itself remains total computable.
-/

namespace GenLimit.Angluin

open GenLimit.Generic
open GenLimit.Gold.Text

/-! ## Decidable finite approximations to stabilization -/

/-- Decode a natural number as a finite history, using the empty history for
codes outside the image of the list encoding. -/
def decodedHistory (code : ℕ) : List ℕ :=
  (Encodable.decode code).getD []

theorem decodedHistory_computable : Computable decodedHistory :=
  Computable.option_getD Computable.decode (Computable.const [])

@[simp] theorem decodedHistory_encode (history : List ℕ) :
    decodedHistory (Encodable.encode history) = history := by
  simp [decodedHistory]

/-- Executable target-consistency test for a finite history. -/
def historyInCheck (F : EffectiveIndexedFamily)
    (i : ℕ) (history : List ℕ) : Bool :=
  observedCheck F history i

theorem historyInCheck_computable (F : EffectiveIndexedFamily) :
    Computable₂ (historyInCheck F) :=
  (observedCheck_computable F).comp₂
    Primrec₂.right.to_comp Primrec₂.left.to_comp

theorem historyInCheck_eq_true_iff
    (F : EffectiveIndexedFamily) (i : ℕ) (history : List ℕ) :
    historyInCheck F i history = true ↔
      HistoryIn history (F.language i) := by
  rw [historyInCheck, observedCheck, boundedAll_eq_true_iff]
  constructor
  · intro h x hx
    obtain ⟨k, hk⟩ := List.get_of_mem hx
    have hmember := h k k.isLt
    rw [F.membership_spec] at hmember
    simpa [← hk] using hmember
  · intro h k hk
    rw [F.membership_spec]
    apply h
    have hget : history.getD k 0 = history[k] := by
      rw [List.getD_eq_getElem?_getD]
      simp [hk]
    rw [hget]
    exact List.get_mem history ⟨k, hk⟩

/-- A coded extension is accepted when it is not target-consistent, or when
it leaves the learner's current conjecture unchanged. -/
def extensionAccepted (F : EffectiveIndexedFamily)
    (M : EffectiveIdentifier) (p : ℕ × List ℕ) (code : ℕ) : Bool :=
  let extension := decodedHistory code
  if historyInCheck F p.1 extension then
    decide (M (p.2 ++ extension) = M p.2)
  else
    true

theorem extensionAccepted_computable
    (F : EffectiveIndexedFamily) {M : EffectiveIdentifier}
    (hM : Computable M) :
    Computable₂ (extensionAccepted F M) := by
  let Input := ((ℕ × List ℕ) × ℕ)
  have hextension : Computable (fun z : Input => decodedHistory z.2) :=
    decodedHistory_computable.comp Computable.snd
  have hwithin : Computable (fun z : Input =>
      historyInCheck F z.1.1 (decodedHistory z.2)) :=
    (historyInCheck_computable F).comp
      (Computable.fst.comp Computable.fst) hextension
  have happended : Computable (fun z : Input =>
      M (z.1.2 ++ decodedHistory z.2)) :=
    hM.comp <| Primrec.list_append.to_comp.comp
      (Computable.snd.comp Computable.fst) hextension
  have hcurrent : Computable (fun z : Input => M z.1.2) :=
    hM.comp (Computable.snd.comp Computable.fst)
  have hequal : Computable (fun z : Input =>
      decide (M (z.1.2 ++ decodedHistory z.2) = M z.1.2)) :=
    (Primrec.beq.to_comp.comp happended hcurrent).of_eq fun _ => by
      rfl
  exact (Computable.to₂ <|
    Computable.cond hwithin hequal (Computable.const true)).of_eq
      fun z => by
        rcases z with ⟨p, code⟩
        simp only [extensionAccepted]
        cases historyInCheck F p.1 (decodedHistory code) <;> rfl

theorem extensionAccepted_eq_true_iff
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    (i : ℕ) (history : List ℕ) (code : ℕ) :
    extensionAccepted F M (i, history) code = true ↔
      HistoryIn (decodedHistory code) (F.language i) →
        M (history ++ decodedHistory code) = M history := by
  simp only [extensionAccepted]
  by_cases hwithin : historyInCheck F i (decodedHistory code) = true
  · simp only [if_pos hwithin]
    simp only [decide_eq_true_eq]
    have hhistory :=
      (historyInCheck_eq_true_iff F i (decodedHistory code)).mp hwithin
    constructor
    · intro heq _
      exact heq
    · intro himp
      exact himp hhistory
  · have hfalse : historyInCheck F i (decodedHistory code) = false :=
      Bool.eq_false_of_not_eq_true hwithin
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro _ hhistory
      exact False.elim (hwithin <|
        (historyInCheck_eq_true_iff F i (decodedHistory code)).mpr hhistory)
    · intro _
      trivial

/-- `code` is a provisional stabilizing-history candidate at finite search
stage `s`. -/
def stabilizationCandidateCheck (F : EffectiveIndexedFamily)
    (M : EffectiveIdentifier) (p : ℕ × ℕ) (code : ℕ) : Bool :=
  match Encodable.decode code with
  | none => false
  | some history =>
      historyInCheck F p.1 history &&
        boundedAll (extensionAccepted F M) (p.1, history) p.2

theorem stabilizationCandidateCheck_computable
    (F : EffectiveIndexedFamily) {M : EffectiveIdentifier}
    (hM : Computable M) :
    Computable₂ (stabilizationCandidateCheck F M) := by
  let Input := ((ℕ × ℕ) × ℕ)
  have hdecoded : Computable (fun z : Input =>
      (Encodable.decode z.2 : Option (List ℕ))) :=
    Computable.decode.comp Computable.snd
  have hsome : Computable₂ (fun (z : Input) (history : List ℕ) =>
      historyInCheck F z.1.1 history &&
        boundedAll (extensionAccepted F M)
          (z.1.1, history) z.1.2) := by
    have hhistory : Computable₂ (fun (z : Input) (history : List ℕ) =>
        historyInCheck F z.1.1 history) :=
      (historyInCheck_computable F).comp₂
        (Primrec.fst.comp₂
          (Primrec.fst.comp₂ Primrec₂.left)).to_comp
        Primrec₂.right.to_comp
    have hbounded : Computable₂ (fun (z : Input) (history : List ℕ) =>
        boundedAll (extensionAccepted F M)
          (z.1.1, history) z.1.2) :=
      (boundedAll_computable (extensionAccepted_computable F hM)).comp₂
        (Primrec₂.pair.comp₂
          (Primrec.fst.comp₂
            (Primrec.fst.comp₂ Primrec₂.left))
          Primrec₂.right).to_comp
        (Primrec.snd.comp₂
          (Primrec.fst.comp₂ Primrec₂.left)).to_comp
    exact Primrec.and.to_comp.comp₂ hhistory hbounded
  exact (Computable.to₂ <|
    Computable.option_casesOn hdecoded (Computable.const false) hsome).of_eq
      fun z => by
        rcases z with ⟨p, code⟩
        simp only [stabilizationCandidateCheck]
        cases (Encodable.decode code : Option (List ℕ)) <;> rfl

theorem stabilizing_candidate_true
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    {i : ℕ} {history : List ℕ}
    (hstable : SyntacticallyStabilizing M (F.language i) history)
    (s : ℕ) :
    stabilizationCandidateCheck F M (i, s) (Encodable.encode history) = true := by
  rw [stabilizationCandidateCheck]
  simp only [Encodable.encodek, Bool.and_eq_true]
  constructor
  · exact (historyInCheck_eq_true_iff F i history).mpr hstable.1
  · rw [boundedAll_eq_true_iff]
    intro code _hcode
    exact (extensionAccepted_eq_true_iff F M i history code).mpr
      (hstable.2 (decodedHistory code))

/-- Least provisional stabilizing history visible at stage `s`, if there is
one among the first `s + 1` codes. -/
def provisionalHistory (F : EffectiveIndexedFamily)
    (M : EffectiveIdentifier) (i s : ℕ) : Option (List ℕ) :=
  (firstTrue (stabilizationCandidateCheck F M)
    (i, s) (s + 1)).bind Encodable.decode

theorem provisionalHistory_computable
    (F : EffectiveIndexedFamily) {M : EffectiveIdentifier}
    (hM : Computable M) :
    Computable₂ (provisionalHistory F M) := by
  have hsearch : Computable (fun p : ℕ × ℕ =>
      firstTrue (stabilizationCandidateCheck F M)
        p (p.2 + 1)) :=
    (firstTrue_computable
      (stabilizationCandidateCheck_computable F hM)).comp
        Computable.id
        (Primrec.succ.to_comp.comp Computable.snd)
  have hdecode : Computable₂ (fun (_p : ℕ × ℕ) (code : ℕ) =>
      (Encodable.decode code : Option (List ℕ))) :=
    Computable.to₂ (Computable.decode.comp Computable.snd)
  exact (Computable.to₂ <| Computable.option_bind hsearch hdecode).of_eq
    fun p => by
      rcases p with ⟨i, s⟩
      rfl

/-- The total stage procedure used for Condition 1.  A stage decodes as a
pair `(s,k)` and emits the `k`th element of the provisional history at search
stage `s`. -/
def lockingEmitter (F : EffectiveIndexedFamily)
    (M : EffectiveIdentifier) (i stage : ℕ) : Option ℕ :=
  let sk := stage.unpair
  (provisionalHistory F M i sk.1).bind fun history =>
    history[sk.2]?

theorem lockingEmitter_computable
    (F : EffectiveIndexedFamily) {M : EffectiveIdentifier}
    (hM : Computable M) :
    Computable₂ (lockingEmitter F M) := by
  let Input := ℕ × ℕ
  have hsearchStage : Computable (fun z : Input => z.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
  have helement : Computable (fun z : Input => z.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
  have hhistory : Computable (fun z : Input =>
      provisionalHistory F M z.1 z.2.unpair.1) :=
    (provisionalHistory_computable F hM).comp Computable.fst hsearchStage
  have hget : Computable₂ (fun (z : Input) (history : List ℕ) =>
      history[z.2.unpair.2]?) :=
    Primrec.list_getElem?.to_comp.comp₂
      Primrec₂.right.to_comp
      (Primrec.snd.comp₂
        (Primrec.unpair.comp₂
          (Primrec.snd.comp₂ Primrec₂.left))).to_comp
  exact (Computable.to₂ <| Computable.option_bind hhistory hget).of_eq
    fun z => by
      rcases z with ⟨i, stage⟩
      rfl

theorem provisionalHistory_historyIn
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    {i s : ℕ} {history : List ℕ}
    (h : provisionalHistory F M i s = some history) :
    HistoryIn history (F.language i) := by
  rw [provisionalHistory, Option.bind_eq_some_iff] at h
  obtain ⟨code, hcode, hdecode⟩ := h
  obtain ⟨-, hcandidate, -⟩ := firstTrue_spec hcode
  rw [stabilizationCandidateCheck, hdecode, Bool.and_eq_true] at hcandidate
  exact (historyInCheck_eq_true_iff F i history).mp hcandidate.1

theorem lockingEmitter_mem_language
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    {i stage x : ℕ} (h : lockingEmitter F M i stage = some x) :
    x ∈ F.language i := by
  rw [lockingEmitter, Option.bind_eq_some_iff] at h
  obtain ⟨history, hhistory, hx⟩ := h
  exact provisionalHistory_historyIn F M hhistory x
    (List.mem_of_getElem? hx)

private theorem exists_stabilizing_of_identifies
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    (hIdentifies :
      SemanticallyIdentifies M F.language)
    (i : ℕ) :
    ∃ history, SyntacticallyStabilizing M (F.language i) history := by
  apply exists_syntacticallyStabilizing (F.nonempty i)
  intro stream hP
  obtain ⟨guess, _hguess, T, hT⟩ := hIdentifies i stream hP
  refine ⟨guess, T, ?_⟩
  intro t ht
  exact hT t ht

private theorem nonstabilizing_candidate_eventually_false
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    {i code : ℕ}
    (hnot : ¬ ∃ history,
      Encodable.decode code = some history ∧
        SyntacticallyStabilizing M (F.language i) history) :
    ∃ N, ∀ s, N ≤ s →
      stabilizationCandidateCheck F M (i, s) code = false := by
  cases hdecode : (Encodable.decode code : Option (List ℕ)) with
  | none =>
      exact ⟨0, fun s _ => by
        rw [stabilizationCandidateCheck, hdecode]⟩
  | some history =>
      by_cases hhistory : HistoryIn history (F.language i)
      · have hnotStable :
            ¬ SyntacticallyStabilizing M (F.language i) history := by
          intro hstable
          exact hnot ⟨history, hdecode, hstable⟩
        have hchanges : ∃ extension,
            HistoryIn extension (F.language i) ∧
              M (history ++ extension) ≠ M history := by
          by_contra h
          push_neg at h
          exact hnotStable ⟨hhistory, h⟩
        obtain ⟨extension, hextension, hchange⟩ := hchanges
        refine ⟨Encodable.encode extension + 1, ?_⟩
        intro s hs
        apply Bool.eq_false_of_not_eq_true
        intro hcandidate
        rw [stabilizationCandidateCheck, hdecode,
          Bool.and_eq_true] at hcandidate
        have haccepted :=
          (boundedAll_eq_true_iff
            (extensionAccepted F M) (i, history) s).mp hcandidate.2
            (Encodable.encode extension)
            (lt_of_lt_of_le (Nat.lt_succ_self _) hs)
        have hsame :=
          (extensionAccepted_eq_true_iff F M i history
            (Encodable.encode extension)).mp haccepted
        exact hchange (by
          simpa only [decodedHistory_encode] using
            hsame (by simpa only [decodedHistory_encode] using hextension))
      · have hcheckFalse : historyInCheck F i history = false :=
          Bool.eq_false_of_not_eq_true fun htrue =>
            hhistory ((historyInCheck_eq_true_iff F i history).mp htrue)
        exact ⟨0, fun s _ => by
          rw [stabilizationCandidateCheck, hdecode]
          simp [hcheckFalse]⟩

private theorem stabilizing_candidate_true_of_decode
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    {i code : ℕ} {history : List ℕ}
    (hdecode : Encodable.decode code = some history)
    (hstable : SyntacticallyStabilizing M (F.language i) history)
    (s : ℕ) :
    stabilizationCandidateCheck F M (i, s) code = true := by
  rw [stabilizationCandidateCheck, hdecode, Bool.and_eq_true]
  constructor
  · exact (historyInCheck_eq_true_iff F i history).mpr hstable.1
  · rw [boundedAll_eq_true_iff]
    intro extensionCode _
    exact (extensionAccepted_eq_true_iff F M i history extensionCode).mpr
      (hstable.2 (decodedHistory extensionCode))

private theorem provisionalHistory_eventually_stabilizing
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    (hIdentifies :
      SemanticallyIdentifies M F.language)
    (i : ℕ) :
    ∃ history, SyntacticallyStabilizing M (F.language i) history ∧
      ∃ N, ∀ s, N ≤ s →
        provisionalHistory F M i s = some history := by
  classical
  let good : ℕ → Prop := fun code => ∃ history,
    Encodable.decode code = some history ∧
      SyntacticallyStabilizing M (F.language i) history
  have hgood : ∃ code, good code := by
    obtain ⟨history, hstable⟩ :=
      exists_stabilizing_of_identifies F M hIdentifies i
    exact ⟨Encodable.encode history, history, by simp, hstable⟩
  let leastCode := Nat.find hgood
  obtain ⟨history, hdecode, hstable⟩ := Nat.find_spec hgood
  change Encodable.decode leastCode = some history at hdecode
  have hlower : ∀ code < leastCode, ¬ good code := by
    intro code hcode
    exact Nat.find_min hgood hcode
  have heach : ∀ code < leastCode, ∃ N, ∀ s, N ≤ s →
      stabilizationCandidateCheck F M (i, s) code = false := by
    intro code hcode
    exact nonstabilizing_candidate_eventually_false F M
      (hlower code hcode)
  have huniform : ∃ N, ∀ code < leastCode, ∀ s, N ≤ s →
      stabilizationCandidateCheck F M (i, s) code = false := by
    have hfinite : ∀ n,
        (∀ code < n, ∃ N, ∀ s, N ≤ s →
          stabilizationCandidateCheck F M (i, s) code = false) →
        ∃ N, ∀ code < n, ∀ s, N ≤ s →
          stabilizationCandidateCheck F M (i, s) code = false := by
      intro n hn
      induction n with
      | zero =>
          exact ⟨0, by simp⟩
      | succ n ih =>
          have hprevEach : ∀ code < n, ∃ N, ∀ s, N ≤ s →
              stabilizationCandidateCheck F M (i, s) code = false := by
            intro code hcode
            exact hn code (Nat.lt.step hcode)
          obtain ⟨Nprev, hprev⟩ := ih hprevEach
          obtain ⟨Nlast, hlast⟩ := hn n (Nat.lt_succ_self n)
          refine ⟨max Nprev Nlast, ?_⟩
          intro code hcode s hs
          rcases Nat.lt_succ_iff_lt_or_eq.mp hcode with hlt | rfl
          · exact hprev code hlt s
              ((Nat.le_max_left _ _).trans hs)
          · exact hlast s ((Nat.le_max_right _ _).trans hs)
    exact hfinite leastCode heach
  obtain ⟨Nlower, hNlower⟩ := huniform
  refine ⟨history, hstable, max Nlower leastCode, ?_⟩
  intro s hs
  have hsLower : Nlower ≤ s := (Nat.le_max_left _ _).trans hs
  have hsCode : leastCode ≤ s := (Nat.le_max_right _ _).trans hs
  have hleastTrue :
      stabilizationCandidateCheck F M (i, s) leastCode = true := by
    exact stabilizing_candidate_true_of_decode F M hdecode hstable s
  let search := firstTrue (stabilizationCandidateCheck F M)
    (i, s) (s + 1)
  have hsearchSome : ∃ code, search = some code := by
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hall := (firstTrue_eq_none_iff
      (stabilizationCandidateCheck F M) (i, s) (s + 1)).mp hnone
    have := hall leastCode (Nat.lt_succ_iff.mpr hsCode)
    simp [hleastTrue] at this
  obtain ⟨found, hfound⟩ := hsearchSome
  have hfoundLe : found ≤ leastCode :=
    firstTrue_le_of_true hfound
      (Nat.lt_succ_iff.mpr hsCode) hleastTrue
  have hfoundEq : found = leastCode := by
    rcases hfoundLe.eq_or_lt with heq | hlt
    · exact heq
    · have hfoundSpec := (firstTrue_spec hfound).2.1
      rw [hNlower found hlt s hsLower] at hfoundSpec
      contradiction
  rw [provisionalHistory]
  change search.bind Encodable.decode = some history
  rw [hfound, hfoundEq]
  simpa using hdecode

private theorem stabilizing_history_subset_enumerated
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    {i N : ℕ} {history : List ℕ}
    (heventual : ∀ s, N ≤ s →
      provisionalHistory F M i s = some history) :
    (↑history.toFinset : Set ℕ) ⊆
      enumeratedSet (lockingEmitter F M) i := by
  intro x hx
  have hxList : x ∈ history := by simpa using hx
  obtain ⟨k, hk⟩ := List.get_of_mem hxList
  refine ⟨Nat.pair N k, ?_⟩
  simp only [lockingEmitter, Nat.unpair_pair]
  rw [heventual N le_rfl]
  simp only [Option.bind_some]
  rw [List.getElem?_eq_getElem k.isLt]
  exact congrArg some hk

private theorem enumeratedSet_lockingEmitter_finite
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    {i N : ℕ} {history : List ℕ}
    (heventual : ∀ s, N ≤ s →
      provisionalHistory F M i s = some history) :
    (enumeratedSet (lockingEmitter F M) i).Finite := by
  classical
  let early : Finset ℕ :=
    ((List.range N).flatMap fun s =>
      (provisionalHistory F M i s).getD []).toFinset
  let bound : Finset ℕ := early ∪ history.toFinset
  apply bound.finite_toSet.subset
  intro x hx
  obtain ⟨stage, hstage⟩ := hx
  rw [lockingEmitter, Option.bind_eq_some_iff] at hstage
  obtain ⟨candidate, hcandidate, hxCandidate⟩ := hstage
  have hxmem : x ∈ candidate := List.mem_of_getElem? hxCandidate
  by_cases hs : stage.unpair.1 < N
  · have hxEarly : x ∈ early := by
      simp only [early, List.mem_toFinset, List.mem_flatMap,
        List.mem_range]
      exact ⟨stage.unpair.1, hs, by simpa [hcandidate] using hxmem⟩
    exact Finset.mem_union_left _ hxEarly
  · have hsN : N ≤ stage.unpair.1 := Nat.le_of_not_gt hs
    have hfixed := heventual stage.unpair.1 hsN
    rw [hfixed] at hcandidate
    injection hcandidate with hcandidateEq
    subst candidate
    exact Finset.mem_union_right _ (by simpa using hxmem)

/-! ## A syntactically stabilizing history denotes the target -/

private theorem stabilizing_guess_denotes
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    (hIdentifies :
      SemanticallyIdentifies M F.language)
    {i : ℕ} {history : List ℕ}
    (hstable : SyntacticallyStabilizing M (F.language i) history) :
    F.language (M history) = F.language i := by
  classical
  obtain ⟨base, hbase⟩ := exists_presentation_of_nonempty (F.nonempty i)
  let stream : ℕ → ℕ := fun t =>
    if ht : t < history.length then
      history.get ⟨t, ht⟩
    else
      base (t - history.length)
  have hstreamP : GenLimit.Presents stream (F.language i) := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, rfl⟩
      by_cases ht : t < history.length
      · simp only [stream, dif_pos ht]
        exact hstable.1 _ (List.get_mem history ⟨t, ht⟩)
      · simp only [stream, dif_neg ht]
        rw [← hbase]
        exact ⟨t - history.length, rfl⟩
    · intro x hx
      rw [← hbase] at hx
      obtain ⟨n, rfl⟩ := hx
      refine ⟨history.length + n, ?_⟩
      have hnot : ¬ history.length + n < history.length := by omega
      simp [stream, hnot]
  have hprefix : GenLimit.textPrefix stream history.length = history := by
    apply List.ext_get
    · simp
    · intro k h₁ h₂
      simp only [GenLimit.textPrefix, List.get_eq_getElem,
        List.getElem_map, List.getElem_range, stream, dif_pos h₂]
  obtain ⟨guess, hguess, T, hT⟩ := hIdentifies i stream hstreamP
  let t := max T history.length
  have hhistoryPrefix : history <+: GenLimit.textPrefix stream t := by
    rw [List.prefix_iff_eq_take]
    have hlen : history.length ≤ t := Nat.le_max_right _ _
    rw [← hprefix]
    rw [GenLimit.textPrefix, GenLimit.textPrefix, ← List.map_take]
    simp [hlen]
  obtain ⟨tail, htail⟩ := hhistoryPrefix
  have htailIn : HistoryIn tail (F.language i) := by
    have hall := historyIn_textPrefix hstreamP t
    rw [← htail, historyIn_append] at hall
    exact hall.2
  have hMhistory : M history = guess := by
    calc
      M history = M (history ++ tail) :=
        (hstable.2 tail htailIn).symm
      _ = M (GenLimit.textPrefix stream t) := by rw [htail]
      _ = guess := hT t (Nat.le_max_left _ _)
  rw [hMhistory]
  exact hguess

private theorem stabilizing_history_isTellTale
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    (hIdentifies :
      SemanticallyIdentifies M F.language)
    {i : ℕ} {history : List ℕ}
    (hstable : SyntacticallyStabilizing M (F.language i) history) :
    IsTellTale F.language i history.toFinset := by
  constructor
  · intro x hx
    exact hstable.1 x (by simpa using hx)
  · intro j hhistoryJ hji
    have hhistoryInJ : HistoryIn history (F.language j) := by
      intro x hx
      exact hhistoryJ (by simpa using hx)
    have hstableJ :
        SyntacticallyStabilizing M (F.language j) history := by
      refine ⟨hhistoryInJ, ?_⟩
      intro extension hextension
      exact hstable.2 extension (hextension.mono hji)
    have hi := stabilizing_guess_denotes F M hIdentifies hstable
    have hj := stabilizing_guess_denotes F M hIdentifies hstableJ
    have hij : F.language i = F.language j := hi.symm.trans hj
    exact hij.subset

private theorem lockingEmitter_isEnumeratedTellTale
    (F : EffectiveIndexedFamily) (M : EffectiveIdentifier)
    (hIdentifies :
      SemanticallyIdentifies M F.language)
    (i : ℕ) :
    IsEnumeratedTellTale F.language i
      (enumeratedSet (lockingEmitter F M) i) := by
  obtain ⟨history, hstable, N, heventual⟩ :=
    provisionalHistory_eventually_stabilizing F M hIdentifies i
  have hfinite :=
    enumeratedSet_lockingEmitter_finite F M heventual
  have hsubset : enumeratedSet (lockingEmitter F M) i ⊆ F.language i := by
    intro x hx
    obtain ⟨stage, hstage⟩ := hx
    exact lockingEmitter_mem_language F M hstage
  have hhistorySubset :=
    stabilizing_history_subset_enumerated F M heventual
  have hTell := stabilizing_history_isTellTale F M hIdentifies hstable
  refine ⟨hfinite, hsubset, ?_⟩
  intro j henumJ hji
  exact hTell.2 j (hhistorySubset.trans henumJ) hji

/-! ## Theorem 1 and Corollary 1 -/

/-- Necessity half of Angluin's effective Theorem 1. -/
theorem effectiveInferrable_conditionOne
    {F : EffectiveIndexedFamily} (h : EffectiveInferrable F) :
    ConditionOne F := by
  obtain ⟨M, hM, hIdentifies⟩ := h
  exact ⟨lockingEmitter F M, lockingEmitter_computable F hM,
    lockingEmitter_isEnumeratedTellTale F M hIdentifies⟩

/-- Angluin's effective Theorem 1. -/
theorem theoremOne (F : EffectiveIndexedFamily) :
    TheoremOneStatement F :=
  ⟨effectiveInferrable_conditionOne,
    ConditionOne.effective_sufficiency⟩

/-! ## Corollary 1 (semantic erasure) -/

/-- Angluin's Corollary 1, obtained by erasing the learner's computability and
applying semantic finite-tell-tale necessity. -/
theorem effectiveInferrable_conditionTwo
    {F : EffectiveIndexedFamily} (h : EffectiveInferrable F) :
    ConditionTwo F.language := by
  obtain ⟨M, _hMComputable, hIdentifies⟩ := h
  exact conditionTwo_of_semanticallyIdentifiable F.language
    ⟨M, hIdentifies⟩

theorem corollaryOne (F : EffectiveIndexedFamily) :
    CorollaryOneStatement F :=
  effectiveInferrable_conditionTwo

end GenLimit.Angluin
