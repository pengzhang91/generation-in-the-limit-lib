import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.ConsumptionBridge

/-!
# Time-indexed tagged reservation history

A concrete algorithm has a finite reservation ledger at every round but may
create infinitely many reservations over its complete run.  Given a family
selecting records from those snapshots, this module proves global
physical-token injectivity by comparing two records in a common later ledger.
It also realizes the paper's observe--reserve--emit order: allocation excludes
the current input, tagged output uses the enlarged active queue, and both new
tokens satisfy the same-round priority inequality.  The projected output
transition is the normalized fallback primitive with no new fallback window.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
namespace FirstConsumptionBridge

open ReservationLedger

/-- A time-indexed sequence of valid finite ledgers whose provenance is
append-only. -/
structure LedgerHistory (Edge : Type*) where
  ledgerAt : ℕ → Ledger Edge
  validAt : ∀ t, Valid (ledgerAt t)
  prefix_succ : ∀ t, ledgerAt t <+: ledgerAt (t + 1)

namespace LedgerHistory

/-- Every earlier ledger remains a prefix of every later ledger. -/
theorem prefix_of_le
    {Edge : Type*} (history : LedgerHistory Edge)
    {s t : ℕ} (hst : s ≤ t) :
    history.ledgerAt s <+: history.ledgerAt t := by
  induction t, hst using Nat.le_induction with
  | base =>
      exact List.prefix_refl _
  | succ t hst ih =>
      exact ih.trans (history.prefix_succ t)

end LedgerHistory

/-- Each demand selects the two side records present in the finite ledger
immediately after its designated reservation event. -/
structure HistoricalLedgerPairFamily
    (Edge Demand : Type*) (history : LedgerHistory Edge) where
  round : Demand → ℕ
  edge : Demand → Edge
  event_injective :
    Function.Injective fun d => (round d, edge d)
  token : Demand → ReservationSide → ℕ
  record_mem :
    ∀ d side,
      ({ tag := ⟨round d, edge d, side⟩,
          value := token d side } : Reservation Edge) ∈
        history.ledgerAt (round d + 1)

/-- Append-only validity upgrades local record membership to global
injectivity of the physical `(demand, side)` token assignment. -/
theorem HistoricalLedgerPairFamily.token_injective
    {Edge Demand : Type*} {history : LedgerHistory Edge}
    (family : HistoricalLedgerPairFamily Edge Demand history) :
    Function.Injective
      (fun p : Demand × ReservationSide =>
        family.token p.1 p.2) := by
  intro left right hValue
  let commonStage :=
    max (family.round left.1 + 1) (family.round right.1 + 1)
  let leftRecord : Reservation Edge :=
    { tag :=
        ⟨family.round left.1, family.edge left.1, left.2⟩
      value := family.token left.1 left.2 }
  let rightRecord : Reservation Edge :=
    { tag :=
        ⟨family.round right.1, family.edge right.1, right.2⟩
      value := family.token right.1 right.2 }
  have hLeftPrefix :
      history.ledgerAt (family.round left.1 + 1) <+:
        history.ledgerAt commonStage :=
    history.prefix_of_le (Nat.le_max_left _ _)
  have hRightPrefix :
      history.ledgerAt (family.round right.1 + 1) <+:
        history.ledgerAt commonStage :=
    history.prefix_of_le (Nat.le_max_right _ _)
  have hLeftMem : leftRecord ∈ history.ledgerAt commonStage :=
    hLeftPrefix.subset (family.record_mem left.1 left.2)
  have hRightMem : rightRecord ∈ history.ledgerAt commonStage :=
    hRightPrefix.subset (family.record_mem right.1 right.2)
  have hRecord : leftRecord = rightRecord := by
    apply reservation_eq_of_value_eq (history.validAt commonStage)
    · exact hLeftMem
    · exact hRightMem
    · exact hValue
  have hTag : leftRecord.tag = rightRecord.tag :=
    congrArg Reservation.tag hRecord
  have hEvent :
      (family.round left.1, family.edge left.1) =
        (family.round right.1, family.edge right.1) := by
    apply Prod.ext
    · exact congrArg ReservationTag.round hTag
    · exact congrArg ReservationTag.edge hTag
  have hDemand : left.1 = right.1 :=
    family.event_injective hEvent
  have hSide : left.2 = right.2 :=
    congrArg ReservationTag.side hTag
  exact Prod.ext hDemand hSide

/-- A history-backed family supplies the generic token interface consumed by
the operational charging schedule. -/
def HistoricalLedgerPairFamily.toTokenSource
    {Edge Demand : Type*} {history : LedgerHistory Edge}
    (family : HistoricalLedgerPairFamily Edge Demand history) :
    TokenSource Demand where
  round := family.round
  token := family.token
  token_injective := family.token_injective

/-! ## One-round tagged output bridge -/

open FiniteRankParent
open FiniteRankFallback

/-- Emit from the active reservation queue union the currently identified
language, without adding the finite-rank fallback window. -/
noncomputable def taggedEmission
    {C : LanguageFamily} {Edge : Type*}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input : ℕ) (current : FamilyPoint C) : ℕ :=
  emittedAtStep hInfinite state.toOutputState input current none

/-- Preserve ledger provenance while recording the current input and tagged
emission as used. -/
noncomputable def taggedOutputStep
    {C : LanguageFamily} {Edge : Type*}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input : ℕ) (current : FamilyPoint C) :
    TaggedOutputState Edge :=
  consume state input
    (taggedEmission hInfinite state input current)

/-- Reserve a batch after seeing the current input but before selecting the
current output.  Allocation excludes the current input as well as all
previously used strings, while the pre-output used set remains unchanged so
the normalized output step records the round exactly once. -/
noncomputable def reserveBatchForInput
    {Edge : Type*}
    (state : TaggedOutputState Edge)
    (input round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger (insert input state.used) round
        language hInfinite edges) :
    TaggedOutputState Edge where
  used := state.used
  ledger :=
    appendBatch state.ledger (insert input state.used) round
      language hInfinite edges
  previousOutput := state.previousOutput
  valid :=
    appendBatch_valid state.ledger (insert input state.used) round
      language hInfinite edges state.valid hFresh

@[simp] theorem reserveBatchForInput_used
    {Edge : Type*}
    (state : TaggedOutputState Edge)
    (input round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger (insert input state.used) round
        language hInfinite edges) :
    (reserveBatchForInput state input round language hInfinite edges
      hFresh).used = state.used :=
  rfl

/-- Reserving the current batch retains the complete prior ledger. -/
theorem reserveBatchForInput_prefix
    {Edge : Type*}
    (state : TaggedOutputState Edge)
    (input round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger (insert input state.used) round
        language hInfinite edges) :
    state.ledger <+:
      (reserveBatchForInput state input round language hInfinite edges
        hFresh).ledger :=
  appendBatch_prefix state.ledger (insert input state.used) round
    language hInfinite edges

/-- Reserve the current batch, emit once from the enlarged active queue, and
record the current input/output as used. -/
noncomputable def reserveBatchThenOutput
    {C : LanguageFamily} {Edge : Type*}
    (hFamilyInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input round : ℕ)
    (current : FamilyPoint C)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger (insert input state.used) round
        language hInfinite edges) :
    TaggedOutputState Edge :=
  taggedOutputStep hFamilyInfinite
    (reserveBatchForInput state input round language hInfinite edges hFresh)
    input current

/-- A concrete reserve-then-output round retains the complete prior ledger. -/
theorem reserveBatchThenOutput_prefix
    {C : LanguageFamily} {Edge : Type*}
    (hFamilyInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input round : ℕ)
    (current : FamilyPoint C)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger (insert input state.used) round
        language hInfinite edges) :
    state.ledger <+:
      (reserveBatchThenOutput hFamilyInfinite state input round current
        language hInfinite edges hFresh).ledger := by
  simpa [reserveBatchThenOutput, taggedOutputStep, consume] using
    reserveBatchForInput_prefix state input round language hInfinite
      edges hFresh

/-- If the input ledger contains only earlier-round records, a concrete
reserve-then-output round advances the same chronology invariant. -/
theorem reserveBatchThenOutput_roundsBefore_succ
    {C : LanguageFamily} {Edge : Type*}
    (hFamilyInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input round : ℕ)
    (current : FamilyPoint C)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger (insert input state.used) round
        language hInfinite edges)
    (hRounds : RoundsBefore state.ledger round) :
    RoundsBefore
      (reserveBatchThenOutput hFamilyInfinite state input round current
        language hInfinite edges hFresh).ledger
      (round + 1) := by
  simpa [reserveBatchThenOutput, taggedOutputStep, consume] using
    appendBatch_roundsBefore_succ state.ledger
      (insert input state.used) round language hInfinite edges hRounds

private theorem outputState_eq
    {left right : OutputState}
    (hUsed : left.used = right.used)
    (hQueue : left.queue = right.queue)
    (hPrevious : left.previousOutput = right.previousOutput) :
    left = right := by
  cases left
  cases right
  simp_all

/-- The tagged consumption step is exactly the normalized no-new-fallback
step on the active-queue projection. -/
theorem taggedOutputStep_toOutputState
    {C : LanguageFamily} {Edge : Type*}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input : ℕ) (current : FamilyPoint C) :
    (taggedOutputStep hInfinite state input current).toOutputState =
      outputStep hInfinite state.toOutputState input current none := by
  classical
  apply outputState_eq
  · rfl
  · ext x
    simp [taggedOutputStep, taggedEmission, TaggedOutputState.toOutputState,
      consume, outputStep, emittedAtStep, priorityAtStep, activeQueue,
      and_assoc, and_left_comm, and_comm]
  · rfl

/-- Every active token distinct from the current input is a priority
candidate, so the tagged emission is no larger in ambient order. -/
theorem taggedEmission_le_active
    {C : LanguageFamily} {Edge : Type*}
    (hInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input : ℕ) (current : FamilyPoint C)
    {token : ℕ}
    (hActive : token ∈ activeQueue state.ledger state.used)
    (hTokenNeInput : token ≠ input) :
    taggedEmission hInfinite state input current ≤ token := by
  apply emittedAtStep_le_candidate
      hInfinite state.toOutputState input current none
  · have hUnused : token ∉ state.used :=
      (mem_activeQueue.mp hActive).2
    simpa [hTokenNeInput, hUnused]
  · left
    simpa [priorityAtStep, TaggedOutputState.toOutputState,
      hTokenNeInput] using hActive

/-- The concrete allocation-then-emission transition discharges queue
priority for both tokens of every newly reserved edge. -/
theorem reserveBatchForInput_pair_priority
    {C : LanguageFamily} {Edge : Type*}
    (hFamilyInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input round : ℕ)
    (current : FamilyPoint C)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger (insert input state.used) round
        language hInfinite edges)
    {edge : Edge} (hEdge : edge ∈ edges) :
    let reserved :=
      reserveBatchForInput state input round language hInfinite edges hFresh
    ∃ first second,
      ({ tag := firstTag round edge, value := first } :
        Reservation Edge) ∈ reserved.ledger ∧
      ({ tag := secondTag round edge, value := second } :
        Reservation Edge) ∈ reserved.ledger ∧
      first ≠ second ∧
      taggedEmission hFamilyInfinite reserved input current ≤ first ∧
      taggedEmission hFamilyInfinite reserved input current ≤ second := by
  classical
  dsimp only
  obtain
      ⟨first, second, hFirstRecord, hSecondRecord,
        hFirstFresh, hSecondFresh, hNe⟩ :=
    appendBatch_hasFreshPair state.ledger
      (insert input state.used) round language hInfinite edges hEdge
  have hFirstNotInput : first ≠ input := by
    intro hEq
    apply hFirstFresh
    simp [hEq]
  have hSecondNotInput : second ≠ input := by
    intro hEq
    apply hSecondFresh
    simp [hEq]
  have hFirstNotUsed : first ∉ state.used := by
    intro hUsed
    apply hFirstFresh
    exact Finset.mem_insert_of_mem hUsed
  have hSecondNotUsed : second ∉ state.used := by
    intro hUsed
    apply hSecondFresh
    exact Finset.mem_insert_of_mem hUsed
  have hFirstActive :
      first ∈
        activeQueue
          (reserveBatchForInput state input round language hInfinite edges
            hFresh).ledger
          (reserveBatchForInput state input round language hInfinite edges
            hFresh).used := by
    rw [mem_activeQueue]
    exact
      ⟨⟨({ tag := firstTag round edge, value := first } :
            Reservation Edge),
          hFirstRecord, rfl⟩,
        hFirstNotUsed⟩
  have hSecondActive :
      second ∈
        activeQueue
          (reserveBatchForInput state input round language hInfinite edges
            hFresh).ledger
          (reserveBatchForInput state input round language hInfinite edges
            hFresh).used := by
    rw [mem_activeQueue]
    exact
      ⟨⟨({ tag := secondTag round edge, value := second } :
            Reservation Edge),
          hSecondRecord, rfl⟩,
        hSecondNotUsed⟩
  refine
    ⟨first, second, hFirstRecord, hSecondRecord, hNe, ?_, ?_⟩
  · exact
      taggedEmission_le_active hFamilyInfinite
        (reserveBatchForInput state input round language hInfinite edges
          hFresh)
        input current hFirstActive hFirstNotInput
  · exact
      taggedEmission_le_active hFamilyInfinite
        (reserveBatchForInput state input round language hInfinite edges
          hFresh)
        input current hSecondActive hSecondNotInput

/-- The pair records and their same-round priority inequalities survive into
the post-output ledger, exactly the snapshot used by a historical family. -/
theorem reserveBatchThenOutput_pair
    {C : LanguageFamily} {Edge : Type*}
    (hFamilyInfinite : ∀ n, (C n).Infinite)
    (state : TaggedOutputState Edge)
    (input round : ℕ)
    (current : FamilyPoint C)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger (insert input state.used) round
        language hInfinite edges)
    {edge : Edge} (hEdge : edge ∈ edges) :
    ∃ first second,
      ({ tag := firstTag round edge, value := first } :
        Reservation Edge) ∈
          (reserveBatchThenOutput hFamilyInfinite state input round current
            language hInfinite edges hFresh).ledger ∧
      ({ tag := secondTag round edge, value := second } :
        Reservation Edge) ∈
          (reserveBatchThenOutput hFamilyInfinite state input round current
            language hInfinite edges hFresh).ledger ∧
      first ≠ second ∧
      taggedEmission hFamilyInfinite
          (reserveBatchForInput state input round language hInfinite edges
            hFresh)
          input current ≤ first ∧
      taggedEmission hFamilyInfinite
          (reserveBatchForInput state input round language hInfinite edges
            hFresh)
          input current ≤ second := by
  obtain
      ⟨first, second, hFirst, hSecond, hNe,
        hFirstPriority, hSecondPriority⟩ :=
    reserveBatchForInput_pair_priority hFamilyInfinite state input round
      current language hInfinite edges hFresh hEdge
  refine
    ⟨first, second, ?_, ?_, hNe, hFirstPriority, hSecondPriority⟩
  · simpa [reserveBatchThenOutput, taggedOutputStep, consume] using hFirst
  · simpa [reserveBatchThenOutput, taggedOutputStep, consume] using hSecond

end FirstConsumptionBridge
end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
