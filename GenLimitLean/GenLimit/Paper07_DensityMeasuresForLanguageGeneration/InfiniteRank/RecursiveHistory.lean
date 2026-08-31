import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.HistoricalLedger

/-!
# Recursive observe--reserve--emit histories

This module packages the one-round historical-ledger bridge into an actual
recursive run.  The run observes the current input, reserves one
duplicate-free batch against that input and the exact prior used history,
emits from the enlarged active queue, and then records the input and output as
used.

The priority inequalities below use the ambient order on `ℕ`, exactly as the
current fallback implementation does.  They do not silently identify that
order with positions in a fixed target language.  A later charging schedule
must still supply the target-position comparison required by `Schedule`.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
namespace FirstConsumptionBridge
namespace RecursiveHistory

open ReservationLedger

/-- All exogenous data needed to run the operational reservation bridge. -/
structure RunSpec (C : LanguageFamily) (Edge : Type*) where
  familyInfinite : ∀ n, (C n).Infinite
  input : ℕ → ℕ
  current : ℕ → FiniteRankParent.FamilyPoint C
  reservationLanguage : Edge → Language
  reservationInfinite : ∀ edge, (reservationLanguage edge).Infinite
  edgesAt : ℕ → List Edge
  edgesAt_nodup : ∀ t, (edgesAt t).Nodup

/-- A state at the start of `round`, bundled with the chronology invariant
needed to allocate fresh event tags for that round. -/
structure ChronologicalState (Edge : Type*) (round : ℕ) where
  state : TaggedOutputState Edge
  roundsBefore : RoundsBefore state.ledger round

/-- The empty state is chronologically valid at round zero. -/
def initialState {Edge : Type*} : ChronologicalState Edge 0 where
  state :=
    { used := ∅
      ledger := []
      previousOutput := none
      valid := by
        simp [Valid, UniqueTags, UniqueStrings, tags, values] }
  roundsBefore := by
    simp [RoundsBefore]

/-- Duplicate-free current edges are sequentially fresh because the packaged
ledger contains records only from strictly earlier rounds. -/
noncomputable def freshAt
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ)
    (snapshot : ChronologicalState Edge round) :
    SequentiallyFresh snapshot.state.ledger
      (insert (spec.input round) snapshot.state.used) round
      spec.reservationLanguage spec.reservationInfinite
      (spec.edgesAt round) :=
  sequentiallyFresh_of_roundsBefore snapshot.state.ledger
    (insert (spec.input round) snapshot.state.used) round
    spec.reservationLanguage spec.reservationInfinite
    (spec.edgesAt round) (spec.edgesAt_nodup round)
    snapshot.roundsBefore

/-- One exact observe--reserve--emit transition. -/
noncomputable def advance
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ)
    (snapshot : ChronologicalState Edge round) :
    ChronologicalState Edge (round + 1) where
  state :=
    reserveBatchThenOutput spec.familyInfinite snapshot.state
      (spec.input round) round (spec.current round)
      spec.reservationLanguage spec.reservationInfinite
      (spec.edgesAt round) (freshAt spec round snapshot)
  roundsBefore :=
    reserveBatchThenOutput_roundsBefore_succ spec.familyInfinite
      snapshot.state (spec.input round) round (spec.current round)
      spec.reservationLanguage spec.reservationInfinite
      (spec.edgesAt round) (freshAt spec round snapshot)
      snapshot.roundsBefore

/-- The infinite operational run, indexed by its start-of-round snapshots. -/
noncomputable def run
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) :
    (round : ℕ) → ChronologicalState Edge round
  | 0 => initialState
  | round + 1 => advance spec round (run spec round)

/-- The tagged state at the start of a round. -/
noncomputable def stateAt
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    TaggedOutputState Edge :=
  (run spec round).state

/-- The canonical freshness proof used by the recursive run at one round. -/
noncomputable def runFreshAt
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    SequentiallyFresh (stateAt spec round).ledger
      (insert (spec.input round) (stateAt spec round).used) round
      spec.reservationLanguage spec.reservationInfinite
      (spec.edgesAt round) :=
  freshAt spec round (run spec round)

/-- The intermediate post-reservation, pre-emission state at one round. -/
noncomputable def reservedAt
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    TaggedOutputState Edge :=
  reserveBatchForInput (stateAt spec round)
    (spec.input round) round
    spec.reservationLanguage spec.reservationInfinite
    (spec.edgesAt round) (runFreshAt spec round)

/-- The output emitted at one round, after its reservations have been made. -/
noncomputable def outputAt
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) : ℕ :=
  taggedEmission spec.familyInfinite (reservedAt spec round)
    (spec.input round) (spec.current round)

@[simp] theorem stateAt_zero_used
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) :
    (stateAt spec 0).used = ∅ :=
  rfl

/-- Reservation does not prematurely consume the current input or output. -/
@[simp] theorem reservedAt_used
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    (reservedAt spec round).used = (stateAt spec round).used :=
  rfl

/-- The next state has exactly the ledger visible to the emission step. -/
@[simp] theorem stateAt_succ_ledger
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    (stateAt spec (round + 1)).ledger =
      (reservedAt spec round).ledger := by
  rfl

/-- The transition records exactly the output that was selected from the
post-reservation queue. -/
@[simp] theorem stateAt_succ_previousOutput
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    (stateAt spec (round + 1)).previousOutput =
      some (outputAt spec round) := by
  rfl

/-- One round adds exactly its observed input and emitted output to `used`. -/
@[simp] theorem stateAt_succ_used
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    (stateAt spec (round + 1)).used =
      insert (outputAt spec round)
        (insert (spec.input round) (stateAt spec round).used) := by
  rfl

/-- The historical ledger is literally append-only at every transition. -/
theorem stateAt_ledger_prefix_succ
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    (stateAt spec round).ledger <+:
      (stateAt spec (round + 1)).ledger := by
  simpa [stateAt, run, advance] using
    reserveBatchThenOutput_prefix spec.familyInfinite
      (run spec round).state (spec.input round) round
      (spec.current round) spec.reservationLanguage
      spec.reservationInfinite (spec.edgesAt round)
      (freshAt spec round (run spec round))

/-- Every snapshot contains reservations from strictly earlier rounds only. -/
theorem stateAt_roundsBefore
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    RoundsBefore (stateAt spec round).ledger round :=
  (run spec round).roundsBefore

/-- The recursive run realizes the existing abstract `LedgerHistory` API. -/
noncomputable def ledgerHistory
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) :
    LedgerHistory Edge where
  ledgerAt := fun round => (stateAt spec round).ledger
  validAt := fun round => (stateAt spec round).valid
  prefix_succ := stateAt_ledger_prefix_succ spec

/-- Prefix chronology for arbitrary earlier and later run snapshots. -/
theorem stateAt_ledger_prefix_of_le
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) {earlier later : ℕ}
    (h : earlier ≤ later) :
    (stateAt spec earlier).ledger <+:
      (stateAt spec later).ledger :=
  (ledgerHistory spec).prefix_of_le h

/-- Exact successor equation for the finite history semantics. -/
theorem consumedBeforeSet_succ
    (input output : ℕ → ℕ) (round : ℕ) :
    consumedBeforeSet input output (round + 1) =
      insert (output round)
        (insert (input round) (consumedBeforeSet input output round)) := by
  classical
  ext x
  simp [consumedBeforeSet, Finset.range_add_one, or_left_comm]

/-- The operational state's `used` field is neither an over- nor
under-approximation: it is exactly the accumulated input/output history. -/
theorem stateAt_used_eq_consumedBeforeSet
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ) :
    (stateAt spec round).used =
      consumedBeforeSet spec.input (outputAt spec) round := by
  induction round with
  | zero =>
      simp [consumedBeforeSet]
  | succ round ih =>
      calc
        (stateAt spec (round + 1)).used =
            insert (outputAt spec round)
              (insert (spec.input round) (stateAt spec round).used) :=
          stateAt_succ_used spec round
        _ =
            insert (outputAt spec round)
              (insert (spec.input round)
                (consumedBeforeSet spec.input (outputAt spec) round)) := by
          rw [ih]
        _ = consumedBeforeSet spec.input (outputAt spec) (round + 1) :=
          (consumedBeforeSet_succ spec.input (outputAt spec) round).symm

/-- Membership in `used` is exactly the semantic `UsedBefore` predicate. -/
theorem mem_stateAt_used_iff_usedBefore
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round x : ℕ) :
    x ∈ (stateAt spec round).used ↔
      UsedBefore spec.input (outputAt spec) round x := by
  rw [stateAt_used_eq_consumedBeforeSet spec round]
  exact mem_consumedBeforeSet

/-- A record reserved at one round remains present in every later
post-reservation snapshot. -/
theorem reservedAt_record_mono
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) {reservationRound currentRound : ℕ}
    (hRound : reservationRound ≤ currentRound)
    {reservation : Reservation Edge}
    (hRecord : reservation ∈ (reservedAt spec reservationRound).ledger) :
    reservation ∈ (reservedAt spec currentRound).ledger := by
  rcases hRound.eq_or_lt with hEq | hLt
  · simpa [hEq] using hRecord
  · have hStart :
        reservation ∈ (stateAt spec (reservationRound + 1)).ledger := by
      simpa using hRecord
    have hAtCurrent :
        reservation ∈ (stateAt spec currentRound).ledger :=
      (stateAt_ledger_prefix_of_le spec hLt).subset hStart
    have hPrefix :
        (stateAt spec currentRound).ledger <+:
          (reservedAt spec currentRound).ledger := by
      simpa [reservedAt] using
        reserveBatchForInput_prefix (stateAt spec currentRound)
          (spec.input currentRound) currentRound
          spec.reservationLanguage spec.reservationInfinite
          (spec.edgesAt currentRound) (runFreshAt spec currentRound)
    exact hPrefix.subset hAtCurrent

/-- Historical queue priority for the recursive run.  If a reserved value has
not yet appeared in the exact input/output history and is not the current
input, then the current emitted value is no larger in ambient `ℕ` order.

This is the operational analogue of `Schedule.priority_available`; converting
it to that field still requires a target-language position comparison. -/
theorem output_le_reserved_value_ambient
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge)
    {reservationRound currentRound token : ℕ}
    (hRound : reservationRound ≤ currentRound)
    {reservation : Reservation Edge}
    (hRecord : reservation ∈ (reservedAt spec reservationRound).ledger)
    (hValue : reservation.value = token)
    (hUnused :
      ¬ UsedBefore spec.input (outputAt spec) currentRound token)
    (hNeInput : token ≠ spec.input currentRound) :
    outputAt spec currentRound ≤ token := by
  have hNotUsed : token ∉ (stateAt spec currentRound).used := by
    intro hUsed
    exact hUnused
      ((mem_stateAt_used_iff_usedBefore spec currentRound token).mp hUsed)
  have hActive :
      token ∈
        activeQueue (reservedAt spec currentRound).ledger
          (reservedAt spec currentRound).used := by
    rw [mem_activeQueue]
    refine
      ⟨⟨reservation,
          reservedAt_record_mono spec hRound hRecord,
          hValue⟩, ?_⟩
    simpa using hNotUsed
  exact
    taggedEmission_le_active spec.familyInfinite
      (reservedAt spec currentRound) (spec.input currentRound)
      (spec.current currentRound) hActive hNeInput

/-- A current reservation is fresh from the exact prior history and from the
just-observed current input. -/
theorem reserved_pair_fresh_from_history
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ)
    {edge : Edge} (hEdge : edge ∈ spec.edgesAt round) :
    ∃ first second,
      ({ tag := firstTag round edge, value := first } :
        Reservation Edge) ∈ (reservedAt spec round).ledger ∧
      ({ tag := secondTag round edge, value := second } :
        Reservation Edge) ∈ (reservedAt spec round).ledger ∧
      first ∉ consumedBeforeSet spec.input (outputAt spec) round ∧
      second ∉ consumedBeforeSet spec.input (outputAt spec) round ∧
      first ≠ spec.input round ∧
      second ≠ spec.input round ∧
      first ≠ second := by
  obtain ⟨first, second, hFirst, hSecond, hFirstFresh, hSecondFresh, hNe⟩ :=
    appendBatch_hasFreshPair (stateAt spec round).ledger
      (insert (spec.input round) (stateAt spec round).used) round
      spec.reservationLanguage spec.reservationInfinite
      (spec.edgesAt round) hEdge
  have hFirstHistory : first ∉ (stateAt spec round).used := by
    intro hUsed
    exact hFirstFresh (Finset.mem_insert_of_mem hUsed)
  have hSecondHistory : second ∉ (stateAt spec round).used := by
    intro hUsed
    exact hSecondFresh (Finset.mem_insert_of_mem hUsed)
  have hFirstInput : first ≠ spec.input round := by
    intro hEq
    exact hFirstFresh (by simp [hEq])
  have hSecondInput : second ≠ spec.input round := by
    intro hEq
    exact hSecondFresh (by simp [hEq])
  refine
    ⟨first, second, ?_, ?_, ?_, ?_, hFirstInput, hSecondInput, hNe⟩
  · exact hFirst
  · exact hSecond
  · rwa [← stateAt_used_eq_consumedBeforeSet spec round]
  · rwa [← stateAt_used_eq_consumedBeforeSet spec round]

/-- Same-round priority lifted to the recursive run.  The inequalities here
are solely in the ambient natural-number order. -/
theorem output_le_reserved_pair_ambient
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (round : ℕ)
    {edge : Edge} (hEdge : edge ∈ spec.edgesAt round) :
    ∃ first second,
      ({ tag := firstTag round edge, value := first } :
        Reservation Edge) ∈ (stateAt spec (round + 1)).ledger ∧
      ({ tag := secondTag round edge, value := second } :
        Reservation Edge) ∈ (stateAt spec (round + 1)).ledger ∧
      first ≠ second ∧
      outputAt spec round ≤ first ∧
      outputAt spec round ≤ second := by
  simpa [stateAt, run, advance, outputAt, reservedAt, runFreshAt] using
    reserveBatchThenOutput_pair spec.familyInfinite
      (run spec round).state (spec.input round) round
      (spec.current round) spec.reservationLanguage
      spec.reservationInfinite (spec.edgesAt round)
      (freshAt spec round (run spec round)) hEdge

end RecursiveHistory
end FirstConsumptionBridge
end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
