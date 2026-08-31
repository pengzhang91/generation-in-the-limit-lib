import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.RecursiveHistory

/-!
# The recursive run supplies a global token source

The infinite-rank construction keeps only a finite reservation ledger at any
one round, while its append-only history collects reservation events across
the run.  This module selects the canonical pair created by every actual
`(round, edge)` event in `RecursiveHistory.run` and packages those pairs as
the global `TokenSource` required by the first-consumption charging argument.

This closes the bookkeeping step from the concrete recursive run to the
history-backed source.  Consumption deadlines and transport from ambient
natural-number order to positions in the target language remain separate
dynamic obligations.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
namespace FirstConsumptionBridge
namespace RecursiveHistory

open ReservationLedger

/-- An actual reservation event in the recursive run: an edge together with
proof that it occurs in that round's duplicate-free batch. -/
abbrev RunDemand
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) :=
  Σ round : ℕ, {edge : Edge // edge ∈ spec.edgesAt round}

/-- The concrete pair allocated for one run demand.  The choice is harmless:
valid tagged ledgers make each tag's stored value unique. -/
noncomputable def reservedPair
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (d : RunDemand spec) : ℕ × ℕ := by
  classical
  let hPair :=
    reserved_pair_fresh_from_history spec d.1 d.2.2
  exact ⟨hPair.choose, hPair.choose_spec.choose⟩

theorem reservedPair_first_mem
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (d : RunDemand spec) :
    ({ tag := firstTag d.1 d.2.1,
        value := (reservedPair spec d).1 } :
      Reservation Edge) ∈ (reservedAt spec d.1).ledger := by
  classical
  let hPair :=
    reserved_pair_fresh_from_history spec d.1 d.2.2
  simpa [reservedPair, hPair] using hPair.choose_spec.choose_spec.1

theorem reservedPair_second_mem
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (d : RunDemand spec) :
    ({ tag := secondTag d.1 d.2.1,
        value := (reservedPair spec d).2 } :
      Reservation Edge) ∈ (reservedAt spec d.1).ledger := by
  classical
  let hPair :=
    reserved_pair_fresh_from_history spec d.1 d.2.2
  simpa [reservedPair, hPair] using hPair.choose_spec.choose_spec.2.1

theorem reservedPair_first_fresh
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (d : RunDemand spec) :
    ¬UsedBefore spec.input (outputAt spec) d.1
      (reservedPair spec d).1 := by
  classical
  let hPair :=
    reserved_pair_fresh_from_history spec d.1 d.2.2
  have hFresh :
      (reservedPair spec d).1 ∉
        consumedBeforeSet spec.input (outputAt spec) d.1 := by
    simpa [reservedPair, hPair] using
      hPair.choose_spec.choose_spec.2.2.1
  intro hUsed
  exact hFresh ((mem_consumedBeforeSet).2 hUsed)

theorem reservedPair_second_fresh
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) (d : RunDemand spec) :
    ¬UsedBefore spec.input (outputAt spec) d.1
      (reservedPair spec d).2 := by
  classical
  let hPair :=
    reserved_pair_fresh_from_history spec d.1 d.2.2
  have hFresh :
      (reservedPair spec d).2 ∉
        consumedBeforeSet spec.input (outputAt spec) d.1 := by
    simpa [reservedPair, hPair] using
      hPair.choose_spec.choose_spec.2.2.2.1
  intro hUsed
  exact hFresh ((mem_consumedBeforeSet).2 hUsed)

/-- Every run demand chooses its pair from the append-only snapshot directly
after that demand's reservation round. -/
noncomputable def historicalPairFamily
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) :
    HistoricalLedgerPairFamily Edge (RunDemand spec) (ledgerHistory spec) where
  round := fun d => d.1
  edge := fun d => d.2.1
  event_injective := by
    intro left right hEvent
    have hRound : left.1 = right.1 :=
      congrArg Prod.fst hEvent
    cases left with
    | mk leftRound leftEdge =>
      cases right with
      | mk rightRound rightEdge =>
        dsimp only at hRound ⊢
        subst rightRound
        have hEdge : leftEdge.1 = rightEdge.1 :=
          congrArg Prod.snd hEvent
        cases Subtype.ext hEdge
        rfl
  token := fun d side =>
    match side with
    | .first => (reservedPair spec d).1
    | .second => (reservedPair spec d).2
  record_mem := by
    intro d side
    cases side with
    | first =>
        simpa [ledgerHistory] using reservedPair_first_mem spec d
    | second =>
        simpa [ledgerHistory] using reservedPair_second_mem spec d

/-- The complete recursive run now supplies the globally injective physical
token assignment consumed by `Schedule`. -/
noncomputable def runTokenSource
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) :
    TokenSource (RunDemand spec) :=
  (historicalPairFamily spec).toTokenSource

theorem runTokenSource_injective
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge) :
    Function.Injective
      (fun p : RunDemand spec × ReservationSide =>
        (runTokenSource spec).token p.1 p.2) :=
  (runTokenSource spec).token_injective

theorem runToken_fresh_at_reservation
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge)
    (d : RunDemand spec) (side : ReservationSide) :
    ¬UsedBefore spec.input (outputAt spec)
      ((runTokenSource spec).round d)
      ((runTokenSource spec).token d side) := by
  cases side with
  | first =>
      simpa [runTokenSource, historicalPairFamily] using
        reservedPair_first_fresh spec d
  | second =>
      simpa [runTokenSource, historicalPairFamily] using
        reservedPair_second_fresh spec d

/-- The recursive run's queue rule applies to every globally selected token
at every later round while that token remains unused. -/
theorem output_le_runToken_ambient
    {C : LanguageFamily} {Edge : Type*}
    (spec : RunSpec C Edge)
    (d : RunDemand spec) (side : ReservationSide) {round : ℕ}
    (hRound : (runTokenSource spec).round d ≤ round)
    (hUnused :
      ¬UsedBefore spec.input (outputAt spec) round
        ((runTokenSource spec).token d side))
    (hNeInput :
      (runTokenSource spec).token d side ≠ spec.input round) :
    outputAt spec round ≤ (runTokenSource spec).token d side := by
  cases side with
  | first =>
      apply output_le_reserved_value_ambient spec hRound
          (reservedPair_first_mem spec d) rfl hUnused
      simpa [runTokenSource, historicalPairFamily] using hNeInput
  | second =>
      apply output_le_reserved_value_ambient spec hRound
          (reservedPair_second_mem spec d) rfl hUnused
      simpa [runTokenSource, historicalPairFamily] using hNeInput

end RecursiveHistory
end FirstConsumptionBridge
end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
