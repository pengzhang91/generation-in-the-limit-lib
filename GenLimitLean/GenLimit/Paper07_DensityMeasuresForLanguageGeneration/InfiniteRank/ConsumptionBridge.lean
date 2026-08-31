import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.ReservationLedger
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.OneTenth

/-!
# First-consumption charging from permanent reservations

This module isolates the token-source interface needed by the
first-consumption argument in Kleinberg--Wei's infinite-rank construction.
A valid finite ledger supplies one such source but forces the demand type to
be finite.  A historical pair family over time-indexed valid snapshots can
supply a source without that finite-snapshot restriction.

The operational schedule records append-time freshness, consumption before a
deadline, and queue priority only at or after the reservation round.  Its charge is
the generator output at the first round consuming either token.  The charge
is strictly earlier in target order and injective separately on input-first
and output-first demands.  Without an additional cross-class invariant its
fibers have capacity two; with that invariant it is globally injective.

The remaining schedule fields are the exact semantic obligations needed from
the dynamic algorithm.  In particular, ledger uniqueness alone does not
prove queue priority, consumption deadlines, or cross-class separation.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
namespace FirstConsumptionBridge

open ReservationLedger

/-- A value has been used strictly before round `t`, either as input or
output.  Inputs may repeat. -/
def UsedBefore {Value : Type*}
    (input output : ℕ → Value) (t : ℕ) (x : Value) : Prop :=
  ∃ s < t, input s = x ∨ output s = x

/-- A value is consumed at one round by either participant. -/
def ConsumedAt {Value : Type*}
    (input output : ℕ → Value) (t : ℕ) (x : Value) : Prop :=
  input t = x ∨ output t = x

/-- Two side-tagged records selected from one permanent ledger.  Injective
event labels prevent two demands from reusing one round/edge pair. -/
structure LedgerPairFamily
    (Edge Demand : Type*) (ledger : Ledger Edge) where
  round : Demand → ℕ
  edge : Demand → Edge
  event_injective :
    Function.Injective fun d => (round d, edge d)
  token : Demand → ReservationSide → ℕ
  record_mem :
    ∀ d side,
      ({ tag := ⟨round d, edge d, side⟩,
          value := token d side } : Reservation Edge) ∈ ledger

/-- Ledger string uniqueness and injective event labels make the
`(demand, side)` token assignment injective. -/
theorem LedgerPairFamily.token_injective
    {Edge Demand : Type*} {ledger : Ledger Edge}
    (family : LedgerPairFamily Edge Demand ledger)
    (hValid : Valid ledger) :
    Function.Injective
      (fun p : Demand × ReservationSide =>
        family.token p.1 p.2) := by
  intro left right hValue
  let leftRecord : Reservation Edge :=
    { tag :=
        ⟨family.round left.1, family.edge left.1, left.2⟩
      value := family.token left.1 left.2 }
  let rightRecord : Reservation Edge :=
    { tag :=
        ⟨family.round right.1, family.edge right.1, right.2⟩
      value := family.token right.1 right.2 }
  have hRecord : leftRecord = rightRecord := by
    apply reservation_eq_of_value_eq hValid
    · exact family.record_mem left.1 left.2
    · exact family.record_mem right.1 right.2
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

/-- The charging schedule needs only reservation times, physical tokens, and
global token injectivity.  Concrete finite snapshots and time-indexed ledger
histories both project to this interface. -/
structure TokenSource (Demand : Type*) where
  round : Demand → ℕ
  token : Demand → ReservationSide → ℕ
  token_injective :
    Function.Injective
      (fun p : Demand × ReservationSide =>
        token p.1 p.2)

/-- A valid finite ledger snapshot supplies a token source.  Such a source
can index only finitely many demands; infinite runs use `LedgerHistory`. -/
def LedgerPairFamily.toTokenSource
    {Edge Demand : Type*} {ledger : Ledger Edge}
    (family : LedgerPairFamily Edge Demand ledger)
    (hValid : Valid ledger) :
    TokenSource Demand where
  round := family.round
  token := family.token
  token_injective := family.token_injective hValid

/-- One finite ledger cannot contain distinct token pairs for infinitely many
demands. -/
theorem LedgerPairFamily.finite_demand
    {Edge Demand : Type*} {ledger : Ledger Edge}
    (family : LedgerPairFamily Edge Demand ledger)
    (hValid : Valid ledger) :
    Finite Demand := by
  let firstToken : Demand → ℕ :=
    fun d => family.token d .first
  have hFirstInjective : Function.Injective firstToken := by
    intro left right hValue
    have hPair :
        (left, ReservationSide.first) =
          (right, ReservationSide.first) :=
      family.token_injective hValid hValue
    exact congrArg Prod.fst hPair
  have hRange :
      Set.range firstToken ⊆
        (ReservationLedger.stringRange ledger : Set ℕ) := by
    rintro value ⟨d, rfl⟩
    change firstToken d ∈ ReservationLedger.stringRange ledger
    rw [ReservationLedger.mem_stringRange]
    exact
      ⟨({ tag :=
            ⟨family.round d, family.edge d, .first⟩,
          value := family.token d .first } :
          Reservation Edge),
        family.record_mem d .first, rfl⟩
  have hRangeFinite : (Set.range firstToken).Finite :=
    (ReservationLedger.stringRange ledger).finite_toSet.subset hRange
  have hUnivFinite : (Set.univ : Set Demand).Finite := by
    apply Set.Finite.of_finite_image (f := firstToken)
    · simpa only [Set.image_univ] using hRangeFinite
    · exact hFirstInjective.injOn
  exact Set.finite_univ_iff.mp hUnivFinite

/-! ## Permanent provenance under consumption -/

/-- Mark one input and output as used without deleting ledger provenance. -/
def consume {Edge : Type*}
    (state : TaggedOutputState Edge) (input output : ℕ) :
    TaggedOutputState Edge where
  used := insert output (insert input state.used)
  ledger := state.ledger
  previousOutput := some output
  valid := state.valid

@[simp] theorem consume_used {Edge : Type*}
    (state : TaggedOutputState Edge) (input output : ℕ) :
    (consume state input output).used =
      insert output (insert input state.used) :=
  rfl

@[simp] theorem consume_ledger {Edge : Type*}
    (state : TaggedOutputState Edge) (input output : ℕ) :
    (consume state input output).ledger = state.ledger :=
  rfl

@[simp] theorem consume_previousOutput {Edge : Type*}
    (state : TaggedOutputState Edge) (input output : ℕ) :
    (consume state input output).previousOutput = some output :=
  rfl

/-- One consumption step erases exactly the current input and output from the
active-queue view. -/
theorem activeQueue_consume {Edge : Type*}
    (state : TaggedOutputState Edge) (input output : ℕ) :
    activeQueue
        (consume state input output).ledger
        (consume state input output).used =
      ((activeQueue state.ledger state.used).erase input).erase output := by
  classical
  ext x
  simp [activeQueue, consume, and_assoc, and_left_comm, and_comm]

/-- A previously active reservation that disappears in one step equals the
current input or output. -/
theorem eq_input_or_output_of_active_not_active_after
    {Edge : Type*} {state : TaggedOutputState Edge}
    {input output x : ℕ}
    (hBefore : x ∈ activeQueue state.ledger state.used)
    (hAfter :
      x ∉ activeQueue
        (consume state input output).ledger
        (consume state input output).used) :
    x = input ∨ x = output := by
  by_contra hConsumed
  have hInput : x ≠ input := by
    intro hEq
    exact hConsumed (Or.inl hEq)
  have hOutput : x ≠ output := by
    intro hEq
    exact hConsumed (Or.inr hEq)
  apply hAfter
  rw [activeQueue_consume]
  simp [hInput, hOutput, hBefore]

/-- Values consumed strictly before round `t`. -/
def consumedBeforeSet
    (input output : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).image input ∪ (Finset.range t).image output

@[simp] theorem mem_consumedBeforeSet
    {input output : ℕ → ℕ} {t x : ℕ} :
    x ∈ consumedBeforeSet input output t ↔
      UsedBefore input output t x := by
  classical
  simp only [consumedBeforeSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_range, UsedBefore]
  constructor
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inr rfl⟩
  · rintro ⟨s, hs, hInput | hOutput⟩
    · left
      exact ⟨s, hs, hInput⟩
    · right
      exact ⟨s, hs, hOutput⟩

/-! ## Reservation-time-aware schedules -/

/-- An operational schedule whose tokens come from a globally injective
token source.

`token_fresh_at_reservation` connects allocation-time freshness to the
input/output history.  `priority_available` explicitly requires that the
reservation already exists at the round where queue priority is invoked.
Positions refer to the fixed target ordering, independently of the ambient
natural values used by the fallback implementation. -/
structure Schedule
    (Demand : Type*) (input output : ℕ → ℕ) where
  family : TokenSource Demand
  tokenPosition : Demand → ReservationSide → ℕ
  outputPosition : ℕ → ℕ
  outputPosition_injective : Function.Injective outputPosition
  deadline : Demand → ℕ
  keyPosition : Demand → ℕ
  token_fresh_at_reservation :
    ∀ d side,
      ¬ UsedBefore input output
        (family.round d) (family.token d side)
  consumed_before :
    ∀ d side,
      UsedBefore input output (deadline d) (family.token d side)
  output_token_position :
    ∀ d side t,
      output t = family.token d side →
        outputPosition t = tokenPosition d side
  priority_available :
    ∀ d side t,
      family.round d ≤ t →
      t < deadline d →
      ¬ UsedBefore input output t (family.token d side) →
      input t ≠ family.token d side →
      outputPosition t ≤ tokenPosition d side
  tokenPosition_le_key :
    ∀ d side, tokenPosition d side ≤ keyPosition d
  key_not_output :
    ∀ d t, outputPosition t ≠ keyPosition d

namespace Schedule

/-- Physical-token injectivity is supplied by the schedule's token source. -/
theorem token_injective
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output) :
    Function.Injective
      (fun p : Demand × ReservationSide =>
        schedule.family.token p.1 p.2) :=
  schedule.family.token_injective

/-- First round consuming one specified side of a demand's pair. -/
noncomputable def firstUse
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) (side : ReservationSide) : ℕ := by
  classical
  exact Nat.find (schedule.consumed_before d side)

theorem firstUse_lt_deadline
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) (side : ReservationSide) :
    schedule.firstUse d side < schedule.deadline d := by
  classical
  exact (Nat.find_spec (schedule.consumed_before d side)).1

theorem consumedAt_firstUse
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) (side : ReservationSide) :
    ConsumedAt input output (schedule.firstUse d side)
      (schedule.family.token d side) := by
  classical
  exact (Nat.find_spec (schedule.consumed_before d side)).2

theorem not_usedBefore_firstUse
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) (side : ReservationSide) :
    ¬ UsedBefore input output (schedule.firstUse d side)
      (schedule.family.token d side) := by
  classical
  rintro ⟨s, hs, hConsumed⟩
  have hmin : schedule.firstUse d side ≤ s :=
    Nat.find_min'
      (schedule.consumed_before d side)
      ⟨lt_trans hs (schedule.firstUse_lt_deadline d side),
        hConsumed⟩
  exact (Nat.not_lt_of_ge hmin) hs

/-- Append-time freshness forces first consumption to occur no earlier than
reservation. -/
theorem reservationRound_le_firstUse
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) (side : ReservationSide) :
    schedule.family.round d ≤ schedule.firstUse d side := by
  by_contra hNotLe
  have hLt :
      schedule.firstUse d side < schedule.family.round d :=
    Nat.lt_of_not_ge hNotLe
  apply schedule.token_fresh_at_reservation d side
  exact
    ⟨schedule.firstUse d side, hLt,
      schedule.consumedAt_firstUse d side⟩

/-- The first-consumed side, breaking a tie toward `.first`. -/
noncomputable def chosenSide
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) : ReservationSide :=
  if schedule.firstUse d .first ≤ schedule.firstUse d .second then
    .first
  else
    .second

/-- First round consuming either token of the pair. -/
noncomputable def chargeRound
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) : ℕ :=
  min (schedule.firstUse d .first) (schedule.firstUse d .second)

theorem firstUse_chosenSide
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    schedule.firstUse d (schedule.chosenSide d) =
      schedule.chargeRound d := by
  classical
  unfold chosenSide chargeRound
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (Nat.le_of_not_ge h)).symm

theorem chargeRound_lt_deadline
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    schedule.chargeRound d < schedule.deadline d := by
  rw [← schedule.firstUse_chosenSide d]
  exact schedule.firstUse_lt_deadline d (schedule.chosenSide d)

theorem reservationRound_le_chargeRound
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    schedule.family.round d ≤ schedule.chargeRound d := by
  unfold chargeRound
  exact
    le_min
      (schedule.reservationRound_le_firstUse d .first)
      (schedule.reservationRound_le_firstUse d .second)

theorem consumedAt_chargeRound
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    ConsumedAt input output (schedule.chargeRound d)
      (schedule.family.token d (schedule.chosenSide d)) := by
  rw [← schedule.firstUse_chosenSide d]
  exact schedule.consumedAt_firstUse d (schedule.chosenSide d)

/-- The side opposite `chosenSide`. -/
noncomputable def otherSide
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) : ReservationSide :=
  match schedule.chosenSide d with
  | .first => .second
  | .second => .first

theorem otherSide_ne_chosenSide
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    schedule.otherSide d ≠ schedule.chosenSide d := by
  generalize hSide : schedule.chosenSide d = side
  cases side <;> simp [otherSide, hSide]

theorem chargeRound_le_firstUse_other
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    schedule.chargeRound d ≤
      schedule.firstUse d (schedule.otherSide d) := by
  unfold chargeRound otherSide chosenSide
  split_ifs with h
  · exact min_le_right _ _
  · exact min_le_left _ _

theorem other_not_usedBefore_chargeRound
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    ¬ UsedBefore input output (schedule.chargeRound d)
      (schedule.family.token d (schedule.otherSide d)) := by
  classical
  rintro ⟨s, hs, hConsumed⟩
  have hFirstLe :
      schedule.firstUse d (schedule.otherSide d) ≤ s :=
    Nat.find_min'
      (schedule.consumed_before d (schedule.otherSide d))
      ⟨lt_trans hs (schedule.chargeRound_lt_deadline d),
        hConsumed⟩
  have hChargeLe :
      schedule.chargeRound d ≤
        schedule.firstUse d (schedule.otherSide d) :=
    schedule.chargeRound_le_firstUse_other d
  exact (Nat.not_lt_of_ge (le_trans hChargeLe hFirstLe)) hs

/-- Output position at the first consumption of a pair. -/
noncomputable def charge
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) : ℕ :=
  schedule.outputPosition (schedule.chargeRound d)

/-- Whether the first pair consumption occurs on the input side. -/
def InputFirst
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) : Prop :=
  input (schedule.chargeRound d) =
    schedule.family.token d (schedule.chosenSide d)

theorem outputFirst_of_not_inputFirst
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand)
    (hNotInput : ¬ schedule.InputFirst d) :
    output (schedule.chargeRound d) =
      schedule.family.token d (schedule.chosenSide d) := by
  rcases schedule.consumedAt_chargeRound d with hInput | hOutput
  · exact (hNotInput hInput).elim
  · exact hOutput

/-- At first consumption, either the chosen token is output or input consumes
it while the other already-reserved token remains available. -/
theorem charge_le_key
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    schedule.charge d ≤ schedule.keyPosition d := by
  by_cases hInput : schedule.InputFirst d
  · have hInputNeOther :
        input (schedule.chargeRound d) ≠
          schedule.family.token d (schedule.otherSide d) := by
      intro hEq
      have hTokens :
          schedule.family.token d (schedule.chosenSide d) =
            schedule.family.token d (schedule.otherSide d) := by
        rw [← hInput, hEq]
      have hPairs :
          (d, schedule.chosenSide d) =
            (d, schedule.otherSide d) :=
        schedule.token_injective hTokens
      exact schedule.otherSide_ne_chosenSide d
        (congrArg Prod.snd hPairs).symm
    calc
      schedule.charge d
          ≤ schedule.tokenPosition d (schedule.otherSide d) := by
        exact schedule.priority_available
          d (schedule.otherSide d) (schedule.chargeRound d)
          (schedule.reservationRound_le_chargeRound d)
          (schedule.chargeRound_lt_deadline d)
          (schedule.other_not_usedBefore_chargeRound d)
          hInputNeOther
      _ ≤ schedule.keyPosition d :=
        schedule.tokenPosition_le_key d (schedule.otherSide d)
  · have hOutput := schedule.outputFirst_of_not_inputFirst d hInput
    calc
      schedule.charge d =
          schedule.tokenPosition d (schedule.chosenSide d) := by
        exact schedule.output_token_position
          d (schedule.chosenSide d) (schedule.chargeRound d) hOutput
      _ ≤ schedule.keyPosition d :=
        schedule.tokenPosition_le_key d (schedule.chosenSide d)

/-- A missing demand charges a strictly earlier target position. -/
theorem charge_lt_key
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (d : Demand) :
    schedule.charge d < schedule.keyPosition d := by
  apply Nat.lt_of_le_of_ne (schedule.charge_le_key d)
  exact schedule.key_not_output d (schedule.chargeRound d)

theorem chargeRound_eq_of_charge_eq
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    {left right : Demand}
    (hCharge : schedule.charge left = schedule.charge right) :
    schedule.chargeRound left = schedule.chargeRound right :=
  schedule.outputPosition_injective hCharge

/-- The charge is injective among input-first demands.  Repeated input values
do not matter because equal output positions force the same round. -/
theorem charge_injectiveOn_inputFirst
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output) :
    Set.InjOn schedule.charge {d | schedule.InputFirst d} := by
  intro left hLeft right hRight hCharge
  have hRound := schedule.chargeRound_eq_of_charge_eq hCharge
  have hToken :
      schedule.family.token left (schedule.chosenSide left) =
        schedule.family.token right (schedule.chosenSide right) := by
    rw [← hLeft, ← hRight, hRound]
  have hPair :
      (left, schedule.chosenSide left) =
        (right, schedule.chosenSide right) :=
    schedule.token_injective hToken
  exact congrArg Prod.fst hPair

/-- The charge is injective among output-first demands. -/
theorem charge_injectiveOn_outputFirst
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output) :
    Set.InjOn schedule.charge {d | ¬ schedule.InputFirst d} := by
  intro left hLeft right hRight hCharge
  have hRound := schedule.chargeRound_eq_of_charge_eq hCharge
  have hLeftOutput :=
    schedule.outputFirst_of_not_inputFirst left hLeft
  have hRightOutput :=
    schedule.outputFirst_of_not_inputFirst right hRight
  have hToken :
      schedule.family.token left (schedule.chosenSide left) =
        schedule.family.token right (schedule.chosenSide right) := by
    rw [← hLeftOutput, ← hRightOutput, hRound]
  have hPair :
      (left, schedule.chosenSide left) =
        (right, schedule.chosenSide right) :=
    schedule.token_injective hToken
  exact congrArg Prod.fst hPair

/-- The exact residual premise needed for the printed globally injective
single charge: input-first and output-first demands may not hit one output. -/
def NoCrossCollision
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output) : Prop :=
  ∀ inputDemand outputDemand,
    schedule.InputFirst inputDemand →
    ¬ schedule.InputFirst outputDemand →
    schedule.charge inputDemand ≠ schedule.charge outputDemand

/-- Cross-class separation upgrades the two classwise injections to global
injectivity. -/
theorem charge_injective
    {Demand : Type*} {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (hCross : schedule.NoCrossCollision) :
    Function.Injective schedule.charge := by
  intro left right hCharge
  by_cases hLeft : schedule.InputFirst left
  · by_cases hRight : schedule.InputFirst right
    · exact schedule.charge_injectiveOn_inputFirst hLeft hRight hCharge
    · exact (hCross left right hLeft hRight hCharge).elim
  · by_cases hRight : schedule.InputFirst right
    · exact (hCross right left hRight hLeft hCharge.symm).elim
    · exact schedule.charge_injectiveOn_outputFirst hLeft hRight hCharge

/-- Without cross-class separation, every output charge has capacity two. -/
theorem card_le_two_mul_output
    {Demand : Type*}
    [DecidableEq Demand]
    {input output : ℕ → ℕ}
    (schedule : Schedule Demand input output)
    (source : Finset Demand) (target : Finset ℕ)
    (hmaps : Set.MapsTo schedule.charge source target) :
    source.card ≤ 2 * target.card := by
  classical
  let inputSource :=
    source.filter fun d => schedule.InputFirst d
  let outputSource :=
    source.filter fun d => ¬ schedule.InputFirst d
  have hPartition : source = inputSource ∪ outputSource := by
    ext d
    by_cases h : schedule.InputFirst d <;>
      simp [inputSource, outputSource, h]
  have hDisjoint : Disjoint inputSource outputSource := by
    rw [Finset.disjoint_left]
    intro d hIn hOut
    exact (Finset.mem_filter.mp hOut).2
      (Finset.mem_filter.mp hIn).2
  have hInputMaps :
      Set.MapsTo schedule.charge inputSource target := by
    intro d hd
    apply hmaps
    exact (Finset.mem_filter.mp hd).1
  have hOutputMaps :
      Set.MapsTo schedule.charge outputSource target := by
    intro d hd
    apply hmaps
    exact (Finset.mem_filter.mp hd).1
  have hInputInj :
      Set.InjOn schedule.charge inputSource := by
    intro left hLeft right hRight hEq
    apply schedule.charge_injectiveOn_inputFirst
    · exact (Finset.mem_filter.mp hLeft).2
    · exact (Finset.mem_filter.mp hRight).2
    · exact hEq
  have hOutputInj :
      Set.InjOn schedule.charge outputSource := by
    intro left hLeft right hRight hEq
    apply schedule.charge_injectiveOn_outputFirst
    · exact (Finset.mem_filter.mp hLeft).2
    · exact (Finset.mem_filter.mp hRight).2
    · exact hEq
  have hInputCard : inputSource.card ≤ target.card :=
    card_le_of_injective_charge
      inputSource target schedule.charge hInputMaps hInputInj
  have hOutputCard : outputSource.card ≤ target.card :=
    card_le_of_injective_charge
      outputSource target schedule.charge hOutputMaps hOutputInj
  rw [hPartition, Finset.card_union_of_disjoint hDisjoint]
  omega

end Schedule
end FirstConsumptionBridge
end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
