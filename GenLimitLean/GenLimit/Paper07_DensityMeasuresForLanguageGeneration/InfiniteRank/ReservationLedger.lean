import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Fallback

/-!
# Tagged fallback reservation ledger

An append-only reservation ledger for the Kleinberg--Wei
fallback construction.  The ledger retains the round, forest edge, and side
which created every reserved string.  Its active queue is derived by removing
used strings, rather than by deleting provenance from the ledger.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.ReservationLedger

open FiniteRankParent

/-- The two reservations created for one fallback event. -/
inductive ReservationSide where
  | first
  | second
  deriving DecidableEq

/-- Stable provenance for a reserved string.  `Edge` can be instantiated by
the actual frozen parent edge used by the repaired algorithm. -/
structure ReservationTag (Edge : Type*) where
  round : ℕ
  edge : Edge
  side : ReservationSide

theorem reservationTag_eq {Edge : Type*}
    {left right : ReservationTag Edge}
    (hRound : left.round = right.round)
    (hEdge : left.edge = right.edge)
    (hSide : left.side = right.side) :
    left = right := by
  cases left
  cases right
  simp_all

/-- A string together with the event which reserved it. -/
structure Reservation (Edge : Type*) where
  tag : ReservationTag Edge
  value : ℕ

/-- The chronological, append-only reservation history. -/
abbrev Ledger (Edge : Type*) := List (Reservation Edge)

/-- A concrete edge label available directly from the current family-point
API.  A repaired algorithm may use a stronger frozen-edge subtype instead. -/
abbrev FamilyEdge (C : LanguageFamily) :=
  FamilyPoint C × FamilyPoint C

/-- The tags already present in a ledger. -/
def tags {Edge : Type*} (ledger : Ledger Edge) :
    List (ReservationTag Edge) :=
  ledger.map Reservation.tag

/-- The reserved strings already present in a ledger. -/
def values {Edge : Type*} (ledger : Ledger Edge) : List ℕ :=
  ledger.map Reservation.value

/-- No reservation event is represented twice. -/
def UniqueTags {Edge : Type*} (ledger : Ledger Edge) : Prop :=
  (tags ledger).Nodup

/-- No string is charged to two reservation events. -/
def UniqueStrings {Edge : Type*} (ledger : Ledger Edge) : Prop :=
  (values ledger).Nodup

/-- The two collision-freedom invariants of a tagged ledger. -/
def Valid {Edge : Type*} (ledger : Ledger Edge) : Prop :=
  UniqueTags ledger ∧ UniqueStrings ledger

/-- A valid ledger gives each tag at most one reservation record. -/
theorem reservation_eq_of_tag_eq {Edge : Type*}
    {ledger : Ledger Edge} (hValid : Valid ledger)
    {left right : Reservation Edge}
    (hLeft : left ∈ ledger) (hRight : right ∈ ledger)
    (hTag : left.tag = right.tag) :
    left = right := by
  have hNodup :
      (ledger.map Reservation.tag).Nodup := by
    simpa [UniqueTags, tags] using hValid.1
  exact
    List.inj_on_of_nodup_map hNodup hLeft hRight hTag

/-- A valid ledger gives each reserved string exactly one provenance record. -/
theorem reservation_eq_of_value_eq {Edge : Type*}
    {ledger : Ledger Edge} (hValid : Valid ledger)
    {left right : Reservation Edge}
    (hLeft : left ∈ ledger) (hRight : right ∈ ledger)
    (hValue : left.value = right.value) :
    left = right := by
  have hNodup :
      (ledger.map Reservation.value).Nodup := by
    simpa [UniqueStrings, values] using hValid.2
  exact
    List.inj_on_of_nodup_map hNodup hLeft hRight hValue

/-- The two tags of an edge event have not already been allocated. -/
def EventFresh {Edge : Type*}
    (ledger : Ledger Edge) (round : ℕ) (edge : Edge) : Prop :=
  ReservationTag.mk round edge .first ∉ tags ledger ∧
    ReservationTag.mk round edge .second ∉ tags ledger

/-- Every reservation currently in the ledger was made at an earlier round.
This is a convenient inductive condition implying event-tag freshness. -/
def RoundsBefore {Edge : Type*}
    (ledger : Ledger Edge) (round : ℕ) : Prop :=
  ∀ reservation ∈ ledger, reservation.tag.round < round

theorem eventFresh_of_roundsBefore {Edge : Type*}
    {ledger : Ledger Edge} {round : ℕ} (edge : Edge)
    (hRounds : RoundsBefore ledger round) :
    EventFresh ledger round edge := by
  constructor <;> intro hTag
  · rcases List.mem_map.mp hTag with
      ⟨reservation, hReservation, hEq⟩
    have hlt := hRounds reservation hReservation
    have hr :
        reservation.tag.round = round :=
      congrArg ReservationTag.round hEq
    exact (Nat.ne_of_lt hlt) hr
  · rcases List.mem_map.mp hTag with
      ⟨reservation, hReservation, hEq⟩
    have hlt := hRounds reservation hReservation
    have hr :
        reservation.tag.round = round :=
      congrArg ReservationTag.round hEq
    exact (Nat.ne_of_lt hlt) hr

/-- The finite string range occupied by a ledger. -/
noncomputable def stringRange {Edge : Type*} (ledger : Ledger Edge) :
    Finset ℕ := by
  classical
  exact (values ledger).toFinset

/-- External used strings together with every historical reservation. -/
noncomputable def forbiddenRange {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ) : Finset ℕ := by
  classical
  exact used ∪ stringRange ledger

/-- The queue exposed to the existing output API: historical reservations
which have not yet been used. -/
noncomputable def activeQueue {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ) : Finset ℕ := by
  classical
  exact stringRange ledger \ used

/-- Output state with an append-only provenance ledger behind its finite
queue.  The `valid` field rules out tag and string collisions globally. -/
structure TaggedOutputState (Edge : Type*) where
  used : Finset ℕ
  ledger : Ledger Edge
  previousOutput : Option ℕ
  valid : Valid ledger

/-- Snapshot the ledger-backed state in the finite fallback-state shape.
This projection exposes the current used set, active queue, and previous
output; it does not claim that ledger transitions are equivalent to the
existing fallback transition system. -/
noncomputable def TaggedOutputState.toOutputState {Edge : Type*}
    (state : TaggedOutputState Edge) :
    FiniteRankFallback.OutputState where
  used := state.used
  queue := activeQueue state.ledger state.used
  previousOutput := state.previousOutput

@[simp] theorem mem_stringRange {Edge : Type*}
    {ledger : Ledger Edge} {x : ℕ} :
    x ∈ stringRange ledger ↔
      ∃ reservation ∈ ledger, reservation.value = x := by
  classical
  simp [stringRange, values]

@[simp] theorem mem_forbiddenRange {Edge : Type*}
    {ledger : Ledger Edge} {used : Finset ℕ} {x : ℕ} :
    x ∈ forbiddenRange ledger used ↔
      x ∈ used ∨ ∃ reservation ∈ ledger, reservation.value = x := by
  classical
  simp [forbiddenRange]

@[simp] theorem mem_activeQueue {Edge : Type*}
    {ledger : Ledger Edge} {used : Finset ℕ} {x : ℕ} :
    x ∈ activeQueue ledger used ↔
      (∃ reservation ∈ ledger, reservation.value = x) ∧ x ∉ used := by
  classical
  simp [activeQueue]

/-- The forbidden range really is finite when viewed as a set. -/
theorem forbiddenRange_finite {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ) :
    ((forbiddenRange ledger used : Finset ℕ) : Set ℕ).Finite :=
  (forbiddenRange ledger used).finite_toSet

/-- The queue projection is fresh by construction, independently of ledger
validity. -/
theorem activeQueue_disjoint_used {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ) :
    Disjoint (activeQueue ledger used) used := by
  classical
  rw [Finset.disjoint_left]
  intro x hxActive hxUsed
  exact (Finset.mem_sdiff.mp hxActive).2 hxUsed

theorem TaggedOutputState.toOutputState_queue_fresh {Edge : Type*}
    (state : TaggedOutputState Edge) :
    Disjoint state.toOutputState.queue state.toOutputState.used :=
  activeQueue_disjoint_used state.ledger state.used

/-- An infinite language contains two distinct strings outside any finite
forbidden range. -/
theorem exists_two_fresh
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ) :
    ∃ first second,
      first ∈ L ∧ second ∈ L ∧
      first ∉ forbidden ∧ second ∉ forbidden ∧
      first ≠ second := by
  obtain ⟨first, hfirstL, hfirstFresh⟩ :=
    hInfinite.exists_notMem_finset forbidden
  obtain ⟨second, hsecondL, hsecondFresh⟩ :=
    hInfinite.exists_notMem_finset (insert first forbidden)
  refine ⟨first, second, hfirstL, hsecondL, hfirstFresh, ?_, ?_⟩
  · exact fun hsecondForbidden =>
      hsecondFresh (Finset.mem_insert_of_mem hsecondForbidden)
  · intro hEq
    apply hsecondFresh
    rw [Finset.mem_insert]
    exact Or.inl hEq.symm

/-- The least member of an infinite language outside a finite forbidden
range.  This is the canonical primitive used by the reservation ledger. -/
noncomputable def leastFresh
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ) :
    ℕ := by
  classical
  exact Nat.find (hInfinite.exists_notMem_finset forbidden)

theorem leastFresh_spec
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ) :
    leastFresh L hInfinite forbidden ∈ L ∧
      leastFresh L hInfinite forbidden ∉ forbidden := by
  classical
  simpa [leastFresh] using
    Nat.find_spec (hInfinite.exists_notMem_finset forbidden)

/-- `leastFresh` is genuinely least among all admissible comparison
strings. -/
theorem leastFresh_le
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ)
    {comparison : ℕ}
    (hComparisonL : comparison ∈ L)
    (hComparisonFresh : comparison ∉ forbidden) :
    leastFresh L hInfinite forbidden ≤ comparison := by
  classical
  exact Nat.find_min'
    (hInfinite.exists_notMem_finset forbidden)
    ⟨hComparisonL, hComparisonFresh⟩

/-- The canonical collision-free pair: first take the least fresh language
member, then the least member fresh even after inserting the first choice.
Thus this is the first two elements of `L \ forbidden` in natural order. -/
noncomputable def allocatePair
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ) :
    ℕ × ℕ :=
  let first := leastFresh L hInfinite forbidden
  (first, leastFresh L hInfinite (insert first forbidden))

theorem allocatePair_spec
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ) :
    let pair := allocatePair L hInfinite forbidden
    pair.1 ∈ L ∧ pair.2 ∈ L ∧
      pair.1 ∉ forbidden ∧ pair.2 ∉ forbidden ∧
      pair.1 ≠ pair.2 := by
  classical
  let first := leastFresh L hInfinite forbidden
  have hFirst := leastFresh_spec L hInfinite forbidden
  have hSecond :=
    leastFresh_spec L hInfinite (insert first forbidden)
  refine ⟨hFirst.1, hSecond.1, hFirst.2, ?_, ?_⟩
  · intro hForbidden
    exact hSecond.2 (Finset.mem_insert_of_mem hForbidden)
  · intro hEq
    apply hSecond.2
    rw [Finset.mem_insert]
    exact Or.inl hEq.symm

/-- The canonical pair is strictly increasing. -/
theorem allocatePair_strictMono
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ) :
    (allocatePair L hInfinite forbidden).1 <
      (allocatePair L hInfinite forbidden).2 := by
  classical
  let first := leastFresh L hInfinite forbidden
  let second := leastFresh L hInfinite (insert first forbidden)
  have hSecond := leastFresh_spec L hInfinite (insert first forbidden)
  have hLe : first ≤ second :=
    leastFresh_le L hInfinite forbidden hSecond.1
      (fun hForbidden =>
        hSecond.2 (Finset.mem_insert_of_mem hForbidden))
  have hNe : first ≠ second := by
    intro hEq
    apply hSecond.2
    rw [Finset.mem_insert]
    exact Or.inl hEq.symm
  exact lt_of_le_of_ne hLe hNe

/-- The first reservation is no larger than every fresh comparison string. -/
theorem allocatePair_first_le
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ)
    {comparison : ℕ}
    (hComparisonL : comparison ∈ L)
    (hComparisonFresh : comparison ∉ forbidden) :
    (allocatePair L hInfinite forbidden).1 ≤ comparison := by
  exact leastFresh_le L hInfinite forbidden
    hComparisonL hComparisonFresh

/-- Unless the comparison string is the first reservation itself, the second
reservation is no larger than it.  This is the exact second-least bound used
when comparing fallback choices against a fresh witness. -/
theorem allocatePair_second_le
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ)
    {comparison : ℕ}
    (hComparisonL : comparison ∈ L)
    (hComparisonFresh : comparison ∉ forbidden)
    (hComparisonNeFirst :
      comparison ≠ (allocatePair L hInfinite forbidden).1) :
    (allocatePair L hInfinite forbidden).2 ≤ comparison := by
  classical
  apply leastFresh_le L hInfinite
    (insert (allocatePair L hInfinite forbidden).1 forbidden)
    hComparisonL
  simp [hComparisonFresh, hComparisonNeFirst]

theorem allocatePair_second_le_of_first_lt
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ)
    {comparison : ℕ}
    (hComparisonL : comparison ∈ L)
    (hComparisonFresh : comparison ∉ forbidden)
    (hFirstLt :
      (allocatePair L hInfinite forbidden).1 < comparison) :
    (allocatePair L hInfinite forbidden).2 ≤ comparison :=
  allocatePair_second_le L hInfinite forbidden
    hComparisonL hComparisonFresh (Nat.ne_of_gt hFirstLt)

/-- A fresh comparison below the second canonical choice must be the first
choice. -/
theorem fresh_eq_first_of_lt_second
    (L : Language) (hInfinite : L.Infinite) (forbidden : Finset ℕ)
    {comparison : ℕ}
    (hComparisonL : comparison ∈ L)
    (hComparisonFresh : comparison ∉ forbidden)
    (hLtSecond :
      comparison < (allocatePair L hInfinite forbidden).2) :
    comparison = (allocatePair L hInfinite forbidden).1 := by
  by_contra hNe
  exact (Nat.not_lt_of_ge
    (allocatePair_second_le L hInfinite forbidden
      hComparisonL hComparisonFresh hNe)) hLtSecond

/-- The two stable tags allocated at one edge event. -/
def firstTag {Edge : Type*} (round : ℕ) (edge : Edge) :
    ReservationTag Edge :=
  ⟨round, edge, .first⟩

def secondTag {Edge : Type*} (round : ℕ) (edge : Edge) :
    ReservationTag Edge :=
  ⟨round, edge, .second⟩

/-- The two tagged entries produced by one fallback event. -/
noncomputable def allocatedEntries {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite) :
    List (Reservation Edge) :=
  let pair := allocatePair L hInfinite (forbiddenRange ledger used)
  [⟨firstTag round edge, pair.1⟩,
    ⟨secondTag round edge, pair.2⟩]

/-- Append a collision-free pair while retaining the complete old history. -/
noncomputable def appendPair {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite) :
    Ledger Edge :=
  ledger ++ allocatedEntries ledger used round edge L hInfinite

/-- The old ledger is literally a prefix of the updated ledger. -/
theorem appendPair_prefix {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite) :
    ledger <+: appendPair ledger used round edge L hInfinite := by
  exact List.prefix_append ledger _

/-- A pair allocated at `round` extends a history from earlier rounds to a
history strictly before `round + 1`. -/
theorem appendPair_roundsBefore_succ {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite)
    (hRounds : RoundsBefore ledger round) :
    RoundsBefore
      (appendPair ledger used round edge L hInfinite)
      (round + 1) := by
  intro reservation hReservation
  rw [appendPair, List.mem_append] at hReservation
  rcases hReservation with hOld | hNew
  · exact Nat.lt.step (hRounds reservation hOld)
  · simp only [allocatedEntries, List.mem_cons, List.mem_nil_iff,
      or_false] at hNew
    rcases hNew with rfl | rfl <;>
      exact Nat.lt_succ_self round

/-- Appending a current-round event preserves the weaker invariant that all
records, old and new, lie before the next round. -/
theorem appendPair_roundsBefore_succ_of_succ {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite)
    (hRounds : RoundsBefore ledger (round + 1)) :
    RoundsBefore
      (appendPair ledger used round edge L hInfinite)
      (round + 1) := by
  intro reservation hReservation
  rw [appendPair, List.mem_append] at hReservation
  rcases hReservation with hOld | hNew
  · exact hRounds reservation hOld
  · simp only [allocatedEntries, List.mem_cons, List.mem_nil_iff,
      or_false] at hNew
    rcases hNew with rfl | rfl <;>
      exact Nat.lt_succ_self round

/-- Tag-side injectivity for the pair introduced by one event. -/
theorem firstTag_ne_secondTag {Edge : Type*}
    (round : ℕ) (edge : Edge) :
    firstTag round edge ≠ secondTag round edge := by
  intro h
  have := congrArg ReservationTag.side h
  cases this

/-- Appending a fresh event preserves both ledger collision invariants. -/
theorem appendPair_valid {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite)
    (hValid : Valid ledger)
    (hFirstFresh : firstTag round edge ∉ tags ledger)
    (hSecondFresh : secondTag round edge ∉ tags ledger) :
    Valid (appendPair ledger used round edge L hInfinite) := by
  classical
  let pair :=
    allocatePair L hInfinite (forbiddenRange ledger used)
  have hpair :
      pair.1 ∈ L ∧ pair.2 ∈ L ∧
        pair.1 ∉ forbiddenRange ledger used ∧
        pair.2 ∉ forbiddenRange ledger used ∧
        pair.1 ≠ pair.2 := by
    simpa [pair] using
      allocatePair_spec L hInfinite (forbiddenRange ledger used)
  constructor
  · simp only [UniqueTags, appendPair, allocatedEntries, tags,
      List.map_append, List.map_cons, List.map_nil]
    change
      (tags ledger ++
        [firstTag round edge, secondTag round edge]).Nodup
    rw [List.nodup_append]
    refine ⟨hValid.1, ?_, ?_⟩
    · simp [firstTag_ne_secondTag]
    · intro old hold new hnew
      simp at hnew
      rcases hnew with rfl | rfl
      · intro hEq
        exact hFirstFresh (hEq ▸ hold)
      · intro hEq
        exact hSecondFresh (hEq ▸ hold)
  · simp only [UniqueStrings, appendPair, allocatedEntries, values,
      List.map_append, List.map_cons, List.map_nil]
    change (values ledger ++ [pair.1, pair.2]).Nodup
    rw [List.nodup_append]
    refine ⟨hValid.2, ?_, ?_⟩
    · simp [hpair.2.2.2.2]
    · intro old hold new hnew
      have holdRange : old ∈ stringRange ledger := by
        simpa [stringRange] using hold
      have holdForbidden : old ∈ forbiddenRange ledger used := by
        exact Finset.mem_union_right used holdRange
      simp at hnew
      rcases hnew with rfl | rfl
      · intro hEq
        exact hpair.2.2.1 (hEq ▸ holdForbidden)
      · intro hEq
        exact hpair.2.2.2.1 (hEq ▸ holdForbidden)

/-- Both new reservations are immediately available to the old queue view,
belong to the fallback language, and are distinct. -/
theorem appendPair_allocated_pair_spec {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite) :
    let pair :=
      allocatePair L hInfinite (forbiddenRange ledger used)
    pair.1 ∈ L ∧ pair.2 ∈ L ∧ pair.1 ≠ pair.2 ∧
      pair.1 ∈
        activeQueue
          (appendPair ledger used round edge L hInfinite) used ∧
      pair.2 ∈
        activeQueue
          (appendPair ledger used round edge L hInfinite) used := by
  classical
  let pair :=
    allocatePair L hInfinite (forbiddenRange ledger used)
  have hpair :
      pair.1 ∈ L ∧ pair.2 ∈ L ∧
        pair.1 ∉ forbiddenRange ledger used ∧
        pair.2 ∉ forbiddenRange ledger used ∧
        pair.1 ≠ pair.2 := by
    simpa [pair] using
      allocatePair_spec L hInfinite (forbiddenRange ledger used)
  have hfirstUsed : pair.1 ∉ used := by
    intro hUsed
    apply hpair.2.2.1
    exact Finset.mem_union_left _ hUsed
  have hsecondUsed : pair.2 ∉ used := by
    intro hUsed
    apply hpair.2.2.2.1
    exact Finset.mem_union_left _ hUsed
  refine ⟨hpair.1, hpair.2.1, hpair.2.2.2.2, ?_, ?_⟩
  · rw [mem_activeQueue]
    refine ⟨?_, hfirstUsed⟩
    refine
      ⟨({ tag := firstTag round edge, value := pair.1 } :
          Reservation Edge), ?_, rfl⟩
    apply List.mem_append.mpr
    right
    simp [allocatedEntries, pair]
  · rw [mem_activeQueue]
    refine ⟨?_, hsecondUsed⟩
    refine
      ⟨({ tag := secondTag round edge, value := pair.2 } :
          Reservation Edge), ?_, rfl⟩
    apply List.mem_append.mpr
    right
    simp [allocatedEntries, pair]

/-- Reserve a pair in a tagged output state.  Used strings and the previous
output are unchanged; only the append-only ledger grows. -/
noncomputable def TaggedOutputState.reservePair {Edge : Type*}
    (state : TaggedOutputState Edge)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite)
    (hFresh : EventFresh state.ledger round edge) :
    TaggedOutputState Edge where
  used := state.used
  ledger :=
    appendPair state.ledger state.used round edge L hInfinite
  previousOutput := state.previousOutput
  valid :=
    appendPair_valid state.ledger state.used round edge L hInfinite
      state.valid hFresh.1 hFresh.2

/-- Reserving is history-monotone even after packaging the invariants. -/
theorem TaggedOutputState.reservePair_prefix {Edge : Type*}
    (state : TaggedOutputState Edge)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite)
    (hFresh : EventFresh state.ledger round edge) :
    state.ledger <+:
      (state.reservePair round edge L hInfinite hFresh).ledger :=
  appendPair_prefix state.ledger state.used round edge L hInfinite

@[simp] theorem TaggedOutputState.reservePair_used {Edge : Type*}
    (state : TaggedOutputState Edge)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite)
    (hFresh : EventFresh state.ledger round edge) :
    (state.reservePair round edge L hInfinite hFresh).used =
      state.used :=
  rfl

@[simp] theorem TaggedOutputState.reservePair_previousOutput
    {Edge : Type*}
    (state : TaggedOutputState Edge)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite)
    (hFresh : EventFresh state.ledger round edge) :
    (state.reservePair round edge L hInfinite hFresh).previousOutput =
      state.previousOutput :=
  rfl

/-! ## Sequential batch reservation -/

/-- Appending an event cannot consume the tags of a different edge at the
same round.  This is the local fact that turns a duplicate-free edge list
into the sequential freshness needed by `appendBatch`. -/
theorem eventFresh_appendPair_of_ne {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (allocatedEdge otherEdge : Edge)
    (L : Language) (hInfinite : L.Infinite)
    (hOtherFresh : EventFresh ledger round otherEdge)
    (hNe : otherEdge ≠ allocatedEdge) :
    EventFresh
      (appendPair ledger used round allocatedEdge L hInfinite)
      round otherEdge := by
  classical
  constructor
  · intro hMem
    have hCases :
        firstTag round otherEdge ∈ tags ledger ∨
          firstTag round otherEdge =
            firstTag round allocatedEdge ∨
          firstTag round otherEdge =
            secondTag round allocatedEdge := by
      simpa [appendPair, allocatedEntries, tags] using hMem
    rcases hCases with hOld | hFirst | hSecond
    · exact hOtherFresh.1 hOld
    · apply hNe
      exact congrArg ReservationTag.edge hFirst
    · have hSide := congrArg ReservationTag.side hSecond
      cases hSide
  · intro hMem
    have hCases :
        secondTag round otherEdge ∈ tags ledger ∨
          secondTag round otherEdge =
            firstTag round allocatedEdge ∨
          secondTag round otherEdge =
            secondTag round allocatedEdge := by
      simpa [appendPair, allocatedEntries, tags] using hMem
    rcases hCases with hOld | hFirst | hSecond
    · exact hOtherFresh.2 hOld
    · have hSide := congrArg ReservationTag.side hFirst
      cases hSide
    · apply hNe
      exact congrArg ReservationTag.edge hSecond

/-- Sequentially append one canonical pair for every edge in a list.  The
language may depend on the edge.  Each allocation sees the ledger produced by
all earlier allocations, so its finite forbidden range includes every
historical reservation, including earlier entries in this same batch. -/
noncomputable def appendBatch {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite) :
    List Edge → Ledger Edge
  | [] => ledger
  | edge :: rest =>
      appendBatch
        (appendPair ledger used round edge
          (language edge) (hInfinite edge))
        used round language hInfinite rest

/-- The exact freshness obligation consumed by a sequential batch.  Unlike a
flat postcondition, this definition records that every event tag is fresh at
the moment its pair is allocated. -/
def SequentiallyFresh {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite) :
    List Edge → Prop
  | [] => True
  | edge :: rest =>
      EventFresh ledger round edge ∧
        SequentiallyFresh
          (appendPair ledger used round edge
            (language edge) (hInfinite edge))
          used round language hInfinite rest

/-- A duplicate-free batch whose events are all fresh in the input ledger is
sequentially fresh.  Earlier allocations only introduce the two tags of
their own distinct edge. -/
theorem sequentiallyFresh_of_nodup {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hNodup : edges.Nodup)
    (hInitiallyFresh :
      ∀ edge ∈ edges, EventFresh ledger round edge) :
    SequentiallyFresh ledger used round language hInfinite edges := by
  induction edges generalizing ledger with
  | nil =>
      simp [SequentiallyFresh]
  | cons head rest ih =>
      rw [List.nodup_cons] at hNodup
      constructor
      · exact hInitiallyFresh head (by simp)
      · apply ih
        · exact hNodup.2
        · intro edge hEdge
          apply eventFresh_appendPair_of_ne
            ledger used round head edge
            (language head) (hInfinite head)
          · exact hInitiallyFresh edge (by simp [hEdge])
          · intro hEq
            apply hNodup.1
            rw [← hEq]
            exact hEdge

/-- In the standard round-by-round use, a duplicate-free edge list is enough:
all input records come from earlier rounds, hence all current-round event tags
are initially fresh. -/
theorem sequentiallyFresh_of_roundsBefore {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hNodup : edges.Nodup)
    (hRounds : RoundsBefore ledger round) :
    SequentiallyFresh ledger used round language hInfinite edges :=
  sequentiallyFresh_of_nodup ledger used round language hInfinite
    edges hNodup
    (fun edge _ => eventFresh_of_roundsBefore edge hRounds)

/-- A sequential batch retains the entire input ledger as a literal prefix. -/
theorem appendBatch_prefix {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge) :
    ledger <+:
      appendBatch ledger used round language hInfinite edges := by
  induction edges generalizing ledger with
  | nil =>
      simp [appendBatch]
  | cons edge rest ih =>
      exact
        (appendPair_prefix ledger used round edge
          (language edge) (hInfinite edge)).trans
          (ih
            (appendPair ledger used round edge
              (language edge) (hInfinite edge)))

/-- A batch of events tagged at `round` preserves the invariant that every
record lies strictly before `round + 1`. -/
theorem appendBatch_roundsBefore_succ_of_succ {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hRounds : RoundsBefore ledger (round + 1)) :
    RoundsBefore
      (appendBatch ledger used round language hInfinite edges)
      (round + 1) := by
  induction edges generalizing ledger with
  | nil =>
      simpa [appendBatch]
  | cons edge rest ih =>
      apply ih
      exact
        appendPair_roundsBefore_succ_of_succ ledger used round edge
          (language edge) (hInfinite edge) hRounds

/-- In particular, a history from strictly earlier rounds becomes a history
strictly before the successor round after the batch. -/
theorem appendBatch_roundsBefore_succ {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hRounds : RoundsBefore ledger round) :
    RoundsBefore
      (appendBatch ledger used round language hInfinite edges)
      (round + 1) :=
  appendBatch_roundsBefore_succ_of_succ ledger used round language
    hInfinite edges
    (fun reservation hReservation =>
      Nat.lt.step (hRounds reservation hReservation))

/-- Sequential freshness and input validity suffice to preserve both global
collision invariants across an arbitrary finite batch. -/
theorem appendBatch_valid {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hValid : Valid ledger)
    (hFresh :
      SequentiallyFresh ledger used round language hInfinite edges) :
    Valid (appendBatch ledger used round language hInfinite edges) := by
  induction edges generalizing ledger with
  | nil =>
      simpa [appendBatch]
  | cons edge rest ih =>
      rcases hFresh with ⟨hHeadFresh, hRestFresh⟩
      apply ih
      · exact
          appendPair_valid ledger used round edge
            (language edge) (hInfinite edge) hValid
            hHeadFresh.1 hHeadFresh.2
      · exact hRestFresh

/-- Convenient validity theorem for the common round-indexed use of a
duplicate-free edge batch. -/
theorem appendBatch_valid_of_roundsBefore {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hValid : Valid ledger)
    (hNodup : edges.Nodup)
    (hRounds : RoundsBefore ledger round) :
    Valid (appendBatch ledger used round language hInfinite edges) :=
  appendBatch_valid ledger used round language hInfinite edges hValid
    (sequentiallyFresh_of_roundsBefore ledger used round language
      hInfinite edges hNodup hRounds)

/-- Reserving a sequential batch in a packaged state changes neither the
externally used range nor the previous output. -/
noncomputable def TaggedOutputState.reserveBatch {Edge : Type*}
    (state : TaggedOutputState Edge)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger state.used round
        language hInfinite edges) :
    TaggedOutputState Edge where
  used := state.used
  ledger :=
    appendBatch state.ledger state.used round language hInfinite edges
  previousOutput := state.previousOutput
  valid :=
    appendBatch_valid state.ledger state.used round language hInfinite
      edges state.valid hFresh

theorem TaggedOutputState.reserveBatch_prefix {Edge : Type*}
    (state : TaggedOutputState Edge)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger state.used round
        language hInfinite edges) :
    state.ledger <+:
      (state.reserveBatch round language hInfinite edges hFresh).ledger :=
  appendBatch_prefix state.ledger state.used round language hInfinite edges

@[simp] theorem TaggedOutputState.reserveBatch_used {Edge : Type*}
    (state : TaggedOutputState Edge)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger state.used round
        language hInfinite edges) :
    (state.reserveBatch round language hInfinite edges hFresh).used =
      state.used :=
  rfl

@[simp] theorem TaggedOutputState.reserveBatch_previousOutput
    {Edge : Type*}
    (state : TaggedOutputState Edge)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge)
    (hFresh :
      SequentiallyFresh state.ledger state.used round
        language hInfinite edges) :
    (state.reserveBatch round language hInfinite edges hFresh).previousOutput =
      state.previousOutput :=
  rfl

/-! ## Two-per-edge provenance -/

/-- The two side-tagged records for an edge occur in a ledger, with distinct
physical strings. -/
def HasPairProvenance {Edge : Type*}
    (ledger : Ledger Edge) (round : ℕ) (edge : Edge) : Prop :=
  ∃ first second,
    ({ tag := firstTag round edge, value := first } :
      Reservation Edge) ∈ ledger ∧
    ({ tag := secondTag round edge, value := second } :
      Reservation Edge) ∈ ledger ∧
    first ≠ second

/-- Provenance survives every history extension. -/
theorem HasPairProvenance.mono {Edge : Type*}
    {oldLedger newLedger : Ledger Edge}
    {round : ℕ} {edge : Edge}
    (hProvenance : HasPairProvenance oldLedger round edge)
    (hPrefix : oldLedger <+: newLedger) :
    HasPairProvenance newLedger round edge := by
  rcases hProvenance with
    ⟨first, second, hFirst, hSecond, hNe⟩
  exact ⟨first, second, hPrefix.subset hFirst,
    hPrefix.subset hSecond, hNe⟩

/-- One pair append creates the advertised two side-tagged records. -/
theorem appendPair_hasPairProvenance {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ) (edge : Edge)
    (L : Language) (hInfinite : L.Infinite) :
    HasPairProvenance
      (appendPair ledger used round edge L hInfinite)
      round edge := by
  classical
  let pair :=
    allocatePair L hInfinite (forbiddenRange ledger used)
  have hPair :=
    allocatePair_spec L hInfinite (forbiddenRange ledger used)
  refine ⟨pair.1, pair.2, ?_, ?_, ?_⟩
  · apply List.mem_append.mpr
    right
    simp [allocatedEntries, pair]
  · apply List.mem_append.mpr
    right
    simp [allocatedEntries, pair]
  · simpa [pair] using hPair.2.2.2.2

/-- Every listed edge receives a persistent two-record provenance witness in
the final batch ledger. -/
theorem appendBatch_hasPairProvenance {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge) {edge : Edge}
    (hEdge : edge ∈ edges) :
    HasPairProvenance
      (appendBatch ledger used round language hInfinite edges)
      round edge := by
  induction edges generalizing ledger with
  | nil =>
      simp at hEdge
  | cons head rest ih =>
      rw [List.mem_cons] at hEdge
      rcases hEdge with rfl | hRest
      · apply HasPairProvenance.mono
          (appendPair_hasPairProvenance ledger used round edge
            (language edge) (hInfinite edge))
        exact
          appendBatch_prefix
            (appendPair ledger used round edge
              (language edge) (hInfinite edge))
            used round language hInfinite rest
      · exact
          ih
            (appendPair ledger used round head
              (language head) (hInfinite head))
            hRest

/-- Every edge in an appended batch receives two records whose physical
strings avoid the `used` set supplied to the allocator. -/
theorem appendBatch_hasFreshPair
    {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge) {edge : Edge}
    (hEdge : edge ∈ edges) :
    ∃ first second,
      ({ tag := firstTag round edge, value := first } :
        Reservation Edge) ∈
          appendBatch ledger used round language hInfinite edges ∧
      ({ tag := secondTag round edge, value := second } :
        Reservation Edge) ∈
          appendBatch ledger used round language hInfinite edges ∧
      first ∉ used ∧ second ∉ used ∧ first ≠ second := by
  classical
  induction edges generalizing ledger with
  | nil =>
      simp at hEdge
  | cons head rest ih =>
      rw [List.mem_cons] at hEdge
      rcases hEdge with rfl | hRest
      · let pair :=
          allocatePair (language edge) (hInfinite edge)
            (forbiddenRange ledger used)
        have hPair :
            pair.1 ∈ language edge ∧
              pair.2 ∈ language edge ∧
              pair.1 ∉ forbiddenRange ledger used ∧
              pair.2 ∉ forbiddenRange ledger used ∧
              pair.1 ≠ pair.2 := by
          simpa [pair] using
            allocatePair_spec (language edge) (hInfinite edge)
              (forbiddenRange ledger used)
        have hFirstHead :
            ({ tag := firstTag round edge, value := pair.1 } :
              Reservation Edge) ∈
                appendPair ledger used round edge
                  (language edge) (hInfinite edge) := by
          apply List.mem_append.mpr
          right
          simp [allocatedEntries, pair]
        have hSecondHead :
            ({ tag := secondTag round edge, value := pair.2 } :
              Reservation Edge) ∈
                appendPair ledger used round edge
                  (language edge) (hInfinite edge) := by
          apply List.mem_append.mpr
          right
          simp [allocatedEntries, pair]
        have hPrefix :
            appendPair ledger used round edge
                (language edge) (hInfinite edge) <+:
              appendBatch
                (appendPair ledger used round edge
                  (language edge) (hInfinite edge))
                used round language hInfinite rest :=
          appendBatch_prefix
            (appendPair ledger used round edge
              (language edge) (hInfinite edge))
            used round language hInfinite rest
        refine
          ⟨pair.1, pair.2, hPrefix.subset hFirstHead,
            hPrefix.subset hSecondHead, ?_, ?_, hPair.2.2.2.2⟩
        · intro hUsed
          apply hPair.2.2.1
          exact Finset.mem_union_left _ hUsed
        · intro hUsed
          apply hPair.2.2.2.1
          exact Finset.mem_union_left _ hUsed
      · exact
          ih
            (appendPair ledger used round head
              (language head) (hInfinite head))
            hRest

/-- In a valid ledger, the two provenance witnesses are the unique records
with their respective side tags.  Since `ReservationSide` has exactly two
constructors, this is the exact two-per-edge statement needed by charging:
one uniquely sourced physical string on each side. -/
theorem HasPairProvenance.uniqueSides {Edge : Type*}
    {ledger : Ledger Edge} {round : ℕ} {edge : Edge}
    (hValid : Valid ledger)
    (hProvenance : HasPairProvenance ledger round edge) :
    ∃ first second,
      ({ tag := firstTag round edge, value := first } :
        Reservation Edge) ∈ ledger ∧
      ({ tag := secondTag round edge, value := second } :
        Reservation Edge) ∈ ledger ∧
      first ≠ second ∧
      (∀ reservation ∈ ledger,
        reservation.tag = firstTag round edge →
          reservation =
            ({ tag := firstTag round edge, value := first } :
              Reservation Edge)) ∧
      (∀ reservation ∈ ledger,
        reservation.tag = secondTag round edge →
          reservation =
            ({ tag := secondTag round edge, value := second } :
              Reservation Edge)) := by
  rcases hProvenance with
    ⟨first, second, hFirst, hSecond, hNe⟩
  refine ⟨first, second, hFirst, hSecond, hNe, ?_, ?_⟩
  · intro reservation hReservation hTag
    exact reservation_eq_of_tag_eq hValid
      hReservation hFirst hTag
  · intro reservation hReservation hTag
    exact reservation_eq_of_tag_eq hValid
      hReservation hSecond hTag

/-- Exact cardinal/provenance form: every ledger record carrying this
round-and-edge label is one of the two witnessed side records.  Together with
their distinct values, this rules out both missing and extra physical
reservations for the event. -/
theorem HasPairProvenance.exactTwo {Edge : Type*}
    {ledger : Ledger Edge} {round : ℕ} {edge : Edge}
    (hValid : Valid ledger)
    (hProvenance : HasPairProvenance ledger round edge) :
    ∃ first second,
      ({ tag := firstTag round edge, value := first } :
        Reservation Edge) ∈ ledger ∧
      ({ tag := secondTag round edge, value := second } :
        Reservation Edge) ∈ ledger ∧
      first ≠ second ∧
      ∀ reservation ∈ ledger,
        reservation.tag.round = round →
        reservation.tag.edge = edge →
        reservation =
            ({ tag := firstTag round edge, value := first } :
              Reservation Edge) ∨
          reservation =
            ({ tag := secondTag round edge, value := second } :
              Reservation Edge) := by
  rcases hProvenance.uniqueSides hValid with
    ⟨first, second, hFirst, hSecond, hNe,
      hUniqueFirst, hUniqueSecond⟩
  refine ⟨first, second, hFirst, hSecond, hNe, ?_⟩
  intro reservation hReservation hRound hEdge
  cases hSide : reservation.tag.side with
  | first =>
      left
      apply hUniqueFirst reservation hReservation
      exact reservationTag_eq hRound hEdge hSide
  | second =>
      right
      apply hUniqueSecond reservation hReservation
      exact reservationTag_eq hRound hEdge hSide

/-- A valid sequential batch gives every listed edge exactly two globally
collision-free, side-tagged physical reservations. -/
theorem appendBatch_exactTwo {Edge : Type*}
    (ledger : Ledger Edge) (used : Finset ℕ)
    (round : ℕ)
    (language : Edge → Language)
    (hInfinite : ∀ edge, (language edge).Infinite)
    (edges : List Edge) {edge : Edge}
    (hValid : Valid ledger)
    (hFresh :
      SequentiallyFresh ledger used round language hInfinite edges)
    (hEdge : edge ∈ edges) :
    ∃ first second,
      ({ tag := firstTag round edge, value := first } :
        Reservation Edge) ∈
          appendBatch ledger used round language hInfinite edges ∧
      ({ tag := secondTag round edge, value := second } :
        Reservation Edge) ∈
          appendBatch ledger used round language hInfinite edges ∧
      first ≠ second ∧
      ∀ reservation ∈
          appendBatch ledger used round language hInfinite edges,
        reservation.tag.round = round →
        reservation.tag.edge = edge →
        reservation =
            ({ tag := firstTag round edge, value := first } :
              Reservation Edge) ∨
          reservation =
            ({ tag := secondTag round edge, value := second } :
              Reservation Edge) := by
  apply HasPairProvenance.exactTwo
    (appendBatch_valid ledger used round language hInfinite edges
      hValid hFresh)
  exact
    appendBatch_hasPairProvenance ledger used round language hInfinite
      edges hEdge

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.ReservationLedger
