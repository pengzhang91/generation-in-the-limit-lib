import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.MembershipQueryAssignments
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.MembershipQueryDiagonalRepair

/-!
# A completion-driven repair of Theorem 7

Under the contradictory assumption that one machine satisfies the universal
two-language guarantee, its termination clause can be used at every finite
phase.  We complete the current finite assignment to two infinite languages,
run the machine on that legal completion, and retain only the finitely many
answers actually queried by the resulting execution.  This avoids the
incorrect claim in the printed proof that every infinite query loop must
mention infinitely many distinct words.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## Recording the answers used by one finite execution -/

noncomputable def executionQueryWords
    (rounds : List TwoLanguageRound) : Finset ℕ := by
  classical
  exact (rounds.flatMap fun round => round.2.1.map fun qa => qa.1.2).toFinset

theorem mem_executionQueryWords
    {rounds : List TwoLanguageRound} {x : ℕ} :
    x ∈ executionQueryWords rounds ↔
      ∃ round ∈ rounds, ∃ qa ∈ round.2.1, qa.1.2 = x := by
  classical
  simp [executionQueryWords]

noncomputable def languagePairBits
    (L₀ L₁ : Set ℕ) (x : ℕ) : Bool × Bool := by
  classical
  exact (decide (x ∈ L₀), decide (x ∈ L₁))

theorem languagePairBits_left
    (L₀ L₁ : Set ℕ) (x : ℕ) :
    (languagePairBits L₀ L₁ x).1 = true ↔ x ∈ L₀ := by
  classical
  simp [languagePairBits]

theorem languagePairBits_right
    (L₀ L₁ : Set ℕ) (x : ℕ) :
    (languagePairBits L₀ L₁ x).2 = true ↔ x ∈ L₁ := by
  classical
  simp [languagePairBits]

/-- Extend a finite assignment by recording both membership bits of every
word queried by a completed execution. -/
noncomputable def recordExecutionAnswers
    (assignment : PartialTwoLanguageAssignment)
    (L₀ L₁ : Set ℕ) (rounds : List TwoLanguageRound) :
    PartialTwoLanguageAssignment := by
  classical
  exact fun x =>
    match assignment x with
    | some bits => some bits
    | none =>
        if x ∈ executionQueryWords rounds
        then some (languagePairBits L₀ L₁ x)
        else none

theorem assignmentExtends_recordExecutionAnswers
    (assignment : PartialTwoLanguageAssignment)
    (L₀ L₁ : Set ℕ) (rounds : List TwoLanguageRound) :
    AssignmentExtends assignment
      (recordExecutionAnswers assignment L₀ L₁ rounds) := by
  intro x bits hbits
  classical
  simp [recordExecutionAnswers, hbits]

theorem recordExecutionAnswers_domain_subset
    (assignment : PartialTwoLanguageAssignment)
    (L₀ L₁ : Set ℕ) (rounds : List TwoLanguageRound) :
    partialAssignmentDomain
        (recordExecutionAnswers assignment L₀ L₁ rounds) ⊆
      partialAssignmentDomain assignment ∪
        (↑(executionQueryWords rounds) : Set ℕ) := by
  intro x hx
  rcases hx with ⟨bits, hbits⟩
  classical
  by_cases hold : ∃ old, assignment x = some old
  · exact Or.inl hold
  · have hnone : assignment x = none := by
      cases h : assignment x with
      | none => rfl
      | some old => exact (hold ⟨old, h⟩).elim
    have hquery : x ∈ executionQueryWords rounds := by
      by_contra hnot
      simp [recordExecutionAnswers, hnone, hnot] at hbits
    exact Or.inr hquery

theorem recordExecutionAnswers_domain_finite
    {assignment : PartialTwoLanguageAssignment}
    (hfinite : (partialAssignmentDomain assignment).Finite)
    (L₀ L₁ : Set ℕ) (rounds : List TwoLanguageRound) :
    (partialAssignmentDomain
      (recordExecutionAnswers assignment L₀ L₁ rounds)).Finite := by
  apply (hfinite.union (executionQueryWords rounds).finite_toSet).subset
  exact recordExecutionAnswers_domain_subset assignment L₀ L₁ rounds

theorem recordExecutionAnswers_decides
    (assignment : PartialTwoLanguageAssignment)
    (L₀ L₁ : Set ℕ) (rounds : List TwoLanguageRound) :
    PartialAssignmentDecidesExecution
      (recordExecutionAnswers assignment L₀ L₁ rounds) rounds := by
  intro round hround qa hqa
  classical
  let x := qa.1.2
  have hx : x ∈ executionQueryWords rounds :=
    mem_executionQueryWords.mpr ⟨round, hround, qa, hqa, rfl⟩
  cases h : assignment x with
  | none =>
      refine ⟨languagePairBits L₀ L₁ x, ?_⟩
      change recordExecutionAnswers assignment L₀ L₁ rounds x = _
      simp [recordExecutionAnswers, h, hx]
  | some bits =>
      refine ⟨bits, ?_⟩
      change recordExecutionAnswers assignment L₀ L₁ rounds x = _
      simp [recordExecutionAnswers, h]

theorem recordExecutionAnswers_realized
    {assignment : PartialTwoLanguageAssignment}
    {L₀ L₁ : Set ℕ} {rounds : List TwoLanguageRound}
    (hrealizes : LanguagePairRealizes assignment L₀ L₁) :
    LanguagePairRealizes
      (recordExecutionAnswers assignment L₀ L₁ rounds) L₀ L₁ := by
  intro x bits hbits
  classical
  cases h : assignment x with
  | some old =>
      have heq : bits = old := by
        have hsome : some old = some bits := by
          simpa [recordExecutionAnswers, h] using hbits
        exact (Option.some.inj hsome).symm
      subst bits
      exact hrealizes x old h
  | none =>
      by_cases hx : x ∈ executionQueryWords rounds
      · have heq : bits = languagePairBits L₀ L₁ x := by
          have hsome : some (languagePairBits L₀ L₁ x) = some bits := by
            simpa [recordExecutionAnswers, h, hx] using hbits
          exact (Option.some.inj hsome).symm
        subst bits
        exact ⟨languagePairBits_left L₀ L₁ x,
          languagePairBits_right L₀ L₁ x⟩
      · simp [recordExecutionAnswers, h, hx] at hbits

theorem recordExecutionAnswers_common_subset
    {assignment : PartialTwoLanguageAssignment}
    {L₀ L₁ : Set ℕ} {rounds : List TwoLanguageRound}
    (hrealizes : LanguagePairRealizes assignment L₀ L₁)
    (hintersection : L₀ ∩ L₁ ⊆ partialAssignmentCommon assignment) :
    partialAssignmentCommon
        (recordExecutionAnswers assignment L₀ L₁ rounds) ⊆
      partialAssignmentCommon assignment := by
  intro x hx
  have hrecorded :=
    recordExecutionAnswers_realized (rounds := rounds) hrealizes
      x (true, true) hx
  exact hintersection ⟨hrecorded.1.mp rfl, hrecorded.2.mp rfl⟩

/-! ## Recording an output without creating a new common word -/

def recordOutput
    (assignment : PartialTwoLanguageAssignment)
    (z : ℕ) : PartialTwoLanguageAssignment :=
  match assignment z with
  | some _ => assignment
  | none => assignIfUnset assignment z (sideBits false)

theorem recordOutput_extends
    (assignment : PartialTwoLanguageAssignment)
    (z : ℕ) :
    AssignmentExtends assignment (recordOutput assignment z) := by
  unfold recordOutput
  split
  · exact AssignmentExtends.refl assignment
  · exact assignmentExtends_assignIfUnset assignment z (sideBits false)

theorem recordOutput_domain_finite
    {assignment : PartialTwoLanguageAssignment}
    (hfinite : (partialAssignmentDomain assignment).Finite)
    (z : ℕ) :
    (partialAssignmentDomain (recordOutput assignment z)).Finite := by
  unfold recordOutput
  split
  · exact hfinite
  · apply (hfinite.union (Set.finite_singleton z)).subset
    intro x hx
    rcases hx with ⟨bits, hbits⟩
    by_cases hxz : x = z
    · exact Or.inr hxz
    · exact Or.inl ⟨bits, by simpa [assignIfUnset, hxz] using hbits⟩

theorem recordOutput_common_subset
    (assignment : PartialTwoLanguageAssignment) (z : ℕ) :
    partialAssignmentCommon (recordOutput assignment z) ⊆
      partialAssignmentCommon assignment := by
  intro x hx
  unfold recordOutput at hx
  split at hx
  · exact hx
  next hnone =>
    by_cases hxz : x = z
    · subst x
      simp [partialAssignmentCommon, assignIfUnset, hnone,
        sideBits_not_common] at hx
    · simpa [partialAssignmentCommon, assignIfUnset, hxz] using hx

theorem recordOutput_output_common
    {assignment : PartialTwoLanguageAssignment}
    {z : ℕ}
    (hz : z ∈ partialAssignmentCommon
      (recordOutput assignment z)) :
    z ∈ partialAssignmentCommon assignment :=
  recordOutput_common_subset assignment z hz

theorem recordOutput_assigns_output
    (assignment : PartialTwoLanguageAssignment) (z : ℕ) :
    ∃ bits, recordOutput assignment z z = some bits := by
  cases h : assignment z with
  | some bits => exact ⟨bits, by simp [recordOutput, h]⟩
  | none =>
      exact ⟨sideBits false, by simp [recordOutput, assignIfUnset, h]⟩

/-! ## One completion-driven phase -/

theorem assignCommon_extends
    (assignment : PartialTwoLanguageAssignment) (x : ℕ) :
    AssignmentExtends assignment (assignCommon assignment x) :=
  assignmentExtends_assignIfUnset assignment x (true, true)

theorem assignCommon_self
    {assignment : PartialTwoLanguageAssignment} {x : ℕ}
    (hfresh : assignment x = none) :
    assignCommon assignment x x = some (true, true) := by
  simp [assignCommon, assignIfUnset, hfresh]

theorem assignCommon_domain_finite
    {assignment : PartialTwoLanguageAssignment}
    (hfinite : (partialAssignmentDomain assignment).Finite)
    (x : ℕ) :
    (partialAssignmentDomain (assignCommon assignment x)).Finite := by
  apply (hfinite.union (Set.finite_singleton x)).subset
  intro y hy
  rcases hy with ⟨bits, hbits⟩
  by_cases hyx : y = x
  · exact Or.inr hyx
  · exact Or.inl ⟨bits, by
      simpa [assignCommon, assignIfUnset, hyx] using hbits⟩

theorem assignCommon_common_subset
    (assignment : PartialTwoLanguageAssignment) (x : ℕ) :
    partialAssignmentCommon (assignCommon assignment x) ⊆
      partialAssignmentCommon assignment ∪ {x} := by
  intro y hy
  by_cases hyx : y = x
  · exact Or.inr hyx
  · exact Or.inl (by
      simpa [partialAssignmentCommon, assignCommon, assignIfUnset, hyx]
        using hy)

/-- Finite invariant maintained between phases.  The common part of the
partial assignment consists only of already supplied positive inputs. -/
structure FiniteDiagonalStage where
  assignment : PartialTwoLanguageAssignment
  domainFinite : (partialAssignmentDomain assignment).Finite
  inputs : List ℕ
  inputsNodup : inputs.Nodup
  inputsCommon :
    ∀ x, x ∈ inputs → assignment x = some (true, true)
  commonOnlyInputs :
    partialAssignmentCommon assignment ⊆ (↑inputs.toFinset : Set ℕ)

/-- A permanently one-sided word witnessing that the limit pair contains two
distinct languages. -/
def diagonalDistinctnessMarker : ℕ := 0

def initialDiagonalAssignment : PartialTwoLanguageAssignment :=
  assignIfUnset (fun _ ↦ none) diagonalDistinctnessMarker (true, false)

def initialDiagonalStage : FiniteDiagonalStage where
  assignment := initialDiagonalAssignment
  domainFinite := by
    apply (Set.finite_singleton diagonalDistinctnessMarker).subset
    intro x hx
    rcases hx with ⟨bits, hbits⟩
    by_cases hmarker : x = diagonalDistinctnessMarker
    · exact hmarker
    · simp [initialDiagonalAssignment, assignIfUnset, hmarker] at hbits
  inputs := []
  inputsNodup := List.nodup_nil
  inputsCommon := by simp
  commonOnlyInputs := by
    intro x hx
    by_cases hmarker : x = diagonalDistinctnessMarker
    · subst x
      simp [partialAssignmentCommon, initialDiagonalAssignment,
        assignIfUnset] at hx
    · simp [partialAssignmentCommon, initialDiagonalAssignment,
        assignIfUnset] at hx

/-- All data retained from one phase.  `queryAssignment` records exactly the
answers used by `rounds`; `next` additionally records the output one-sidedly. -/
structure CompletionDrivenStep
    (A : TwoLanguageMembershipAlgorithm) (current : FiniteDiagonalStage) where
  newInput : ℕ
  newInputFresh : current.assignment newInput = none
  commonAssignment : PartialTwoLanguageAssignment
  commonAssignment_eq :
    commonAssignment = assignCommon current.assignment newInput
  temporaryLeft : Set ℕ
  temporaryRight : Set ℕ
  temporaryLeftInfinite : temporaryLeft.Infinite
  temporaryRightInfinite : temporaryRight.Infinite
  temporaryRealizesCommon :
    LanguagePairRealizes commonAssignment temporaryLeft temporaryRight
  temporaryIntersection :
    temporaryLeft ∩ temporaryRight ⊆
      partialAssignmentCommon commonAssignment
  rounds : List TwoLanguageRound
  output : ℕ
  execution :
    ExecutionValid A temporaryLeft temporaryRight
      (current.inputs ++ [newInput]) rounds
  outputAtLast :
    ∃ hlast : current.inputs.length < rounds.length,
      (rounds.get ⟨current.inputs.length, hlast⟩).2.2 = output
  queryAssignment : PartialTwoLanguageAssignment
  queryAssignment_eq :
    queryAssignment = recordExecutionAnswers commonAssignment
      temporaryLeft temporaryRight rounds
  queryAssignmentFinite :
    (partialAssignmentDomain queryAssignment).Finite
  queryAssignmentDecides :
    PartialAssignmentDecidesExecution queryAssignment rounds
  temporaryRealizesQuery :
    LanguagePairRealizes queryAssignment temporaryLeft temporaryRight
  queryCommonOnlyOld :
    partialAssignmentCommon queryAssignment ⊆
      partialAssignmentCommon commonAssignment
  next : FiniteDiagonalStage
  nextInputs : next.inputs = current.inputs ++ [newInput]
  nextAssignment :
    next.assignment = recordOutput queryAssignment output
  assignmentExtends :
    AssignmentExtends current.assignment next.assignment

theorem exists_fresh_for_stage (stage : FiniteDiagonalStage) :
    ∃ x, stage.assignment x = none := by
  obtain ⟨x, _hxUniv, hx⟩ :=
    Set.infinite_univ.exists_notMem_finset
      stage.domainFinite.toFinset
  refine ⟨x, ?_⟩
  cases h : stage.assignment x with
  | none => rfl
  | some bits =>
      exact (hx (stage.domainFinite.mem_toFinset.mpr ⟨bits, h⟩)).elim

theorem list_ofFn_get_eq_self {xs : List α} :
    List.ofFn (fun i : Fin xs.length ↦ xs.get i) = xs := by
  exact List.ofFn_get xs

theorem exists_completionDrivenStep
    {A : TwoLanguageMembershipAlgorithm}
    (hUniversal :
      ∀ L₀ L₁ : Set ℕ, L₀ ≠ L₁ → L₀.Infinite → L₁.Infinite →
        NonuniformTwoLanguageMembershipGuarantee A L₀ L₁)
    (current : FiniteDiagonalStage) :
    Nonempty (CompletionDrivenStep A current) := by
  classical
  obtain ⟨x, hxfresh⟩ := exists_fresh_for_stage current
  let common := assignCommon current.assignment x
  have hcommonFinite :
      (partialAssignmentDomain common).Finite := by
    exact assignCommon_domain_finite current.domainFinite x
  obtain ⟨L₀, L₁, hL₀NeL₁, hL₀Infinite, hL₁Infinite, hrealizes,
      hintersection⟩ :=
    finitePartialAssignment_has_separated_infinite_completion hcommonFinite
  let inputs := current.inputs ++ [x]
  have hinputsLength : inputs.length = current.inputs.length + 1 := by
    simp [inputs]
  let inputFn : Fin inputs.length → ℕ := fun i ↦ inputs.get i
  have hinputCommon : ∀ i, common (inputFn i) = some (true, true) := by
    intro i
    have hmem : inputFn i ∈ inputs := List.get_mem inputs i
    rw [show inputs = current.inputs ++ [x] from rfl] at hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hold | hnew
    · exact assignCommon_extends current.assignment x _ _
        (current.inputsCommon _ hold)
    · rw [hnew]
      exact assignCommon_self hxfresh
  have hinputLeft : ∀ i, inputFn i ∈ L₀ := by
    intro i
    exact (hrealizes _ _ (hinputCommon i)).1.mp rfl
  have hinputRight : ∀ i, inputFn i ∈ L₁ := by
    intro i
    exact (hrealizes _ _ (hinputCommon i)).2.mp rfl
  let stream := finitePrefixThenEnumeration inputFn L₀ hL₀Infinite
  have hpresents : Presents stream L₀ :=
    finitePrefixThenEnumeration_presents hL₀Infinite hinputLeft
  obtain ⟨z, rounds, hvalid, hlast, hz⟩ :=
    ((hUniversal L₀ L₁ hL₀NeL₁ hL₀Infinite hL₁Infinite).choose_spec.choose_spec
      false stream (by simpa [selectedTwoLanguage] using hpresents)
      current.inputs.length).1
  have hprefixInputs : membershipInputPrefix stream inputs.length = inputs := by
    unfold membershipInputPrefix
    have hprefix :
        (fun i : Fin inputs.length ↦ stream i) = inputFn := by
      funext i
      exact finitePrefixThenEnumeration_prefix inputFn L₀ hL₀Infinite i i.isLt
    rw [hprefix]
    exact list_ofFn_get_eq_self
  have hvalidInputs : ExecutionValid A L₀ L₁ inputs rounds := by
    rw [← hprefixInputs]
    simpa [hinputsLength] using hvalid
  let query := recordExecutionAnswers common L₀ L₁ rounds
  have hqueryFinite : (partialAssignmentDomain query).Finite :=
    recordExecutionAnswers_domain_finite hcommonFinite L₀ L₁ rounds
  have hqueryDecides : PartialAssignmentDecidesExecution query rounds :=
    recordExecutionAnswers_decides common L₀ L₁ rounds
  have hrealizesQuery : LanguagePairRealizes query L₀ L₁ :=
    recordExecutionAnswers_realized hrealizes
  have hqueryCommon : partialAssignmentCommon query ⊆
      partialAssignmentCommon common :=
    recordExecutionAnswers_common_subset hrealizes hintersection
  let finalAssignment := recordOutput query z
  have hfinalFinite :
      (partialAssignmentDomain finalAssignment).Finite :=
    recordOutput_domain_finite hqueryFinite z
  have hcurrentFinal : AssignmentExtends current.assignment finalAssignment :=
    (assignCommon_extends current.assignment x).trans
      ((assignmentExtends_recordExecutionAnswers common L₀ L₁ rounds).trans
        (recordOutput_extends query z))
  have hxnotInputs : x ∉ current.inputs := by
    intro hx
    have := current.inputsCommon x hx
    rw [hxfresh] at this
    cases this
  let next : FiniteDiagonalStage :=
    { assignment := finalAssignment
      domainFinite := hfinalFinite
      inputs := inputs
      inputsNodup := current.inputsNodup.append
        (by simp) (by
          intro y hyOld hyNew
          simp only [List.mem_singleton] at hyNew
          subst y
          exact hxnotInputs hyOld)
      inputsCommon := by
        intro y hy
        have hy' : y ∈ current.inputs ∨ y = x := by
          simpa [inputs] using hy
        rcases hy' with hyOld | rfl
        · exact hcurrentFinal y (true, true)
            (current.inputsCommon y hyOld)
        · exact
            ((assignmentExtends_recordExecutionAnswers common L₀ L₁ rounds).trans
              (recordOutput_extends query z)) y (true, true)
              (assignCommon_self hxfresh)
      commonOnlyInputs := by
        intro y hy
        have hyQuery : y ∈ partialAssignmentCommon query :=
          recordOutput_common_subset query z hy
        have hyCommon : y ∈ partialAssignmentCommon common :=
          hqueryCommon hyQuery
        have hyCases := assignCommon_common_subset current.assignment x hyCommon
        rcases hyCases with hyOld | hyx
        · have : y ∈ current.inputs.toFinset :=
            current.commonOnlyInputs hyOld
          have hyList : y ∈ current.inputs := by
            simpa only [List.mem_toFinset] using this
          change y ∈ inputs.toFinset
          rw [List.mem_toFinset]
          change y ∈ current.inputs ++ [x]
          exact List.mem_append_left [x] hyList
        · subst y
          simp [inputs] }
  exact ⟨
    { newInput := x
      newInputFresh := hxfresh
      commonAssignment := common
      commonAssignment_eq := rfl
      temporaryLeft := L₀
      temporaryRight := L₁
      temporaryLeftInfinite := hL₀Infinite
      temporaryRightInfinite := hL₁Infinite
      temporaryRealizesCommon := hrealizes
      temporaryIntersection := hintersection
      rounds := rounds
      output := z
      execution := hvalidInputs
      outputAtLast := ⟨by simpa [hinputsLength] using hlast, hz⟩
      queryAssignment := query
      queryAssignment_eq := rfl
      queryAssignmentFinite := hqueryFinite
      queryAssignmentDecides := hqueryDecides
      temporaryRealizesQuery := hrealizesQuery
      queryCommonOnlyOld := hqueryCommon
      next := next
      nextInputs := rfl
      nextAssignment := rfl
      assignmentExtends := hcurrentFinal }⟩

/-! ## The recursively assembled finite stages -/

section GlobalConstruction

variable {A : TwoLanguageMembershipAlgorithm}

variable (hUniversal :
  ∀ L₀ L₁ : Set ℕ, L₀ ≠ L₁ → L₀.Infinite → L₁.Infinite →
    NonuniformTwoLanguageMembershipGuarantee A L₀ L₁)

noncomputable def completionDrivenChoice
    (current : FiniteDiagonalStage) : CompletionDrivenStep A current :=
  Classical.choice (exists_completionDrivenStep hUniversal current)

noncomputable def globalDiagonalStage : ℕ → FiniteDiagonalStage
  | 0 => initialDiagonalStage
  | n + 1 =>
      (completionDrivenChoice hUniversal (globalDiagonalStage n)).next

noncomputable def globalDiagonalStep (n : ℕ) :
    CompletionDrivenStep A (globalDiagonalStage hUniversal n) :=
  completionDrivenChoice hUniversal (globalDiagonalStage hUniversal n)

noncomputable def globalCommonInput (n : ℕ) : ℕ :=
  (globalDiagonalStep hUniversal n).newInput

noncomputable def globalPhaseOutput (n : ℕ) : ℕ :=
  (globalDiagonalStep hUniversal n).output

@[simp] theorem globalDiagonalStage_zero :
    globalDiagonalStage hUniversal 0 = initialDiagonalStage := rfl

@[simp] theorem globalDiagonalStage_succ (n : ℕ) :
    globalDiagonalStage hUniversal (n + 1) =
      (globalDiagonalStep hUniversal n).next := rfl

theorem globalDiagonalStage_succ_inputs (n : ℕ) :
    (globalDiagonalStage hUniversal (n + 1)).inputs =
      (globalDiagonalStage hUniversal n).inputs ++
        [globalCommonInput hUniversal n] := by
  exact (globalDiagonalStep hUniversal n).nextInputs

theorem globalDiagonalStage_succ_extends (n : ℕ) :
    AssignmentExtends
      (globalDiagonalStage hUniversal n).assignment
      (globalDiagonalStage hUniversal (n + 1)).assignment := by
  exact (globalDiagonalStep hUniversal n).assignmentExtends

theorem globalDiagonalStage_assignment_mono
    {m n : ℕ} (hmn : m ≤ n) :
    AssignmentExtends
      (globalDiagonalStage hUniversal m).assignment
      (globalDiagonalStage hUniversal n).assignment := by
  induction n, hmn using Nat.le_induction with
  | base => exact AssignmentExtends.refl _
  | succ n hmn ih =>
      exact ih.trans (globalDiagonalStage_succ_extends hUniversal n)

theorem globalDiagonalStage_inputs_eq (n : ℕ) :
    (globalDiagonalStage hUniversal n).inputs =
      List.ofFn (fun i : Fin n ↦ globalCommonInput hUniversal i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [globalDiagonalStage_succ_inputs, ih]
      symm
      rw [List.ofFn_succ']
      have hprefix :
          List.ofFn
              (fun i : Fin n ↦ globalCommonInput hUniversal i.castSucc) =
            List.ofFn
              (fun i : Fin n ↦ globalCommonInput hUniversal i) := by
        apply List.ofFn_inj.mpr
        funext i
        rfl
      rw [hprefix]
      simp only [List.concat_eq_append]
      congr 2

theorem globalCommonInput_injective :
    Function.Injective (globalCommonInput hUniversal) := by
  intro m n hmn
  let k := max m n + 1
  have hmLt : m < k := by
    dsimp [k]
    omega
  have hnLt : n < k := by
    dsimp [k]
    omega
  have hnodup :
      (List.ofFn fun i : Fin k ↦ globalCommonInput hUniversal i).Nodup := by
    rw [← globalDiagonalStage_inputs_eq hUniversal k]
    exact (globalDiagonalStage hUniversal k).inputsNodup
  have hfin : (⟨m, hmLt⟩ : Fin k) = ⟨n, hnLt⟩ :=
    (List.nodup_ofFn.mp hnodup) hmn
  exact Fin.val_eq_of_eq hfin

/-! ## The limit pair determined by the monotone assignments -/

noncomputable def globalLeftLanguage : Set ℕ :=
  {x | ∃ n bits,
    (globalDiagonalStage hUniversal n).assignment x = some bits ∧
      bits.1 = true}

noncomputable def globalRightLanguage : Set ℕ :=
  {x | ∃ n bits,
    (globalDiagonalStage hUniversal n).assignment x = some bits ∧
      bits.2 = true}

theorem globalStage_realized (n : ℕ) :
    LanguagePairRealizes
      (globalDiagonalStage hUniversal n).assignment
      (globalLeftLanguage hUniversal)
      (globalRightLanguage hUniversal) := by
  intro x bits hbits
  constructor
  · constructor
    · intro hleft
      exact ⟨n, bits, hbits, hleft⟩
    · rintro ⟨m, other, hother, hotherLeft⟩
      let k := max n m
      have hbitsK :
          (globalDiagonalStage hUniversal k).assignment x = some bits :=
        globalDiagonalStage_assignment_mono hUniversal
          (Nat.le_max_left n m) x bits hbits
      have hotherK :
          (globalDiagonalStage hUniversal k).assignment x = some other :=
        globalDiagonalStage_assignment_mono hUniversal
          (Nat.le_max_right n m) x other hother
      have heq : bits = other :=
        Option.some.inj (hbitsK.symm.trans hotherK)
      simpa [heq] using hotherLeft
  · constructor
    · intro hright
      exact ⟨n, bits, hbits, hright⟩
    · rintro ⟨m, other, hother, hotherRight⟩
      let k := max n m
      have hbitsK :
          (globalDiagonalStage hUniversal k).assignment x = some bits :=
        globalDiagonalStage_assignment_mono hUniversal
          (Nat.le_max_left n m) x bits hbits
      have hotherK :
          (globalDiagonalStage hUniversal k).assignment x = some other :=
        globalDiagonalStage_assignment_mono hUniversal
          (Nat.le_max_right n m) x other hother
      have heq : bits = other :=
        Option.some.inj (hbitsK.symm.trans hotherK)
      simpa [heq] using hotherRight

theorem globalCommonInput_mem (n : ℕ) :
    globalCommonInput hUniversal n ∈
      globalLeftLanguage hUniversal ∩ globalRightLanguage hUniversal := by
  have hmem : globalCommonInput hUniversal n ∈
      (globalDiagonalStage hUniversal (n + 1)).inputs := by
    rw [globalDiagonalStage_succ_inputs]
    simp
  have hbits :=
    (globalDiagonalStage hUniversal (n + 1)).inputsCommon _ hmem
  constructor
  · exact ⟨n + 1, (true, true), hbits, rfl⟩
  · exact ⟨n + 1, (true, true), hbits, rfl⟩

theorem globalLeftLanguage_infinite :
    (globalLeftLanguage hUniversal).Infinite := by
  apply Set.infinite_range_of_injective
      (globalCommonInput_injective hUniversal) |>.mono
  rintro x ⟨n, rfl⟩
  exact (globalCommonInput_mem hUniversal n).1

theorem globalRightLanguage_infinite :
    (globalRightLanguage hUniversal).Infinite := by
  apply Set.infinite_range_of_injective
      (globalCommonInput_injective hUniversal) |>.mono
  rintro x ⟨n, rfl⟩
  exact (globalCommonInput_mem hUniversal n).2

theorem initialDiagonalAssignment_marker :
    initialDiagonalAssignment diagonalDistinctnessMarker =
      some (true, false) := by
  simp [initialDiagonalAssignment, assignIfUnset]

theorem globalMarker_assignment :
    ∀ n,
      (globalDiagonalStage hUniversal n).assignment
          diagonalDistinctnessMarker = some (true, false) := by
  intro n
  exact globalDiagonalStage_assignment_mono hUniversal (Nat.zero_le n)
    diagonalDistinctnessMarker (true, false)
    initialDiagonalAssignment_marker

theorem globalLanguages_ne :
    globalLeftLanguage hUniversal ≠ globalRightLanguage hUniversal := by
  intro heq
  have hleft : diagonalDistinctnessMarker ∈
      globalLeftLanguage hUniversal :=
    ⟨0, (true, false), globalMarker_assignment hUniversal 0, rfl⟩
  have hright : diagonalDistinctnessMarker ∈
      globalRightLanguage hUniversal := by
    simpa [heq] using hleft
  rcases hright with ⟨n, bits, hbits, hbitsRight⟩
  have hmarker := globalMarker_assignment hUniversal n
  have heqBits : bits = (true, false) :=
    Option.some.inj (hbits.symm.trans hmarker)
  simp [heqBits] at hbitsRight

/-! ## Transfer of the phase executions to the limit pair -/

theorem globalPhase_execution (n : ℕ) :
    CommonPrefixExecutionOutputsAt A
      (globalLeftLanguage hUniversal)
      (globalRightLanguage hUniversal)
      (globalCommonInput hUniversal) n
      (globalPhaseOutput hUniversal n) := by
  let step := globalDiagonalStep hUniversal n
  have hqueryNext : AssignmentExtends
      step.queryAssignment step.next.assignment := by
    rw [step.nextAssignment]
    exact recordOutput_extends step.queryAssignment step.output
  have hrealizesFinal : LanguagePairRealizes step.queryAssignment
      (globalLeftLanguage hUniversal)
      (globalRightLanguage hUniversal) := by
    intro x bits hbits
    have hbitsNext := hqueryNext x bits hbits
    exact globalStage_realized hUniversal (n + 1) x bits (by
      simpa [step] using hbitsNext)
  refine ⟨step.rounds, ?_, ?_⟩
  have htransferred := executionValid_of_partialAssignment
    step.execution step.temporaryRealizesQuery hrealizesFinal
      step.queryAssignmentDecides
  have hinputs :
      (globalDiagonalStage hUniversal n).inputs ++ [step.newInput] =
        List.ofFn (fun i : Fin (n + 1) ↦ globalCommonInput hUniversal i) := by
    rw [← globalDiagonalStage_inputs_eq hUniversal (n + 1)]
    exact (globalDiagonalStage_succ_inputs hUniversal n).symm
  rw [← hinputs]
  exact htransferred
  rcases step.outputAtLast with ⟨hlast, hout⟩
  have hlength :
      (globalDiagonalStage hUniversal n).inputs.length = n := by
    rw [globalDiagonalStage_inputs_eq]
    simp
  have hn : n < step.rounds.length := by
    simpa only [hlength] using hlast
  have hindex :
      (⟨(globalDiagonalStage hUniversal n).inputs.length, hlast⟩ :
        Fin step.rounds.length) = ⟨n, hn⟩ := by
    apply Fin.ext
    exact hlength
  refine ⟨hn, ?_⟩
  rw [← hindex]
  simpa [globalPhaseOutput, step] using hout

theorem globalPhaseOutput_assigned (n : ℕ) :
    ∃ bits,
      (globalDiagonalStage hUniversal (n + 1)).assignment
        (globalPhaseOutput hUniversal n) = some bits := by
  let step := globalDiagonalStep hUniversal n
  have hassigned :=
    recordOutput_assigns_output step.queryAssignment step.output
  simpa [globalDiagonalStage_succ, step.nextAssignment,
    globalPhaseOutput, step] using hassigned

theorem globalPhaseOutput_not_freshCommon (n : ℕ) :
    globalPhaseOutput hUniversal n ∉
      (globalLeftLanguage hUniversal ∩ globalRightLanguage hUniversal) \
        (↑(sequenceSample
          (fun i : Fin (n + 1) ↦ globalCommonInput hUniversal i)) : Set ℕ) := by
  rintro ⟨⟨hleft, hright⟩, hnotSample⟩
  obtain ⟨bits, hbits⟩ := globalPhaseOutput_assigned hUniversal n
  have hrealized := globalStage_realized hUniversal (n + 1) _ bits hbits
  have hfirst : bits.1 = true := hrealized.1.mpr hleft
  have hsecond : bits.2 = true := hrealized.2.mpr hright
  have hbitsCommon : bits = (true, true) := by
    apply Prod.ext
    · simpa using hfirst
    · simpa using hsecond
  have hcommon : globalPhaseOutput hUniversal n ∈
      partialAssignmentCommon
        (globalDiagonalStage hUniversal (n + 1)).assignment := by
    simpa [partialAssignmentCommon, hbitsCommon] using hbits
  have hinput : globalPhaseOutput hUniversal n ∈
      (globalDiagonalStage hUniversal (n + 1)).inputs.toFinset :=
    (globalDiagonalStage hUniversal (n + 1)).commonOnlyInputs hcommon
  apply hnotSample
  rw [globalDiagonalStage_inputs_eq] at hinput
  have hlist : globalPhaseOutput hUniversal n ∈
      List.ofFn
        (fun i : Fin (n + 1) ↦ globalCommonInput hUniversal i) := by
    simpa only [List.mem_toFinset] using hinput
  exact mem_sequenceSample_iff.mpr (List.mem_ofFn.mp hlist)

/-- The completion-driven construction supplies the full diagonal
certificate directly from the contradictory universal guarantee. -/
noncomputable def globalMembershipDiagonalCertificate :
    MembershipDiagonalCertificate A where
  leftLanguage := globalLeftLanguage hUniversal
  rightLanguage := globalRightLanguage hUniversal
  languagesDistinct := globalLanguages_ne hUniversal
  leftInfinite := globalLeftLanguage_infinite hUniversal
  rightInfinite := globalRightLanguage_infinite hUniversal
  commonInput := globalCommonInput hUniversal
  commonInput_injective := globalCommonInput_injective hUniversal
  commonInput_mem := globalCommonInput_mem hUniversal
  phaseOutput := globalPhaseOutput hUniversal
  execution := globalPhase_execution hUniversal
  phaseOutput_not_freshCommon :=
    globalPhaseOutput_not_freshCommon hUniversal

/-- Charikar--Pabbaraju Theorem 7.  The proof is stronger than necessary in
one respect: computability of the alleged universal machine is not used.
Universality itself supplies termination on every finite completion selected
by the diagonal. -/
theorem theorem_seven : TheoremSevenStatement := by
  rintro ⟨A, _hcomputable, hUniversal⟩
  exact (globalMembershipDiagonalCertificate hUniversal).not_nonuniformGuarantee
    (hUniversal
      (globalLeftLanguage hUniversal)
      (globalRightLanguage hUniversal)
      (globalLanguages_ne hUniversal)
      (globalLeftLanguage_infinite hUniversal)
      (globalRightLanguage_infinite hUniversal))

end GlobalConstruction

end GenLimit.CharikarPabbaraju
