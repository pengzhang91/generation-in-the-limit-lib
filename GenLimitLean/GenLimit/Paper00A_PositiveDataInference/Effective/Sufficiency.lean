import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper00A_PositiveDataInference.Effective.Definitions
import GenLimit.Support.ComputableSearch

/-!
# Effective sufficiency of Angluin's Condition 1

This file first connects Condition 1's stage-by-stage enumeration to the
finite approximation used by the semantic correctness proof. It then
implements the corresponding bounded least-index list learner and proves the
learner computable.
-/

namespace GenLimit.Angluin

/-- Compatibility name for shared finite-stage enumeration content. -/
abbrev stageContents := GenLimit.Support.stageContents

theorem mem_stageContents_iff
    {emit : ℕ → ℕ → Option ℕ} {i n x : ℕ} :
    x ∈ stageContents emit i n ↔
      ∃ stage < n, emit i stage = some x := by
  exact GenLimit.Support.mem_stageContents_iff

theorem stageContents_mono
    {emit : ℕ → ℕ → Option ℕ} {i n m : ℕ} (hnm : n ≤ m) :
    stageContents emit i n ⊆ stageContents emit i m := by
  exact GenLimit.Support.stageContents_mono hnm

/-- Finitely many emitted values all occur before one common stage. -/
theorem finite_emissions_bounded
    {emit : ℕ → ℕ → Option ℕ} {i : ℕ} (T : Finset ℕ)
    (hT : ∀ x, x ∈ T → ∃ stage, emit i stage = some x) :
    ∃ N, ∀ x, x ∈ T → ∃ stage < N, emit i stage = some x := by
  exact GenLimit.Support.finite_emissions_bounded T hT

/-- A finite set-valued tell-tale enumeration yields the monotone, eventually
stable stage approximation used in Angluin's learner proof. -/
theorem tellTaleApproximation_of_enumeration
    {C : GenLimit.Generic.LanguageFamily ℕ}
    {emit : ℕ → ℕ → Option ℕ}
    (hTell : ∀ i,
      IsEnumeratedTellTale C i (enumeratedSet emit i)) :
    IsTellTaleApproximation C (stageContents emit) := by
  classical
  constructor
  · intro i n m hnm
    exact stageContents_mono hnm
  · intro i
    let hfinite : (enumeratedSet emit i).Finite := (hTell i).1
    let T : Finset ℕ := hfinite.toFinset
    have hTmem {x : ℕ} : x ∈ T ↔ x ∈ enumeratedSet emit i := by
      exact hfinite.mem_toFinset
    have hTtell : IsTellTale C i T := by
      constructor
      · intro x hx
        exact (hTell i).2.1 (hTmem.mp hx)
      · intro j hTj hji
        apply (hTell i).2.2 j
        · intro x hx
          exact hTj (hTmem.mpr hx)
        · exact hji
    have hEvery : ∀ x, x ∈ T → ∃ stage, emit i stage = some x := by
      intro x hx
      exact hTmem.mp hx
    obtain ⟨N, hN⟩ := finite_emissions_bounded T hEvery
    refine ⟨T, hTtell, N, ?_⟩
    intro n hn
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨stage, -, hout⟩ := mem_stageContents_iff.mp hx
      exact hTmem.mpr ⟨stage, hout⟩
    · intro x hx
      obtain ⟨stage, hstage, hout⟩ := hN x hx
      exact mem_stageContents_iff.mpr
        ⟨stage, lt_of_lt_of_le hstage hn, hout⟩

/-- Exact Condition 1 supplies the approximation needed by the semantic
stabilization proof.  The computability witness remains present in the
hypothesis even though this erasure lemma only uses its extensional output. -/
theorem ConditionOne.exists_tellTaleApproximation
    {F : EffectiveIndexedFamily} (h : ConditionOne F) :
    ∃ A : ℕ → ℕ → Finset ℕ,
      IsTellTaleApproximation F.language A := by
  obtain ⟨emit, -, hTell⟩ := h
  exact ⟨stageContents emit,
    tellTaleApproximation_of_enumeration hTell⟩

/-- Forgetting uniform computability from Condition 1 leaves Condition 2. -/
theorem ConditionOne.conditionTwo
    {F : EffectiveIndexedFamily} (h : ConditionOne F) :
    ConditionTwo F.language :=
  h.exists_tellTaleApproximation.choose_spec.conditionTwo

/-- Effective-hypothesis/semantic-conclusion erasure of the sufficiency half
of Angluin's Theorem 1. -/
theorem ConditionOne.semantic_sufficiency
    {F : EffectiveIndexedFamily} (h : ConditionOne F) :
    ∃ M : SemanticIdentifier ℕ,
      SemanticallyIdentifies M F.language := by
  obtain ⟨A, hA⟩ := h.exists_tellTaleApproximation
  exact ⟨semanticLearner F.language A,
    semanticLearner_semanticallyIdentifies hA⟩

/-- Source-facing name for the semantic erasure of Condition 1. -/
theorem ConditionOne.toSemanticallyInferrable
    {F : EffectiveIndexedFamily} (h : ConditionOne F) :
    SemanticallyInferrable F.language :=
  h.semantic_sufficiency

end GenLimit.Angluin

/-!
## Computable bounded learner

This file implements the bounded least-index learner on lists.  Its Boolean
stage tests are computable from the effective family and tell-tale enumerator;
their extensional meaning is exactly the stage predicate used by the semantic
stabilization proof.
-/

namespace GenLimit.Angluin

/-! ## Computable bounded search utilities -/

/-- Compatibility name for the shared bounded universal search. -/
abbrev boundedAll {α : Type*} := GenLimit.Support.boundedAll (alpha := α)

theorem boundedAll_computable {α : Type*} [Primcodable α]
    {p : α → ℕ → Bool} (hp : Computable₂ p) :
    Computable₂ (boundedAll p) := by
  exact GenLimit.Support.boundedAll_computable hp

theorem boundedAll_eq_true_iff {α : Type*}
    (p : α → ℕ → Bool) (a : α) (n : ℕ) :
    boundedAll p a n = true ↔ ∀ k < n, p a k = true := by
  exact GenLimit.Support.boundedAll_eq_true_iff p a n

/-- Compatibility name for shared executable list membership. -/
abbrev listContains := GenLimit.Support.listContains

theorem listContains_computable : Computable₂ listContains := by
  exact GenLimit.Support.listContains_computable

@[simp] theorem listContains_eq_true_iff (xs : List ℕ) (x : ℕ) :
    listContains xs x = true ↔ x ∈ xs := by
  exact GenLimit.Support.listContains_eq_true_iff xs x

/-- Compatibility name for the shared bounded least-witness search. -/
abbrev firstTrue {α : Type*} := GenLimit.Support.firstTrue (alpha := α)

@[simp] theorem firstTrue_zero {α : Type*}
    (p : α → ℕ → Bool) (a : α) :
    firstTrue p a 0 = none :=
  GenLimit.Support.firstTrue_zero p a

theorem firstTrue_succ {α : Type*}
    (p : α → ℕ → Bool) (a : α) (n : ℕ) :
    firstTrue p a (n + 1) =
      match firstTrue p a n with
      | some i => some i
      | none => if p a n then some n else none := by
  exact GenLimit.Support.firstTrue_succ p a n

set_option maxHeartbeats 800000 in
theorem firstTrue_computable {α : Type*} [Primcodable α]
    {p : α → ℕ → Bool} (hp : Computable₂ p) :
    Computable₂ (firstTrue p) := by
  exact GenLimit.Support.firstTrue_computable hp

theorem firstTrue_eq_none_iff {α : Type*}
    (p : α → ℕ → Bool) (a : α) (n : ℕ) :
    firstTrue p a n = none ↔ ∀ i < n, p a i = false := by
  exact GenLimit.Support.firstTrue_eq_none_iff p a n

theorem firstTrue_spec {α : Type*}
    {p : α → ℕ → Bool} {a : α} {n i : ℕ}
    (h : firstTrue p a n = some i) :
    i < n ∧ p a i = true ∧ ∀ j < i, p a j = false := by
  exact GenLimit.Support.firstTrue_spec h

theorem firstTrue_le_of_true {α : Type*}
    {p : α → ℕ → Bool} {a : α} {n i j : ℕ}
    (hfirst : firstTrue p a n = some j)
    (_hi : i < n) (hpi : p a i = true) : j ≤ i := by
  exact GenLimit.Support.firstTrue_le_of_true hfirst _hi hpi

/-! ## Executable stage tests -/

/-- Check that every observed datum belongs to candidate language `i`. -/
def observedCheck (F : EffectiveIndexedFamily)
    (xs : List ℕ) (i : ℕ) : Bool :=
  boundedAll
    (fun p : ℕ × List ℕ => fun k =>
      F.membership p.1 (p.2.getD k 0))
    (i, xs) xs.length

theorem observedCheck_computable (F : EffectiveIndexedFamily) :
    Computable₂ (observedCheck F) := by
  have hget : Computable₂ (fun p : ℕ × List ℕ => fun k : ℕ =>
      p.2.getD k 0) :=
    ((Primrec.list_getD 0).comp₂
      (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right).to_comp
  have hindex : Computable₂ (fun p : ℕ × List ℕ => fun _k : ℕ => p.1) :=
    (Primrec.fst.comp₂ Primrec₂.left).to_comp
  have hmembership : Computable₂ (fun p : ℕ × List ℕ => fun k : ℕ =>
      F.membership p.1 (p.2.getD k 0)) :=
    F.membership_computable.comp₂ hindex hget
  exact (boundedAll_computable hmembership).comp₂
    (Primrec₂.pair.comp₂ Primrec₂.right Primrec₂.left).to_comp
    (Primrec.list_length.comp₂ Primrec₂.left).to_comp

/-- Check one stage of the tell-tale enumeration against the observed list. -/
def emissionAccepted (emit : ℕ → ℕ → Option ℕ)
    (p : ℕ × List ℕ) (stage : ℕ) : Bool :=
  match emit p.1 stage with
  | none => true
  | some x => listContains p.2 x

theorem emissionAccepted_computable
    {emit : ℕ → ℕ → Option ℕ} (hemit : Computable₂ emit) :
    Computable₂ (emissionAccepted emit) := by
  let Input := ((ℕ × List ℕ) × ℕ)
  have hout : Computable (fun z : Input => emit z.1.1 z.2) :=
    hemit.comp
      (Computable.fst.comp Computable.fst) Computable.snd
  have hsome : Computable₂ (fun (z : Input) (x : ℕ) =>
      listContains z.1.2 x) :=
    listContains_computable.comp₂
      (Primrec.snd.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)).to_comp
      Primrec₂.right.to_comp
  exact (Computable.to₂
    (Computable.option_casesOn hout (Computable.const true) hsome)).of_eq
      fun z => by
        rcases z with ⟨p, stage⟩
        dsimp only [emissionAccepted]
        cases emit p.1 stage <;> rfl

/-- Check that all tell-tale elements emitted before the current stage have
already appeared in the data. -/
def emissionCheck (emit : ℕ → ℕ → Option ℕ)
    (xs : List ℕ) (i : ℕ) : Bool :=
  boundedAll (emissionAccepted emit) (i, xs) xs.length

theorem emissionCheck_computable
    {emit : ℕ → ℕ → Option ℕ} (hemit : Computable₂ emit) :
    Computable₂ (emissionCheck emit) :=
  (boundedAll_computable (emissionAccepted_computable hemit)).comp₂
    (Primrec₂.pair.comp₂ Primrec₂.right Primrec₂.left).to_comp
    (Primrec.list_length.comp₂ Primrec₂.left).to_comp

/-- The executable part of Angluin's stage predicate.  The bound `i ≤ t` is
enforced by the learner's finite search range. -/
def effectiveStageEligible (F : EffectiveIndexedFamily)
    (emit : ℕ → ℕ → Option ℕ) (xs : List ℕ) (i : ℕ) : Bool :=
  observedCheck F xs i && emissionCheck emit xs i

theorem effectiveStageEligible_computable
    (F : EffectiveIndexedFamily)
    {emit : ℕ → ℕ → Option ℕ} (hemit : Computable₂ emit) :
    Computable₂ (effectiveStageEligible F emit) :=
  Primrec.and.to_comp.comp₂
    (observedCheck_computable F)
    (emissionCheck_computable hemit)

private theorem getD_ofFn {t : ℕ} (xs : Fin t → ℕ) (k : Fin t) :
    (List.ofFn xs).getD k 0 = xs k := by
  rw [List.getD_eq_getElem?_getD]
  simp [k.isLt]

theorem observedCheck_eq_true_iff
    (F : EffectiveIndexedFamily) {t i : ℕ} (xs : Fin t → ℕ) :
    observedCheck F (List.ofFn xs) i = true ↔
      (↑(GenLimit.Generic.sequenceSample xs) : Set ℕ) ⊆ F.language i := by
  rw [observedCheck, boundedAll_eq_true_iff]
  simp only [List.length_ofFn]
  constructor
  · intro h x hx
    have hxFin : x ∈ GenLimit.Generic.sequenceSample xs := hx
    obtain ⟨k, rfl⟩ :=
      GenLimit.Generic.mem_sequenceSample_iff.mp hxFin
    have hk := h k k.isLt
    rw [F.membership_spec] at hk
    simpa only [getD_ofFn] using hk
  · intro h k hk
    rw [F.membership_spec]
    rw [show (List.ofFn xs).getD k 0 = xs ⟨k, hk⟩ by
      simpa using getD_ofFn xs ⟨k, hk⟩]
    exact h (GenLimit.Generic.mem_sequenceSample_iff.mpr ⟨⟨k, hk⟩, rfl⟩)

theorem emissionCheck_eq_true_iff
    (emit : ℕ → ℕ → Option ℕ) {t i : ℕ} (xs : Fin t → ℕ) :
    emissionCheck emit (List.ofFn xs) i = true ↔
      stageContents emit i t ⊆ GenLimit.Generic.sequenceSample xs := by
  rw [emissionCheck, boundedAll_eq_true_iff]
  simp only [List.length_ofFn]
  constructor
  · intro h x hx
    obtain ⟨stage, hstage, hout⟩ := mem_stageContents_iff.mp hx
    have haccepted := h stage hstage
    simp only [emissionAccepted, hout, listContains_eq_true_iff] at haccepted
    rw [List.mem_ofFn] at haccepted
    exact GenLimit.Generic.mem_sequenceSample_iff.mpr haccepted
  · intro h stage hstage
    cases hout : emit i stage with
    | none => simp [emissionAccepted, hout]
    | some x =>
        have hxStage : x ∈ stageContents emit i t :=
          mem_stageContents_iff.mpr ⟨stage, hstage, hout⟩
        have hxSample := h hxStage
        rw [GenLimit.Generic.mem_sequenceSample_iff] at hxSample
        rw [emissionAccepted, hout, listContains_eq_true_iff,
          List.mem_ofFn]
        exact hxSample

theorem effectiveStageEligible_eq_true_iff
    (F : EffectiveIndexedFamily) (emit : ℕ → ℕ → Option ℕ)
    {t i : ℕ} (xs : Fin t → ℕ) :
    effectiveStageEligible F emit (List.ofFn xs) i = true ↔
      stageContents emit i t ⊆ GenLimit.Generic.sequenceSample xs ∧
        (↑(GenLimit.Generic.sequenceSample xs) : Set ℕ) ⊆ F.language i := by
  rw [effectiveStageEligible, Bool.and_eq_true,
    observedCheck_eq_true_iff, emissionCheck_eq_true_iff]
  exact and_comm

theorem effectiveStageEligible_iff_stageEligible
    (F : EffectiveIndexedFamily) (emit : ℕ → ℕ → Option ℕ)
    {t i : ℕ} (xs : Fin t → ℕ) (hi : i ≤ t) :
    effectiveStageEligible F emit (List.ofFn xs) i = true ↔
      StageEligible F.language (stageContents emit) (List.ofFn xs) i := by
  rw [effectiveStageEligible_eq_true_iff, StageEligible, List.length_ofFn]
  have hsample : historySample (List.ofFn xs) =
      GenLimit.Generic.sequenceSample xs := by
    classical
    ext x
    simp [historySample, GenLimit.Generic.mem_sequenceSample_iff]
  rw [hsample]
  constructor
  · intro h
    exact ⟨hi, h⟩
  · intro h
    exact h.2

/-! ## The computable least-index learner -/

/-- Search candidates `0, ..., xs.length` and return the least one passing
the executable stage test, defaulting to `0` when none passes. -/
def effectiveLearner (F : EffectiveIndexedFamily)
    (emit : ℕ → ℕ → Option ℕ) : EffectiveIdentifier :=
  fun xs =>
    (firstTrue (effectiveStageEligible F emit)
      xs (xs.length + 1)).getD 0

theorem effectiveLearner_computable
    (F : EffectiveIndexedFamily)
    {emit : ℕ → ℕ → Option ℕ} (hemit : Computable₂ emit) :
    Computable (effectiveLearner F emit) := by
  have heligible := effectiveStageEligible_computable F hemit
  have hsearch : Computable (fun xs : List ℕ =>
      firstTrue (effectiveStageEligible F emit)
        xs (xs.length + 1)) :=
    (firstTrue_computable heligible).comp Computable.id
      (Primrec.succ.to_comp.comp Computable.list_length)
  exact (Computable.option_getD hsearch (Computable.const 0)).of_eq
    fun xs => by rfl

/-- The executable learner agrees pointwise with the semantic least-index
learner used in the convergence proof. -/
theorem effectiveLearner_eq_semanticLearner
    (F : EffectiveIndexedFamily) (emit : ℕ → ℕ → Option ℕ)
    (t : ℕ) (xs : Fin t → ℕ) :
    effectiveLearner F emit (List.ofFn xs) =
      semanticLearner F.language (stageContents emit) (List.ofFn xs) := by
  classical
  let p := effectiveStageEligible F emit
  let search := firstTrue p (List.ofFn xs) (t + 1)
  by_cases hex : ∃ i,
      StageEligible F.language (stageContents emit) (List.ofFn xs) i
  · have hsearchNotNone : search ≠ none := by
      intro hnone
      obtain ⟨i, hi⟩ := hex
      have hiT : i ≤ t := by simpa using hi.1
      have hilimit : i < t + 1 := Nat.lt_succ_iff.mpr hiT
      have hptrue : p (List.ofFn xs) i = true :=
        (effectiveStageEligible_iff_stageEligible F emit xs hiT).mpr hi
      have hpfalse :=
        (firstTrue_eq_none_iff p (List.ofFn xs) (t + 1)).mp
          hnone i hilimit
      simp [hptrue] at hpfalse
    obtain ⟨j, hjSearch⟩ := Option.ne_none_iff_exists'.mp hsearchNotNone
    have hjSpec := firstTrue_spec hjSearch
    have hjle : j ≤ t := Nat.lt_succ_iff.mp hjSpec.1
    have hjEligible : StageEligible F.language (stageContents emit)
        (List.ofFn xs) j :=
      (effectiveStageEligible_iff_stageEligible F emit xs hjle).mp
        hjSpec.2.1
    let semantic :=
      semanticLearner F.language (stageContents emit) (List.ofFn xs)
    have hsemanticEligible :
        StageEligible F.language (stageContents emit) (List.ofFn xs) semantic :=
      semanticLearner_eligible hex
    have hsemanticLeT : semantic ≤ t := by
      simpa using hsemanticEligible.1
    have hsemanticLeJ : semantic ≤ j :=
      semanticLearner_le_of_eligible hjEligible
    have hjLeSemantic : j ≤ semantic :=
      firstTrue_le_of_true hjSearch
        (Nat.lt_succ_iff.mpr hsemanticLeT)
        ((effectiveStageEligible_iff_stageEligible F emit xs
          hsemanticLeT).mpr hsemanticEligible)
    have hjEq : j = semantic := Nat.le_antisymm hjLeSemantic hsemanticLeJ
    simp only [effectiveLearner, List.length_ofFn]
    change search.getD 0 = semantic
    rw [hjSearch]
    simpa using hjEq
  · have hallFalse : ∀ i < t + 1, p (List.ofFn xs) i = false := by
      intro i hi
      have hile : i ≤ t := Nat.lt_succ_iff.mp hi
      by_cases hp : p (List.ofFn xs) i = true
      · exact False.elim (hex ⟨i,
          (effectiveStageEligible_iff_stageEligible F emit xs hile).mp hp⟩)
      · exact Bool.eq_false_of_not_eq_true hp
    have hsearchNone : search = none :=
      (firstTrue_eq_none_iff p (List.ofFn xs) (t + 1)).mpr hallFalse
    simp only [effectiveLearner, List.length_ofFn]
    change search.getD 0 =
      semanticLearner F.language (stageContents emit) (List.ofFn xs)
    rw [hsearchNone]
    simp [semanticLearner, hex]

/-- Sufficiency half of Angluin's effective Theorem 1. -/
theorem ConditionOne.effective_sufficiency
    {F : EffectiveIndexedFamily} (h : ConditionOne F) :
    EffectiveInferrable F := by
  obtain ⟨emit, hemit, hTell⟩ := h
  have hA : IsTellTaleApproximation F.language (stageContents emit) :=
    tellTaleApproximation_of_enumeration hTell
  refine ⟨effectiveLearner F emit,
    effectiveLearner_computable F hemit, ?_⟩
  have hsemantic :
      SemanticallyIdentifies
        (semanticLearner F.language (stageContents emit)) F.language :=
    semanticLearner_semanticallyIdentifies hA
  have hlearnerEq :
      effectiveLearner F emit =
        semanticLearner F.language (stageContents emit) := by
    funext xs
    simpa using
      effectiveLearner_eq_semanticLearner F emit xs.length xs.get
  rw [hlearnerEq]
  exact hsemantic

end GenLimit.Angluin
