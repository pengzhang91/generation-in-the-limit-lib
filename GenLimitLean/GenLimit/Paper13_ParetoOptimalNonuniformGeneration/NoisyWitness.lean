import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.WitnessLowerBound
import GenLimit.Paper06_NoisyExamples.Definitions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-!
# Deterministic witness core for noisy Pareto generation

This module formalizes the probability-free combinatorial core of
Charikar--Pabbaraju, *Pareto-optimal Non-uniform Language Generation*,
arXiv:2510.02795v1, Theorem 6 and Appendix B.

The paper traverses pairs `(noise level, language)` diagonally.  We flatten
that traversal to natural-number coordinates.  Thus `F q` is the underlying
language at coordinate `q`, while `noise q` is its allowed noise level.

Four source arguments are checked here.

* Claim B.1: for a fixed finite prefix, every feasible noisy witness set has
  an explicit finite cardinality bound.  Consequently, whenever Step A has
  any candidate at all, a largest-cardinality candidate exists.
* Claim B.2: the finite witness produced by Procedure 2 gives the exact
  earlier-coordinate Pareto tradeoff against every deterministic generator.
* Claim B.3: the old argmax witness survives one insertion by the source's
  old-candidate/new-candidate split, and the invariant iterates through any
  finite sequence of comparator-approved crossings.
* Theorem 6's target-insertion step: once Claim B.3 supplies the argmax
  invariant, a sufficiently large noisy sample cannot make the target fail
  the infinite-intersection check.

This deliberately does not claim the still-missing concrete diagonal
execution of Procedure 2: the finite Claim B.3 induction consumes the exact
per-insertion argmax and comparison facts that the while loop must supply.
No probability, runtime, or membership-oracle semantics is used.
-/

namespace GenLimit.ParetoGeneration

/-- The points of a finite sample that lie outside one diagonal coordinate's
underlying language. -/
noncomputable abbrev noisyExceptions
    (F : ℕ → Set α) (coordinate : ℕ) (sample : Finset α) :
    Finset α :=
  GenLimit.NoisyExamples.negativePart sample (F coordinate)

/-- The source's "`a`-contained" relation, with the noise budget attached to
the flattened diagonal coordinate. -/
def NoiseContainedAt
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (coordinate : ℕ) (sample : Finset α) : Prop :=
  (noisyExceptions F coordinate sample).card ≤ noise coordinate

/-- A Step-A pair consisting of a subcollection and a finite noisy witness
set.  The subcollection lies in the current scope, contains the coordinate
being inserted, has finite common intersection, and accepts the sample up to
its coordinate-wise noise budgets. -/
def NoisyWitnessCandidate
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ)
    (sample : Finset α) (witness : Finset ℕ) : Prop :=
  witness ⊆ scopeSet ∧
    target ∈ witness ∧
    (indexedIntersection F witness).Finite ∧
    ∀ coordinate ∈ witness,
      NoiseContainedAt F noise coordinate sample

/-- A finite witness set is covered by the finite common core together with
the union of its exceptions for the witness coordinates. -/
theorem noisyWitnessCandidate_card_le_core_add
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {scopeSet : Finset ℕ} {target : ℕ}
    {sample : Finset α} {witness : Finset ℕ}
    {maxNoise : ℕ}
    (hCandidate :
      NoisyWitnessCandidate F noise scopeSet target sample witness)
    (hNoise :
      ∀ coordinate ∈ scopeSet, noise coordinate ≤ maxNoise) :
    sample.card ≤
      finiteIntersectionScore F witness +
        witness.card * maxNoise := by
  classical
  let core : Finset α :=
    hCandidate.2.2.1.toFinset
  let bad : Finset α :=
    witness.biUnion fun coordinate =>
      noisyExceptions F coordinate sample
  have hcover : sample ⊆ core ∪ bad := by
    intro x hxSample
    by_cases hxCore : x ∈ indexedIntersection F witness
    · exact Finset.mem_union_left bad
        (by simpa [core] using hxCore)
    · apply Finset.mem_union_right core
      change ¬∀ coordinate, coordinate ∈ witness →
        x ∈ F coordinate at hxCore
      push_neg at hxCore
      obtain ⟨coordinate, hcoordinate, hxOutside⟩ := hxCore
      apply Finset.mem_biUnion.mpr
      refine ⟨coordinate, hcoordinate, ?_⟩
      exact Finset.mem_filter.mpr ⟨hxSample, hxOutside⟩
  have hbad : bad.card ≤ witness.card * maxNoise := by
    apply Finset.card_biUnion_le_card_mul
    intro coordinate hcoordinate
    exact
      (hCandidate.2.2.2 coordinate hcoordinate).trans
        (hNoise coordinate (hCandidate.1 hcoordinate))
  have hcore :
      core.card = finiteIntersectionScore F witness := by
    change hCandidate.2.2.1.toFinset.card =
      (indexedIntersection F witness).ncard
    exact
      (Set.ncard_eq_toFinset_card
        (indexedIntersection F witness)
        hCandidate.2.2.1).symm
  calc
    sample.card ≤ (core ∪ bad).card :=
      Finset.card_le_card hcover
    _ ≤ core.card + bad.card :=
      Finset.card_union_le core bad
    _ ≤ finiteIntersectionScore F witness +
        witness.card * maxNoise := by
      rw [hcore]
      exact Nat.add_le_add_left hbad _

/-- Claim B.1's displayed uniform bound for every Step-A candidate in one
finite scope.  `procedureStepComplexity` is the largest finite common-core
size in that scope, and `scopeSet.card * maxNoise` pays for all exceptions. -/
theorem claim_B_1_noisyWitness_card_bound
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {scopeSet : Finset ℕ} {target : ℕ}
    {sample : Finset α} {witness : Finset ℕ}
    {maxNoise : ℕ}
    (hCandidate :
      NoisyWitnessCandidate F noise scopeSet target sample witness)
    (hNoise :
      ∀ coordinate ∈ scopeSet, noise coordinate ≤ maxNoise) :
    sample.card ≤
      procedureStepComplexity F scopeSet target +
        scopeSet.card * maxNoise := by
  have hFiniteCandidate :
      FiniteIntersectionCandidate F scopeSet target witness :=
    ⟨hCandidate.1, hCandidate.2.1, hCandidate.2.2.1⟩
  have hExists :
      ∃ other,
        FiniteIntersectionCandidate F scopeSet target other :=
    ⟨witness, hFiniteCandidate⟩
  have hCoreMax :
      finiteIntersectionScore F witness ≤
        procedureStepComplexity F scopeSet target := by
    rw [procedureStepComplexity_eq_score F scopeSet target hExists]
    exact
      (procedureStepWitness_spec
        F scopeSet target hExists).2 witness hFiniteCandidate
  have hWitnessCard : witness.card ≤ scopeSet.card :=
    Finset.card_le_card hCandidate.1
  exact
    (noisyWitnessCandidate_card_le_core_add
      hCandidate hNoise).trans
      (Nat.add_le_add hCoreMax
        (Nat.mul_le_mul_right maxNoise hWitnessCard))

/-- A finite sample is feasible for Step A if some subcollection witnesses
it. -/
def NoisyProcedureSampleCandidate
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ)
    (sample : Finset α) : Prop :=
  ∃ witness,
    NoisyWitnessCandidate
      F noise scopeSet target sample witness

/-- Full existence part of Claim B.1: bounded natural-valued scores attain a
maximum even though the universe of possible finite witness sets need not be
finite. -/
theorem claim_B_1_exists_maximal_noisyWitness
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target maxNoise : ℕ)
    (hNoise :
      ∀ coordinate ∈ scopeSet, noise coordinate ≤ maxNoise)
    (hExists :
      ∃ sample,
        NoisyProcedureSampleCandidate
          F noise scopeSet target sample) :
    ∃ sample,
      NoisyProcedureSampleCandidate
          F noise scopeSet target sample ∧
      ∀ other,
        NoisyProcedureSampleCandidate
            F noise scopeSet target other →
        other.card ≤ sample.card := by
  classical
  let bound :=
    procedureStepComplexity F scopeSet target +
      scopeSet.card * maxNoise
  let scores : Finset ℕ :=
    (Finset.range (bound + 1)).filter fun score =>
      ∃ sample,
        NoisyProcedureSampleCandidate
            F noise scopeSet target sample ∧
          sample.card = score
  have hscores : scores.Nonempty := by
    obtain ⟨sample, hsample⟩ := hExists
    refine ⟨sample.card, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      obtain ⟨witness, hwitness⟩ := hsample
      exact claim_B_1_noisyWitness_card_bound hwitness hNoise
    · exact ⟨sample, hsample, rfl⟩
  obtain ⟨score, hscore, hmax⟩ :=
    Finset.exists_max_image scores id hscores
  obtain ⟨sample, hsample, hsampleCard⟩ :=
    (Finset.mem_filter.mp hscore).2
  refine ⟨sample, hsample, ?_⟩
  intro other hother
  have hotherBound : other.card ≤ bound := by
    obtain ⟨witness, hwitness⟩ := hother
    exact claim_B_1_noisyWitness_card_bound hwitness hNoise
  have hotherScore : other.card ∈ scores := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hotherBound),
        ⟨other, hother, rfl⟩⟩
  have := hmax other.card hotherScore
  simpa [hsampleCard] using this

/-- Procedure 2 has no candidate at its first diagonal coordinate when, as
assumed by the paper, the underlying language is infinite.

Unlike Procedure 1, Procedure 2 does not print an empty-witness/zero-score
fallback.  Hence its first instruction to choose a largest `T` is literally
undefined.  This theorem isolates that source-level initialization defect;
the later Claim B.3 lemmas below apply when an actual Step-A maximum exists
or to the corrected max-value invariant. -/
theorem procedure_2_first_step_has_no_candidate
    (F : ℕ → Set α) (noise : ℕ → ℕ) (target : ℕ)
    (hInfinite : (F target).Infinite) :
    ¬∃ sample,
      NoisyProcedureSampleCandidate
        F noise {target} target sample := by
  rintro ⟨sample, witness, hCandidate⟩
  have hFiniteCandidate :
      FiniteIntersectionCandidate F {target} target witness :=
    ⟨hCandidate.1, hCandidate.2.1, hCandidate.2.2.1⟩
  obtain ⟨other, hOther, hOtherNe⟩ :=
    finiteIntersectionCandidate_contains_other
      F {target} target hInfinite hFiniteCandidate
  have hOtherEq : other = target := by
    simpa using hCandidate.1 hOther
  exact hOtherNe hOtherEq

/-! ## The target-insertion core of Theorem 6 -/

/-- The cardinality half of Claim B.3's argmax invariant. -/
def NoisyArgmaxBound
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target bound : ℕ) : Prop :=
  ∀ sample witness,
    NoisyWitnessCandidate
        F noise scopeSet target sample witness →
      sample.card ≤ bound

/-- Enlarging the finite scope preserves feasibility of a fixed noisy
witness. -/
theorem NoisyWitnessCandidate.mono_scope
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {smallScope largeScope : Finset ℕ}
    {target : ℕ} {sample : Finset α} {witness : Finset ℕ}
    (hCandidate :
      NoisyWitnessCandidate
        F noise smallScope target sample witness)
    (hScope : smallScope ⊆ largeScope) :
    NoisyWitnessCandidate
      F noise largeScope target sample witness :=
  ⟨hCandidate.1.trans hScope, hCandidate.2⟩

/-- A candidate whose witness contains a second coordinate is also a
candidate when retargeted to that coordinate.  This is the key observation
in the new-language branch of Claim B.3. -/
theorem NoisyWitnessCandidate.retarget
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {scopeSet : Finset ℕ} {target newTarget : ℕ}
    {sample : Finset α} {witness : Finset ℕ}
    (hCandidate :
      NoisyWitnessCandidate
        F noise scopeSet target sample witness)
    (hNewTarget : newTarget ∈ witness) :
    NoisyWitnessCandidate
      F noise scopeSet newTarget sample witness :=
  ⟨hCandidate.1, hNewTarget, hCandidate.2.2⟩

/-- If a candidate in an enlarged scope does not use the newly inserted
coordinate, it was already a candidate in the old scope. -/
theorem NoisyWitnessCandidate.of_insert_scope_not_mem
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {scopeSet : Finset ℕ} {target newCoordinate : ℕ}
    {sample : Finset α} {witness : Finset ℕ}
    (hCandidate :
      NoisyWitnessCandidate F noise
        (insert newCoordinate scopeSet) target sample witness)
    (hNotUsed : newCoordinate ∉ witness) :
    NoisyWitnessCandidate
      F noise scopeSet target sample witness := by
  refine ⟨?_, hCandidate.2⟩
  intro coordinate hcoordinate
  rcases Finset.mem_insert.mp
      (hCandidate.1 hcoordinate) with hEq | hOld
  · subst coordinate
    exact (hNotUsed hcoordinate).elim
  · exact hOld

/-- A stored Step-A witness together with the literal argmax property from
Claim B.3. -/
def MaximalNoisyWitness
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ)
    (sample : Finset α) (witness : Finset ℕ) : Prop :=
  NoisyWitnessCandidate
      F noise scopeSet target sample witness ∧
    NoisyArgmaxBound
      F noise scopeSet target sample.card

/-- The exact insertion step in Claim B.3.

Suppose the old stored witness maximizes the target score in `scopeSet`.
After `newCoordinate` is inserted, its own Step-A maximum is `newScore`, and
the while-loop comparison says `newScore ≤ oldSample.card`.  Every enlarged
target candidate either omits the new coordinate, hence was covered by the
old maximum, or contains it, hence can be retargeted to `newCoordinate` and
is covered by the comparison.  Therefore the literal old witness remains an
argmax in the enlarged prefix. -/
theorem claim_B_3_maximal_noisyWitness_persists_insert
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {scopeSet : Finset ℕ} {target newCoordinate newScore : ℕ}
    {oldSample : Finset α} {oldWitness : Finset ℕ}
    (hOld :
      MaximalNoisyWitness F noise scopeSet target
        oldSample oldWitness)
    (hNew :
      NoisyArgmaxBound F noise
        (insert newCoordinate scopeSet)
        newCoordinate newScore)
    (hComparison : newScore ≤ oldSample.card) :
    MaximalNoisyWitness F noise
      (insert newCoordinate scopeSet) target
      oldSample oldWitness := by
  constructor
  · exact hOld.1.mono_scope
      (Finset.subset_insert newCoordinate scopeSet)
  · intro sample witness hCandidate
    by_cases hUsesNew : newCoordinate ∈ witness
    · exact
        (hNew sample witness
          (hCandidate.retarget hUsesNew)).trans hComparison
    · exact
        hOld.2 sample witness
          (hCandidate.of_insert_scope_not_mem hUsesNew)

/-- Bound-only form of the same Claim B.3 insertion step.  This is convenient
for induction when the stored witness itself is carried separately. -/
theorem claim_B_3_noisyArgmaxBound_persists_insert
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {scopeSet : Finset ℕ}
    {target newCoordinate oldBound newScore : ℕ}
    (hOld :
      NoisyArgmaxBound F noise scopeSet target oldBound)
    (hNew :
      NoisyArgmaxBound F noise
        (insert newCoordinate scopeSet)
        newCoordinate newScore)
    (hComparison : newScore ≤ oldBound) :
    NoisyArgmaxBound F noise
      (insert newCoordinate scopeSet) target oldBound := by
  intro sample witness hCandidate
  by_cases hUsesNew : newCoordinate ∈ witness
  · exact
      (hNew sample witness
        (hCandidate.retarget hUsesNew)).trans hComparison
  · exact
      hOld sample witness
        (hCandidate.of_insert_scope_not_mem hUsesNew)

/-- Add a finite sequence of newly inserted coordinates to a scope. -/
def noisyInsertAll (scopeSet : Finset ℕ) : List ℕ → Finset ℕ
  | [] => scopeSet
  | newCoordinate :: rest =>
      noisyInsertAll (insert newCoordinate scopeSet) rest

/-- The precise comparator facts needed while a fixed old target is shifted
right by finitely many later insertions.

At each insertion, the new coordinate has a Step-A argmax bound `newScore`,
and the source's swap condition says that score is at most the fixed old
target bound. -/
def NoisyInsertionComparisonBounds
    (F : ℕ → Set α) (noise : ℕ → ℕ) (oldBound : ℕ)
    (scopeSet : Finset ℕ) : List ℕ → Prop
  | [] => True
  | newCoordinate :: rest =>
      ∃ newScore,
        NoisyArgmaxBound F noise
          (insert newCoordinate scopeSet)
          newCoordinate newScore ∧
        newScore ≤ oldBound ∧
        NoisyInsertionComparisonBounds
          F noise oldBound
          (insert newCoordinate scopeSet) rest

theorem scope_subset_noisyInsertAll
    (scopeSet : Finset ℕ) (inserted : List ℕ) :
    scopeSet ⊆ noisyInsertAll scopeSet inserted := by
  induction inserted generalizing scopeSet with
  | nil =>
      exact fun _ h => h
  | cons newCoordinate rest ih =>
      exact
        (Finset.subset_insert newCoordinate scopeSet).trans
          (ih (insert newCoordinate scopeSet))

/-- Finite-stage Claim B.3 invariant: iterating the exact one-insertion
argument preserves the old target's score bound through every crossing
allowed by the Procedure-2 comparator. -/
theorem claim_B_3_noisyArgmaxBound_persists_insertions
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {target oldBound : ℕ} {scopeSet : Finset ℕ}
    (inserted : List ℕ)
    (hOld :
      NoisyArgmaxBound F noise scopeSet target oldBound)
    (hComparisons :
      NoisyInsertionComparisonBounds
        F noise oldBound scopeSet inserted) :
    NoisyArgmaxBound F noise
      (noisyInsertAll scopeSet inserted) target oldBound := by
  induction inserted generalizing scopeSet with
  | nil =>
      simpa [noisyInsertAll] using hOld
  | cons newCoordinate rest ih =>
      obtain
        ⟨newScore, hNew, hComparison, hRest⟩ :=
        hComparisons
      have hStep :
          NoisyArgmaxBound F noise
            (insert newCoordinate scopeSet)
            target oldBound :=
        claim_B_3_noisyArgmaxBound_persists_insert
          hOld hNew hComparison
      exact
        ih hStep hRest

/-- Literal finite-stage argmax form: not only the numerical bound, but the
same stored Step-A witness remains feasible and maximal after all recorded
insertions. -/
theorem claim_B_3_maximal_noisyWitness_persists_insertions
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {target : ℕ} {scopeSet : Finset ℕ}
    {oldSample : Finset α} {oldWitness : Finset ℕ}
    (inserted : List ℕ)
    (hOld :
      MaximalNoisyWitness F noise scopeSet target
        oldSample oldWitness)
    (hComparisons :
      NoisyInsertionComparisonBounds
        F noise oldSample.card scopeSet inserted) :
    MaximalNoisyWitness F noise
      (noisyInsertAll scopeSet inserted) target
      oldSample oldWitness := by
  constructor
  · exact hOld.1.mono_scope
      (scope_subset_noisyInsertAll scopeSet inserted)
  · exact
      claim_B_3_noisyArgmaxBound_persists_insertions
        inserted hOld.2 hComparisons

/-- The final contradiction in Theorem 6: if the current distinct sample is
larger than the maintained noisy witness maximum, inserting the true target
cannot make the selected languages have finite intersection. -/
theorem theorem_6_target_passes_infiniteIntersection_check
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {scopeSet selected : Finset ℕ}
    {target complexity : ℕ} {sample : Finset α}
    (hTargetScope : target ∈ scopeSet)
    (hSelectedScope : selected ⊆ scopeSet)
    (hTargetNoise :
      NoiseContainedAt F noise target sample)
    (hSelectedNoise :
      ∀ coordinate ∈ selected,
        NoiseContainedAt F noise coordinate sample)
    (hArgmax :
      NoisyArgmaxBound
        F noise scopeSet target complexity)
    (hLarge : complexity < sample.card) :
    (indexedIntersection F (insert target selected)).Infinite := by
  by_contra hnotInfinite
  have hFinite :
      (indexedIntersection F (insert target selected)).Finite :=
    Set.not_infinite.mp hnotInfinite
  have hCandidate :
      NoisyWitnessCandidate
        F noise scopeSet target sample (insert target selected) := by
    refine
      ⟨?_, Finset.mem_insert_self target selected,
        hFinite, ?_⟩
    · intro coordinate hcoordinate
      rcases Finset.mem_insert.mp hcoordinate with rfl | hselected
      · exact hTargetScope
      · exact hSelectedScope hselected
    · intro coordinate hcoordinate
      rcases Finset.mem_insert.mp hcoordinate with rfl | hselected
      · exact hTargetNoise
      · exact hSelectedNoise coordinate hselected
  exact (Nat.not_le_of_gt hLarge)
    (hArgmax sample (insert target selected) hCandidate)

/-! ## Claim B.2 from the noisy Procedure-2 witness -/

/-- A deterministic generator realizes one time vector simultaneously over
all flattened `(noise, language)` coordinates.  The sample is repetition
free, is within the coordinate's noise budget, and the output must be both
valid and fresh. -/
def AchievesNoisyTimeVector
    (G : HistoryGenerator α) (F : ℕ → Set α)
    (noise : ℕ → ℕ) (time : TimeVector) : Prop :=
  ∀ coordinate t (xs : Fin t → α), time coordinate ≤ t →
    Function.Injective xs →
    NoiseContainedAt F noise coordinate
      (GenLimit.Generic.sequenceSample xs) →
      G t xs ∈ F coordinate ∧
        ∀ k, G t xs ≠ xs k

/-- The achievable positive time vectors in the deterministic noisy model. -/
def NoisyRealizableTimeVectors
    (F : ℕ → Set α) (noise : ℕ → ℕ) :
    Set TimeVector :=
  {time | ∃ G : HistoryGenerator α,
    AchievesNoisyTimeVector G F noise time ∧
      PositiveTimeVector time}

/-- The exact finite data from Procedure 2 consumed by Claim B.2.

`witnessSet i` is the paper's `T(L_{n,i})`.  The common intersection of the
languages in `witness i` is finite; adjoining that entire core to
`witnessSet i` produces the finite common history used by the adversary.
Every other witness coordinate occurs earlier and has smaller noisy
complexity. -/
structure NoisyProcedureWitnessCertificate
    (F : ℕ → Set α) (noise complexity : ℕ → ℕ) where
  witness : ℕ → Finset ℕ
  witnessSet : ℕ → Finset α
  complexity_eq_card :
    ∀ coordinate,
      complexity coordinate = (witnessSet coordinate).card
  self_mem :
    ∀ coordinate, 0 < complexity coordinate →
      coordinate ∈ witness coordinate
  core_finite :
    ∀ coordinate, 0 < complexity coordinate →
      (indexedIntersection F (witness coordinate)).Finite
  witnessSet_noiseContained :
    ∀ coordinate other,
      other ∈ witness coordinate →
      NoiseContainedAt F noise other
        (witnessSet coordinate)
  other_earlier :
    ∀ coordinate other,
      other ∈ witness coordinate →
      other ≠ coordinate →
      other < coordinate
  other_lower :
    ∀ coordinate other,
      other ∈ witness coordinate →
      other ≠ coordinate →
      complexity other < complexity coordinate

/-- The source adversary's enlarged sample remains within every witness
coordinate's noise budget: all newly adjoined points lie in the common
intersection. -/
theorem NoisyProcedureWitnessCertificate.adversarySample_noiseContained
    [DecidableEq α]
    {F : ℕ → Set α} {noise complexity : ℕ → ℕ}
    (certificate :
      NoisyProcedureWitnessCertificate F noise complexity)
    {coordinate other : ℕ}
    (hComplexity : 0 < complexity coordinate)
    (hOther : other ∈ certificate.witness coordinate) :
    NoiseContainedAt F noise other
      (certificate.witnessSet coordinate ∪
        (certificate.core_finite
          coordinate hComplexity).toFinset) := by
  classical
  apply
    (Finset.card_le_card ?_).trans
      (certificate.witnessSet_noiseContained
        coordinate other hOther)
  intro x hx
  have hxData := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨?_, hxData.2⟩
  rcases Finset.mem_union.mp hxData.1 with hxWitness | hxCore
  · exact hxWitness
  · have hxIntersection :
        x ∈ indexedIntersection F
          (certificate.witness coordinate) := by
      exact
        (certificate.core_finite
          coordinate hComplexity).mem_toFinset.mp hxCore
    exact (hxData.2 (hxIntersection other hOther)).elim

/-- Claim B.2: improving one noisy canonical coordinate forces a loss at an
earlier diagonal coordinate.  This is the complete deterministic
common-prefix adversary from the exact Procedure-2 witness certificate. -/
theorem claim_B_2_noisyWitness_earlierTradeoff
    {F : ℕ → Set α} {noise complexity : ℕ → ℕ}
    (certificate :
      NoisyProcedureWitnessCertificate F noise complexity) :
    EarlierTradeoff (fun coordinate => complexity coordinate + 1)
      (NoisyRealizableTimeVectors F noise) := by
  classical
  intro time htime coordinate hImprove
  obtain ⟨G, hAchieves, hPositive⟩ := htime
  change time coordinate < complexity coordinate + 1 at hImprove
  have hComplexity : 0 < complexity coordinate := by
    have hpos := hPositive coordinate
    omega
  let core : Finset α :=
    (certificate.core_finite
      coordinate hComplexity).toFinset
  let sample : Finset α :=
    certificate.witnessSet coordinate ∪ core
  let xs : Fin sample.card → α :=
    fun k => (sample.equivFin.symm k).1
  have hxsInjective : Function.Injective xs := by
    simpa only [xs] using
      GenLimit.Generic.equivFin_symm_value_injective sample
  have hsample :
      GenLimit.Generic.sequenceSample xs = sample := by
    exact GenLimit.Generic.sequenceSample_equivFin_symm sample
  have hComplexityLe : complexity coordinate ≤ sample.card := by
    rw [certificate.complexity_eq_card coordinate]
    exact Finset.card_le_card
      (Finset.subset_union_left :
        certificate.witnessSet coordinate ⊆ sample)
  have htimeAtSample : time coordinate ≤ sample.card := by
    omega
  have hTargetWitness :
      coordinate ∈ certificate.witness coordinate :=
    certificate.self_mem coordinate hComplexity
  have hTargetNoise :
      NoiseContainedAt F noise coordinate
        (GenLimit.Generic.sequenceSample xs) := by
    rw [hsample]
    exact
      certificate.adversarySample_noiseContained
        hComplexity hTargetWitness
  have hOutput :=
    hAchieves coordinate sample.card xs htimeAtSample
      hxsInjective hTargetNoise
  have hMissing :
      ∃ other,
        other ∈ certificate.witness coordinate ∧
          G sample.card xs ∉ F other := by
    by_contra hnone
    push_neg at hnone
    have hIntersection :
        G sample.card xs ∈
          indexedIntersection F
            (certificate.witness coordinate) := by
      intro other hother
      exact hnone other hother
    have hCore :
        G sample.card xs ∈ core := by
      exact
        (certificate.core_finite
          coordinate hComplexity).mem_toFinset.mpr
          hIntersection
    have hInSample : G sample.card xs ∈ sample :=
      Finset.mem_union_right _ hCore
    have hInSequence :
        G sample.card xs ∈
          GenLimit.Generic.sequenceSample xs := by
      rw [hsample]
      exact hInSample
    rw [GenLimit.Generic.mem_sequenceSample_iff] at hInSequence
    obtain ⟨k, hk⟩ := hInSequence
    exact hOutput.2 k hk.symm
  obtain ⟨other, hOtherWitness, hOtherMissing⟩ := hMissing
  have hOtherNe : other ≠ coordinate := by
    intro hEq
    subst other
    exact hOtherMissing hOutput.1
  have hOtherEarlier :
      other < coordinate :=
    certificate.other_earlier
      coordinate other hOtherWitness hOtherNe
  refine ⟨other, hOtherEarlier, ?_⟩
  by_contra hnotWorse
  have htimeOther :
      time other ≤ sample.card := by
    have hcanonical :
        time other ≤ complexity other + 1 :=
      Nat.le_of_not_gt hnotWorse
    have hlower :=
      certificate.other_lower
        coordinate other hOtherWitness hOtherNe
    omega
  have hOtherNoise :
      NoiseContainedAt F noise other
        (GenLimit.Generic.sequenceSample xs) := by
    rw [hsample]
    exact
      certificate.adversarySample_noiseContained
        hComplexity hOtherWitness
  have hOtherOutput :=
    hAchieves other sample.card xs htimeOther
      hxsInjective hOtherNoise
  exact hOtherMissing hOtherOutput.1

/-- Pareto-frontier consequence of Claim B.2. -/
theorem claim_B_2_noisyWitness_paretoOptimal
    {F : ℕ → Set α} {noise complexity : ℕ → ℕ}
    (certificate :
      NoisyProcedureWitnessCertificate F noise complexity) :
    ParetoOptimal (NoisyRealizableTimeVectors F noise)
      (fun coordinate => complexity coordinate + 1) :=
  earlierTradeoff_implies_paretoOptimal
    (claim_B_2_noisyWitness_earlierTradeoff certificate)

end GenLimit.ParetoGeneration
