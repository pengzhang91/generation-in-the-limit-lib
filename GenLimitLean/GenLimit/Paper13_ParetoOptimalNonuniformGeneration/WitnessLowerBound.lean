import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Order
import GenLimit.Core.GenericGeneration
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card

/-!
# The finite-intersection adversary behind Claim 3.1

This module isolates the semantic lower-bound argument in Claim 3.1 of
Charikar--Pabbaraju, *Pareto-optimal Non-uniform Language Generation*,
arXiv:2510.02795v1.

The paper's insertion procedure supplies, for each language, a finite witness
intersection whose other languages occur earlier and have smaller canonical
complexity.  `WitnessCertificate` records exactly those properties.  The
theorem below then carries out the common-prefix adversary against an
arbitrary deterministic generator and derives the paper's earlier-coordinate
tradeoff.  Thus the difficult combinatorial output of Procedure 1 is kept
separate from the game-theoretic lower bound that consumes it.
-/

namespace GenLimit.ParetoGeneration

/-- A deterministic generator evaluated on a finite sequence of distinct
adversarial examples. -/
abbrev HistoryGenerator (α : Type*) :=
  GenLimit.Generic.Generator α

/-- The generator realizes `time i` as a uniform correctness time for
language `F i`.  The second conclusion is the paper's novelty constraint. -/
def AchievesTimeVector
    (G : HistoryGenerator α) (F : ℕ → Set α) (time : TimeVector) : Prop :=
  ∀ i t (xs : Fin t → α), time i ≤ t →
    Function.Injective xs →
    (∀ k, xs k ∈ F i) →
      G t xs ∈ F i ∧ ∀ k, G t xs ≠ xs k

/-- Paper generation times start at one. -/
def PositiveTimeVector (time : TimeVector) : Prop :=
  ∀ i, 1 ≤ time i

/-- The semantically achievable time vectors for a fixed indexed family. -/
def RealizableTimeVectors (F : ℕ → Set α) : Set TimeVector :=
  {time | ∃ G : HistoryGenerator α,
    AchievesTimeVector G F time ∧ PositiveTimeVector time}

/-- Intersection of the languages indexed by a finite witness collection. -/
def indexedIntersection (F : ℕ → Set α) (witness : Finset ℕ) : Set α :=
  {x | ∀ j, j ∈ witness → x ∈ F j}

/-- The exact facts about Procedure 1 used by Observation 3 and Claim 3.1.

`history i` enumerates the finite witness intersection without repetition.
When the complexity is positive, the witness contains the target.  Every
other witness language has an earlier index and strictly lower complexity.
-/
structure WitnessCertificate
    (F : ℕ → Set α) (complexity : ℕ → ℕ) where
  witness : ℕ → Finset ℕ
  history : ∀ i, Fin (complexity i) → α
  history_injective : ∀ i, Function.Injective (history i)
  history_exact :
    ∀ i, 0 < complexity i →
      Set.range (history i) = indexedIntersection F (witness i)
  self_mem : ∀ i, 0 < complexity i → i ∈ witness i
  other_earlier :
    ∀ i j, j ∈ witness i → j ≠ i → j < i
  other_lower :
    ∀ i j, j ∈ witness i → j ≠ i →
      complexity j < complexity i

/-- Every point in the certified history belongs to every witness language. -/
theorem WitnessCertificate.history_mem
    (C : WitnessCertificate F complexity) (i j : ℕ)
    (hcomplexity : 0 < complexity i)
    (hj : j ∈ C.witness i) (k : Fin (complexity i)) :
    C.history i k ∈ F j := by
  have hrange : C.history i k ∈ Set.range (C.history i) :=
    Set.mem_range_self k
  rw [C.history_exact i hcomplexity] at hrange
  exact hrange j hj

/-- Claim 3.1: improving a certified canonical coordinate forces a loss at
an earlier coordinate.

The proof presents the whole finite witness intersection.  Correctness for
the improved target forces a new output in that target but outside the
intersection.  Some earlier witness language therefore rejects the same
output, and its smaller certified complexity makes this a violation of the
claimed earlier time bound.
-/
theorem witnessCertificate_earlierTradeoff
    {F : ℕ → Set α} {complexity : ℕ → ℕ}
    (C : WitnessCertificate F complexity) :
    EarlierTradeoff (fun i => complexity i + 1)
      (RealizableTimeVectors F) := by
  intro time htime i himprove
  obtain ⟨G, hAchieves, hPositive⟩ := htime
  change time i < complexity i + 1 at himprove
  have hcomplexity : 0 < complexity i := by
    have hpos := hPositive i
    omega
  let xs := C.history i
  have htimeAtWitness : time i ≤ complexity i := by
    omega
  have htargetHistory : ∀ k, xs k ∈ F i := by
    intro k
    exact C.history_mem i i hcomplexity (C.self_mem i hcomplexity) k
  have hout :=
    hAchieves i (complexity i) xs htimeAtWitness
      (C.history_injective i) htargetHistory
  have hmissing :
      ∃ j, j ∈ C.witness i ∧ G (complexity i) xs ∉ F j := by
    by_contra hnone
    push_neg at hnone
    have hintersection :
        G (complexity i) xs ∈ indexedIntersection F (C.witness i) := by
      intro j hj
      exact hnone j hj
    rw [← C.history_exact i hcomplexity] at hintersection
    obtain ⟨k, hk⟩ := hintersection
    exact hout.2 k hk.symm
  obtain ⟨j, hjWitness, hjMissing⟩ := hmissing
  have hji : j ≠ i := by
    intro hEq
    subst j
    exact hjMissing hout.1
  have hjEarlier : j < i := C.other_earlier i j hjWitness hji
  refine ⟨j, hjEarlier, ?_⟩
  by_contra hnotWorse
  have htimeJ : time j ≤ complexity i := by
    have hjLower := C.other_lower i j hjWitness hji
    have : time j ≤ complexity j + 1 := Nat.le_of_not_gt hnotWorse
    omega
  have hjHistory : ∀ k, xs k ∈ F j := by
    intro k
    exact C.history_mem i j hcomplexity hjWitness k
  have houtJ :=
    hAchieves j (complexity i) xs htimeJ
      (C.history_injective i) hjHistory
  exact hjMissing houtJ.1

/-- The Pareto conclusion of Claim 3.1 and Definition 3. -/
theorem witnessCertificate_paretoOptimal
    {F : ℕ → Set α} {complexity : ℕ → ℕ}
    (C : WitnessCertificate F complexity) :
    ParetoOptimal (RealizableTimeVectors F)
      (fun i => complexity i + 1) :=
  earlierTradeoff_implies_paretoOptimal
    (witnessCertificate_earlierTradeoff C)

/-! ## Procedure 1: the exact finite argmax step -/

/-- A subcollection considered in Step (b.i) of Procedure 1: it lies in the
current finite prefix, contains the language being inserted, and has finite
intersection. -/
def FiniteIntersectionCandidate
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ) (witness : Finset ℕ) : Prop :=
  witness ⊆ scopeSet ∧ target ∈ witness ∧
    (indexedIntersection F witness).Finite

/-- All Step-(b.i) candidates form a genuine finite search space. -/
noncomputable def finiteIntersectionCandidates
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ) : Finset (Finset ℕ) := by
  classical
  exact scopeSet.powerset.filter
    (fun witness =>
      target ∈ witness ∧
        (indexedIntersection F witness).Finite)

@[simp] theorem mem_finiteIntersectionCandidates
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ) (witness : Finset ℕ) :
    witness ∈ finiteIntersectionCandidates F scopeSet target ↔
      FiniteIntersectionCandidate F scopeSet target witness := by
  classical
  simp [finiteIntersectionCandidates,
    FiniteIntersectionCandidate]

/-- The finite intersection size optimized in Step (b.i). -/
noncomputable def finiteIntersectionScore
    (F : ℕ → Set α) (witness : Finset ℕ) : ℕ :=
  (indexedIntersection F witness).ncard

/-- Step (b.i) is well-defined: whenever a finite-intersection
subcollection exists, one of the finitely many candidates attains the
largest finite intersection size. -/
theorem exists_maximal_finiteIntersectionCandidate
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ)
    (hexists : ∃ witness,
      FiniteIntersectionCandidate F scopeSet target witness) :
    ∃ witness,
      FiniteIntersectionCandidate F scopeSet target witness ∧
      ∀ other,
        FiniteIntersectionCandidate F scopeSet target other →
        finiteIntersectionScore F other ≤
          finiteIntersectionScore F witness := by
  classical
  let candidates :=
    finiteIntersectionCandidates F scopeSet target
  have hnonempty : candidates.Nonempty := by
    obtain ⟨witness, hwitness⟩ := hexists
    exact ⟨witness,
      (mem_finiteIntersectionCandidates
        F scopeSet target witness).mpr hwitness⟩
  obtain ⟨witness, hwitnessMem, hmax⟩ :=
    Finset.exists_max_image candidates
      (finiteIntersectionScore F) hnonempty
  refine ⟨witness,
    (mem_finiteIntersectionCandidates
      F scopeSet target witness).mp hwitnessMem, ?_⟩
  intro other hother
  exact hmax other
    ((mem_finiteIntersectionCandidates
      F scopeSet target other).mpr hother)

/-- The witness selected by Step (b.i), with the source's empty
subcollection convention when there is no finite-intersection candidate. -/
noncomputable def procedureStepWitness
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ) : Finset ℕ := by
  classical
  if h : ∃ witness,
      FiniteIntersectionCandidate F scopeSet target witness then
    exact Classical.choose
      (exists_maximal_finiteIntersectionCandidate
        F scopeSet target h)
  else
    exact ∅

/-- The `m_check` value in Step (b.i). -/
noncomputable def procedureStepComplexity
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ) : ℕ := by
  classical
  if h : ∃ witness,
      FiniteIntersectionCandidate F scopeSet target witness then
    exact finiteIntersectionScore F
      (procedureStepWitness F scopeSet target)
  else
    exact 0

theorem procedureStepWitness_spec
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ)
    (h : ∃ witness,
      FiniteIntersectionCandidate F scopeSet target witness) :
    FiniteIntersectionCandidate F scopeSet target
        (procedureStepWitness F scopeSet target) ∧
      ∀ other,
        FiniteIntersectionCandidate F scopeSet target other →
        finiteIntersectionScore F other ≤
          finiteIntersectionScore F
            (procedureStepWitness F scopeSet target) := by
  classical
  simp only [procedureStepWitness, dif_pos h]
  exact Classical.choose_spec
    (exists_maximal_finiteIntersectionCandidate
      F scopeSet target h)

theorem procedureStepComplexity_eq_score
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ)
    (h : ∃ witness,
      FiniteIntersectionCandidate F scopeSet target witness) :
    procedureStepComplexity F scopeSet target =
      finiteIntersectionScore F
        (procedureStepWitness F scopeSet target) := by
  classical
  simp [procedureStepComplexity, h]

theorem procedureStepComplexity_eq_zero
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ)
    (h : ¬∃ witness,
      FiniteIntersectionCandidate F scopeSet target witness) :
    procedureStepComplexity F scopeSet target = 0 := by
  classical
  simp [procedureStepComplexity, h]

/-- The empty branch of Step (b.i) is exactly the absence of any candidate,
so assigning complexity zero does not discard a finite intersection. -/
theorem no_finiteIntersectionCandidate_iff_candidates_empty
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ) :
    (¬∃ witness,
      FiniteIntersectionCandidate F scopeSet target witness) ↔
      finiteIntersectionCandidates F scopeSet target = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  simp

/-- If every source language is infinite, a nonempty Procedure-1 witness
cannot consist only of the target language.  This is the first assertion of
Observation 3. -/
theorem finiteIntersectionCandidate_contains_other
    (F : ℕ → Set α) (scopeSet : Finset ℕ)
    (target : ℕ) (hInfinite : (F target).Infinite)
    {witness : Finset ℕ}
    (hCandidate :
      FiniteIntersectionCandidate F scopeSet target witness) :
    ∃ j, j ∈ witness ∧ j ≠ target := by
  by_contra hnone
  push_neg at hnone
  have hwitness : witness = {target} := by
    apply Finset.Subset.antisymm
    · intro j hj
      simp [hnone j hj]
    · simpa using hCandidate.2.1
  have hintersection :
      indexedIntersection F witness = F target := by
    subst witness
    ext x
    simp [indexedIntersection]
  exact hInfinite
    (by simpa [hintersection] using hCandidate.2.2)

/-- Zero-based "earlier language" part of Observation 3. -/
theorem finiteIntersectionCandidate_other_earlier
    (F : ℕ → Set α) {i : ℕ}
    {scopeSet witness : Finset ℕ}
    (hscope : scopeSet ⊆ Finset.range (i + 1))
    (hCandidate :
      FiniteIntersectionCandidate F scopeSet i witness)
    {j : ℕ} (hj : j ∈ witness) (hji : j ≠ i) :
    j < i := by
  have hjScope : j ∈ scopeSet := hCandidate.1 hj
  have hjLe : j < i + 1 :=
    Finset.mem_range.mp (hscope hjScope)
  omega

/-- The local invariant behind Claim 3.2.  If an old witness maximizes the
finite-intersection score in `prefix`, and every newly available candidate
that actually uses `newIndex` has no larger score, then the same old
witness remains an argmax after insertion. -/
theorem maximal_finiteIntersectionCandidate_persists_insert
    (F : ℕ → Set α)
    {scopeSet : Finset ℕ} {target newIndex : ℕ}
    {witness : Finset ℕ}
    (hCandidate :
      FiniteIntersectionCandidate F scopeSet target witness)
    (hMaximal :
      ∀ other,
        FiniteIntersectionCandidate F scopeSet target other →
        finiteIntersectionScore F other ≤
          finiteIntersectionScore F witness)
    (hNewBound :
      ∀ other,
        FiniteIntersectionCandidate F
          (insert newIndex scopeSet) target other →
        newIndex ∈ other →
        finiteIntersectionScore F other ≤
          finiteIntersectionScore F witness) :
    FiniteIntersectionCandidate F
        (insert newIndex scopeSet) target witness ∧
      ∀ other,
        FiniteIntersectionCandidate F
          (insert newIndex scopeSet) target other →
        finiteIntersectionScore F other ≤
          finiteIntersectionScore F witness := by
  classical
  constructor
  · exact ⟨fun j hj =>
      Finset.mem_insert_of_mem (hCandidate.1 hj),
      hCandidate.2⟩
  · intro other hOther
    by_cases hnew : newIndex ∈ other
    · exact hNewBound other hOther hnew
    · apply hMaximal other
      refine ⟨?_, hOther.2⟩
      intro j hj
      have hjInsert : j ∈ insert newIndex scopeSet :=
        hOther.1 hj
      rcases Finset.mem_insert.mp hjInsert with rfl | hjPrefix
      · exact (hnew hj).elim
      · exact hjPrefix

end GenLimit.ParetoGeneration
