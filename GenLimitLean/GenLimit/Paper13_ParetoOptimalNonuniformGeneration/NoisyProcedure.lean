import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.NoisyWitness
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.ArbitraryScheduler
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.VariantExactPareto
import GenLimit.Support.Fresh
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Pairwise

/-!
# A totalized execution of noisy Procedure 2

This module continues the probability-free part of Charikar--Pabbaraju,
*Pareto-optimal Non-uniform Language Generation*, arXiv:2510.02795v1,
Procedure 2 and Theorem 6.

The printed Step A asks for a largest feasible finite set, but at the first
diagonal coordinate there is no feasible set: the only allowed
subcollection consists of one infinite language and therefore has infinite
intersection.  `procedure_2_first_step_has_no_candidate` records that source
defect.

Here the repair is explicit.  `totalNoisyStepSample` and
`totalNoisyStepWitness` return the genuine Step-A argmax when a candidate
exists, and return the empty sample and empty witness otherwise.  The
corresponding score is always total and always bounds every feasible
candidate.  This is the same zero-score convention used by the paper's
Procedure 1; no literal candidate is asserted in the empty branch.

Using that repaired step, the file constructs the complete finite
right-to-left insertion execution, proves the stage-wide Claim B.3 argmax
invariant, assembles the witness certificate consumed by Claim B.2, and
builds the scheduler-driven deterministic generator of Theorem 6 at the
repository's distinct-history noisy semantic boundary.  No probability law,
runtime bound, or membership-oracle implementation is claimed.
-/

namespace GenLimit.ParetoGeneration

/-! ## The corrected, total Step A -/

/-- A finite scope has a finite maximum noise budget. -/
def noisyScopeMaxNoise (noise : ℕ → ℕ) (scopeSet : Finset ℕ) : ℕ :=
  scopeSet.sup noise

theorem noise_le_noisyScopeMaxNoise
    (noise : ℕ → ℕ) {scopeSet : Finset ℕ}
    {coordinate : ℕ} (hcoordinate : coordinate ∈ scopeSet) :
    noise coordinate ≤ noisyScopeMaxNoise noise scopeSet := by
  exact Finset.le_sup (f := noise) hcoordinate

/-- Claim B.1 with the finite-scope noise maximum discharged internally. -/
theorem exists_maximal_noisyWitness_of_exists
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ)
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
          other.card ≤ sample.card :=
  claim_B_1_exists_maximal_noisyWitness
    F noise scopeSet target
    (noisyScopeMaxNoise noise scopeSet)
    (fun _ hcoordinate =>
      noise_le_noisyScopeMaxNoise noise hcoordinate)
    hExists

/-- Corrected Step A: choose an actual largest feasible finite sample when
one exists, and the empty sample otherwise. -/
noncomputable def totalNoisyStepSample
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ) : Finset α := by
  classical
  if hExists :
      ∃ sample,
        NoisyProcedureSampleCandidate
          F noise scopeSet target sample then
    exact Classical.choose
      (exists_maximal_noisyWitness_of_exists
        F noise scopeSet target hExists)
  else
    exact ∅

/-- Corrected Step A's witness subcollection.  In the nonempty branch this
is a genuine witness for `totalNoisyStepSample`; in the repaired empty
branch it is empty. -/
noncomputable def totalNoisyStepWitness
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ) : Finset ℕ := by
  classical
  if hCandidate :
      NoisyProcedureSampleCandidate F noise scopeSet target
        (totalNoisyStepSample F noise scopeSet target) then
    exact Classical.choose hCandidate
  else
    exact ∅

/-- The totalized noisy complexity assigned by repaired Step A. -/
noncomputable def totalNoisyStepComplexity
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ) : ℕ :=
  (totalNoisyStepSample F noise scopeSet target).card

theorem totalNoisyStepSample_spec
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ)
    (hExists :
      ∃ sample,
        NoisyProcedureSampleCandidate
          F noise scopeSet target sample) :
    NoisyProcedureSampleCandidate F noise scopeSet target
        (totalNoisyStepSample F noise scopeSet target) ∧
      ∀ other,
        NoisyProcedureSampleCandidate F noise scopeSet target other →
          other.card ≤
            (totalNoisyStepSample F noise scopeSet target).card := by
  classical
  simp only [totalNoisyStepSample, dif_pos hExists]
  exact Classical.choose_spec
    (exists_maximal_noisyWitness_of_exists
      F noise scopeSet target hExists)

theorem totalNoisyStepWitness_spec
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ)
    (hExists :
      ∃ sample,
        NoisyProcedureSampleCandidate
          F noise scopeSet target sample) :
    NoisyWitnessCandidate F noise scopeSet target
      (totalNoisyStepSample F noise scopeSet target)
      (totalNoisyStepWitness F noise scopeSet target) := by
  classical
  have hCandidate :=
    (totalNoisyStepSample_spec F noise scopeSet target hExists).1
  simp only [totalNoisyStepWitness, dif_pos hCandidate]
  exact Classical.choose_spec hCandidate

theorem totalNoisyStepComplexity_eq_card
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ) :
    totalNoisyStepComplexity F noise scopeSet target =
      (totalNoisyStepSample F noise scopeSet target).card :=
  rfl

/-- The corrected max-value form of Step A is valid even when the source
candidate class is empty. -/
theorem totalNoisyStep_argmaxBound
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ) :
    NoisyArgmaxBound F noise scopeSet target
      (totalNoisyStepComplexity F noise scopeSet target) := by
  classical
  intro sample witness hCandidate
  by_cases hExists :
      ∃ other,
        NoisyProcedureSampleCandidate
          F noise scopeSet target other
  · exact
      (totalNoisyStepSample_spec F noise scopeSet target hExists).2
        sample ⟨witness, hCandidate⟩
  · exact (hExists ⟨sample, witness, hCandidate⟩).elim

/-- Positive repaired score implies that Step A was in its genuine
candidate branch. -/
theorem totalNoisyStep_positive_candidate
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ)
    (hPositive :
      0 < totalNoisyStepComplexity F noise scopeSet target) :
    NoisyWitnessCandidate F noise scopeSet target
      (totalNoisyStepSample F noise scopeSet target)
      (totalNoisyStepWitness F noise scopeSet target) := by
  classical
  apply totalNoisyStepWitness_spec
  by_contra hNone
  have hEmpty :
      totalNoisyStepSample F noise scopeSet target = ∅ := by
    simp [totalNoisyStepSample, hNone]
  rw [totalNoisyStepComplexity, hEmpty] at hPositive
  simp at hPositive

theorem totalNoisyStepComplexity_eq_zero_of_no_candidate
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (scopeSet : Finset ℕ) (target : ℕ)
    (hNone :
      ¬∃ sample,
        NoisyProcedureSampleCandidate
          F noise scopeSet target sample) :
    totalNoisyStepComplexity F noise scopeSet target = 0 := by
  classical
  simp [totalNoisyStepComplexity, totalNoisyStepSample, hNone]

theorem NoisyProcedureSampleCandidate.mono_scope
    {F : ℕ → Set α} {noise : ℕ → ℕ}
    {smallScope largeScope : Finset ℕ} {target : ℕ}
    {sample : Finset α}
    (hCandidate :
      NoisyProcedureSampleCandidate
        F noise smallScope target sample)
    (hScope : smallScope ⊆ largeScope) :
    NoisyProcedureSampleCandidate
      F noise largeScope target sample := by
  obtain ⟨witness, hWitness⟩ := hCandidate
  exact ⟨witness, hWitness.mono_scope hScope⟩

/-- The repaired Step-A maximum is monotone when more coordinates enter the
finite scope. -/
theorem totalNoisyStepComplexity_mono
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    {smallScope largeScope : Finset ℕ} (target : ℕ)
    (hScope : smallScope ⊆ largeScope) :
    totalNoisyStepComplexity F noise smallScope target ≤
      totalNoisyStepComplexity F noise largeScope target := by
  classical
  by_cases hExists :
      ∃ sample,
        NoisyProcedureSampleCandidate
          F noise smallScope target sample
  · let sample :=
      totalNoisyStepSample F noise smallScope target
    have hSmall :
        NoisyProcedureSampleCandidate
          F noise smallScope target sample :=
      (totalNoisyStepSample_spec
        F noise smallScope target hExists).1
    obtain ⟨witness, hWitness⟩ := hSmall
    exact
      totalNoisyStep_argmaxBound
        F noise largeScope target sample witness
        (hWitness.mono_scope hScope)
  · rw [totalNoisyStepComplexity_eq_zero_of_no_candidate
      F noise smallScope target hExists]
    exact Nat.zero_le _

/-! ## The repaired right-to-left insertion loop -/

def noisyInsertionScope (left : List ℕ) (target : ℕ) : Finset ℕ :=
  insert target left.toFinset

noncomputable def noisyInsertionScore
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (left : List ℕ) (target : ℕ) : ℕ :=
  totalNoisyStepComplexity F noise
    (noisyInsertionScope left target) target

structure NoisyInsertionSplit
    (F : ℕ → Set α) (noise complexity : ℕ → ℕ)
    (target : ℕ) (oldOrder : List ℕ) where
  left : List ℕ
  right : List ℕ
  split : oldOrder = left ++ right
  left_lower :
    ∀ i, i ∈ left →
      complexity i < noisyInsertionScore F noise left target
  crossed_upper :
    ∀ before i after,
      right = before ++ i :: after →
        noisyInsertionScore F noise
          (left ++ before ++ [i]) target ≤ complexity i

theorem exists_noisyInsertionSplit
    (F : ℕ → Set α) (noise complexity : ℕ → ℕ)
    (target : ℕ) (oldOrder : List ℕ)
    (hSorted :
      oldOrder.Pairwise (fun i j => complexity i ≤ complexity j))
    (hNodup : oldOrder.Nodup) :
    Nonempty
      (NoisyInsertionSplit F noise complexity target oldOrder) := by
  induction oldOrder using List.reverseRecOn with
  | nil =>
      exact ⟨{
        left := []
        right := []
        split := by simp
        left_lower := by simp
        crossed_upper := by simp
      }⟩
  | append_singleton oldOrder last ih =>
      by_cases hStop :
          complexity last <
            noisyInsertionScore F noise
              (oldOrder ++ [last]) target
      · refine ⟨{
          left := oldOrder ++ [last]
          right := []
          split := by simp
          left_lower := ?_
          crossed_upper := by simp
        }⟩
        intro i hi
        have hle : complexity i ≤ complexity last := by
          have hpairs := (List.pairwise_append.mp hSorted).2.2
          rcases List.mem_append.mp hi with hiOld | hiLast
          · exact hpairs i hiOld last (by simp)
          · have : i = last := by simpa using hiLast
            subst i
            exact Nat.le_refl _
        exact hle.trans_lt hStop
      · have hOldSorted :
            oldOrder.Pairwise
              (fun i j => complexity i ≤ complexity j) :=
          (List.pairwise_append.mp hSorted).1
        have hOldNodup : oldOrder.Nodup :=
          (List.nodup_append.mp hNodup).1
        obtain ⟨prior⟩ := ih hOldSorted hOldNodup
        refine ⟨{
          left := prior.left
          right := prior.right ++ [last]
          split := ?_
          left_lower := prior.left_lower
          crossed_upper := ?_
        }⟩
        · calc
            oldOrder ++ [last] =
                (prior.left ++ prior.right) ++ [last] :=
              congrArg (fun xs => xs ++ [last]) prior.split
            _ = prior.left ++ (prior.right ++ [last]) := by
              simp [List.append_assoc]
        · intro before i after hDecomp
          have hWholeEq :
              oldOrder ++ [last] =
                prior.left ++ (prior.right ++ [last]) := by
            calc
              oldOrder ++ [last] =
                  (prior.left ++ prior.right) ++ [last] :=
                congrArg (fun xs => xs ++ [last]) prior.split
              _ = prior.left ++ (prior.right ++ [last]) := by
                simp [List.append_assoc]
          have hRightNodup :
              (prior.right ++ [last]).Nodup := by
            have hWholeNodup :
                (prior.left ++ (prior.right ++ [last])).Nodup := by
              exact hWholeEq ▸ hNodup
            exact hWholeNodup.of_append_right
          by_cases hi : i = last
          · subst i
            have hBefore : before = prior.right :=
              prefix_eq_of_nodup_decompositions
                (before₂ := prior.right) (after₂ := [])
                hRightNodup hDecomp (by rfl)
            subst before
            rw [← prior.split]
            exact Nat.le_of_not_gt hStop
          · have hiRight : i ∈ prior.right := by
              have : i ∈ prior.right ++ [last] := by
                rw [hDecomp]
                simp
              simpa [hi] using this
            obtain ⟨priorBefore, priorAfter, hPriorDecomp⟩ :=
              List.mem_iff_append.mp hiRight
            have hCanonical :
                prior.right ++ [last] =
                  priorBefore ++ i :: (priorAfter ++ [last]) := by
              rw [hPriorDecomp]
              simp [List.append_assoc]
            have hBefore : before = priorBefore :=
              prefix_eq_of_nodup_decompositions hRightNodup
                hDecomp hCanonical
            subst before
            exact prior.crossed_upper
              priorBefore i priorAfter hPriorDecomp

theorem noisyInsertionScope_mono
    {small large : List ℕ} {target : ℕ}
    (hSub : ∀ i, i ∈ small → i ∈ large) :
    noisyInsertionScope small target ⊆
      noisyInsertionScope large target := by
  classical
  intro i hi
  simp only [noisyInsertionScope, Finset.mem_insert,
    List.mem_toFinset] at hi ⊢
  exact hi.elim Or.inl (fun h => Or.inr (hSub i h))

theorem noisyInsertionScore_mono
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    {small large : List ℕ} (target : ℕ)
    (hSub : ∀ i, i ∈ small → i ∈ large) :
    noisyInsertionScore F noise small target ≤
      noisyInsertionScore F noise large target :=
  totalNoisyStepComplexity_mono F noise target
    (noisyInsertionScope_mono hSub)

theorem NoisyInsertionSplit.right_upper
    {F : ℕ → Set α} {noise complexity : ℕ → ℕ}
    {target : ℕ} {oldOrder : List ℕ}
    (split :
      NoisyInsertionSplit F noise complexity target oldOrder)
    {i : ℕ} (hi : i ∈ split.right) :
    noisyInsertionScore F noise split.left target ≤
      complexity i := by
  obtain ⟨before, after, hDecomp⟩ :=
    List.mem_iff_append.mp hi
  have hMono :
      noisyInsertionScore F noise split.left target ≤
        noisyInsertionScore F noise
          (split.left ++ before ++ [i]) target := by
    apply noisyInsertionScore_mono F noise target
    intro j hj
    simp only [List.mem_append, List.mem_singleton]
    exact Or.inl (Or.inl hj)
  exact hMono.trans
    (split.crossed_upper before i after hDecomp)

/-! ## Stage-wide repaired Claim B.3 -/

/-- The corrected Claim B.3 max-value invariant at every coordinate of an
ordered finite stage. -/
def NoisyOrderArgmaxBounds
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (order : List ℕ) (complexity : ℕ → ℕ) : Prop :=
  ∀ before i after,
    order = before ++ i :: after →
      NoisyArgmaxBound F noise
        (insert i before.toFinset) i (complexity i)

/-- One repaired Procedure-2 insertion preserves the max-value invariant
for every old coordinate and establishes it for the new coordinate. -/
theorem NoisyInsertionSplit.orderArgmaxBounds
    {F : ℕ → Set α} {noise complexity : ℕ → ℕ}
    {target : ℕ} {oldOrder : List ℕ}
    (split :
      NoisyInsertionSplit F noise complexity target oldOrder)
    (hOldNodup : oldOrder.Nodup)
    (hTarget : target ∉ oldOrder)
    (hOld :
      NoisyOrderArgmaxBounds F noise oldOrder complexity) :
    NoisyOrderArgmaxBounds F noise
      (split.left ++ target :: split.right)
      (setComplexity complexity target
        (noisyInsertionScore F noise split.left target)) := by
  classical
  have hNewNodup :
      (split.left ++ target :: split.right).Nodup := by
    rw [List.nodup_middle]
    have : (target :: oldOrder).Nodup :=
      List.nodup_cons.mpr ⟨hTarget, hOldNodup⟩
    simpa [split.split] using this
  intro before i after hDecomp
  by_cases hiTarget : i = target
  · subst i
    have hBefore : before = split.left :=
      prefix_eq_of_nodup_decompositions hNewNodup hDecomp rfl
    subst before
    simpa [noisyInsertionScore, noisyInsertionScope] using
      totalNoisyStep_argmaxBound F noise
        (noisyInsertionScope split.left target) target
  · have hiMem :
        i ∈ split.left ++ target :: split.right := by
      rw [hDecomp]
      simp
    have hiSides : i ∈ split.left ∨ i ∈ split.right := by
      simpa [hiTarget] using hiMem
    rcases hiSides with hiLeft | hiRight
    · obtain ⟨leftBefore, leftAfter, hLeftDecomp⟩ :=
        List.mem_iff_append.mp hiLeft
      have hCanonical :
          split.left ++ target :: split.right =
            leftBefore ++ i ::
              (leftAfter ++ target :: split.right) := by
        rw [hLeftDecomp]
        simp [List.append_assoc]
      have hBefore : before = leftBefore :=
        prefix_eq_of_nodup_decompositions hNewNodup
          hDecomp hCanonical
      subst before
      have hOldDecomp :
          oldOrder =
            leftBefore ++ i :: (leftAfter ++ split.right) := by
        calc
          oldOrder = split.left ++ split.right := split.split
          _ = (leftBefore ++ i :: leftAfter) ++ split.right := by
            rw [hLeftDecomp]
          _ = leftBefore ++ i :: (leftAfter ++ split.right) := by
            simp [List.append_assoc]
      simpa [setComplexity, hiTarget] using
        hOld leftBefore i (leftAfter ++ split.right) hOldDecomp
    · obtain ⟨rightBefore, rightAfter, hRightDecomp⟩ :=
        List.mem_iff_append.mp hiRight
      have hCanonical :
          split.left ++ target :: split.right =
            (split.left ++ target :: rightBefore) ++
              i :: rightAfter := by
        rw [hRightDecomp]
        simp [List.append_assoc]
      have hBefore :
          before = split.left ++ target :: rightBefore :=
        prefix_eq_of_nodup_decompositions hNewNodup
          hDecomp hCanonical
      subst before
      have hOldDecomp :
          oldOrder =
            (split.left ++ rightBefore) ++ i :: rightAfter := by
        calc
          oldOrder = split.left ++ split.right := split.split
          _ = split.left ++
              (rightBefore ++ i :: rightAfter) := by
            rw [hRightDecomp]
          _ = (split.left ++ rightBefore) ++ i :: rightAfter := by
            simp [List.append_assoc]
      have hOldBound :
          NoisyArgmaxBound F noise
            (insert i (split.left ++ rightBefore).toFinset)
            i (complexity i) :=
        hOld (split.left ++ rightBefore) i rightAfter hOldDecomp
      have hNewBound :
          NoisyArgmaxBound F noise
            (insert target
              (insert i
                (split.left ++ rightBefore).toFinset))
            target
            (noisyInsertionScore F noise
              (split.left ++ rightBefore ++ [i]) target) := by
        simpa [noisyInsertionScore, noisyInsertionScope,
          List.toFinset_append, Finset.insert_comm,
          Finset.union_insert] using
          totalNoisyStep_argmaxBound F noise
            (noisyInsertionScope
              (split.left ++ rightBefore ++ [i]) target)
            target
      have hPersist :=
        claim_B_3_noisyArgmaxBound_persists_insert
          hOldBound hNewBound
          (split.crossed_upper
            rightBefore i rightAfter hRightDecomp)
      simpa [setComplexity, hiTarget, List.toFinset_append,
        Finset.insert_comm, Finset.union_insert] using hPersist

/-- The repaired insertion remains sorted by its finalized noisy
complexities. -/
theorem NoisyInsertionSplit.newOrder_pairwise
    {F : ℕ → Set α} {noise complexity : ℕ → ℕ}
    {target : ℕ} {oldOrder : List ℕ}
    (split :
      NoisyInsertionSplit F noise complexity target oldOrder)
    (hOldSorted :
      oldOrder.Pairwise (fun i j => complexity i ≤ complexity j))
    (hTarget : target ∉ oldOrder) :
    (split.left ++ target :: split.right).Pairwise
      (fun i j =>
        setComplexity complexity target
            (noisyInsertionScore F noise split.left target) i ≤
          setComplexity complexity target
            (noisyInsertionScore F noise split.left target) j) := by
  have hTargetLeft : target ∉ split.left := by
    intro h
    apply hTarget
    rw [split.split]
    simp [h]
  have hTargetRight : target ∉ split.right := by
    intro h
    apply hTarget
    rw [split.split]
    simp [h]
  have hOldSorted' :
      (split.left ++ split.right).Pairwise
        (fun i j => complexity i ≤ complexity j) := by
    rw [← split.split]
    exact hOldSorted
  have hLeftSorted :
      split.left.Pairwise
        (fun i j => complexity i ≤ complexity j) :=
    (List.pairwise_append.mp hOldSorted').1
  have hRightSorted :
      split.right.Pairwise
        (fun i j => complexity i ≤ complexity j) :=
    (List.pairwise_append.mp hOldSorted').2.1
  have hOldCross :
      ∀ i, i ∈ split.left →
        ∀ j, j ∈ split.right →
          complexity i ≤ complexity j :=
    (List.pairwise_append.mp hOldSorted').2.2
  rw [List.pairwise_append]
  refine ⟨pairwise_setComplexity_of_not_mem
      hTargetLeft hLeftSorted, ?_, ?_⟩
  · rw [List.pairwise_cons]
    constructor
    · intro j hj
      have hjTarget : j ≠ target := by
        intro h
        subst j
        exact hTargetRight hj
      simpa [setComplexity, hjTarget] using
        split.right_upper hj
    · exact pairwise_setComplexity_of_not_mem
        hTargetRight hRightSorted
  · intro i hi j hj
    rcases List.mem_cons.mp hj with hjTargetEq | hjRight
    · subst j
      have hiTarget : i ≠ target := by
        intro h
        subst i
        exact hTargetLeft hi
      simp only [setComplexity_other _ hiTarget,
        setComplexity_same]
      exact Nat.le_of_lt (split.left_lower i hi)
    · have hiTarget : i ≠ target := by
        intro h
        subst i
        exact hTargetLeft hi
      have hjTarget : j ≠ target := by
        intro h
        subst j
        exact hTargetRight hjRight
      simpa [setComplexity, hiTarget, hjTarget] using
        hOldCross i hi j hjRight

theorem NoisyInsertionSplit.newOrder_perm
    {F : ℕ → Set α} {noise complexity : ℕ → ℕ}
    {target : ℕ} {oldOrder : List ℕ}
    (split :
      NoisyInsertionSplit F noise complexity target oldOrder) :
    (split.left ++ target :: split.right).Perm
      (oldOrder ++ [target]) := by
  have hMove :
      (split.left ++ target :: split.right).Perm
        (split.left ++ (split.right ++ [target])) :=
    List.Perm.append_left split.left
      (List.perm_append_singleton target split.right).symm
  calc
    (split.left ++ target :: split.right).Perm
        (split.left ++ (split.right ++ [target])) := hMove
    _ = (split.left ++ split.right) ++ [target] := by
      simp [List.append_assoc]
    _ = oldOrder ++ [target] :=
      congrArg (fun xs => xs ++ [target]) split.split.symm

/-! ## Certified finite executions -/

/-- A repaired Procedure-2 execution after inserting diagonal coordinates
`0, ..., stage - 1`. -/
structure NoisyProcedureStage
    (F : ℕ → Set α) (noise : ℕ → ℕ) (stage : ℕ) where
  order : List ℕ
  complexity : ℕ → ℕ
  witnessSet : ℕ → Finset α
  witness : ℕ → Finset ℕ
  order_perm : order.Perm (List.range stage)
  sorted :
    order.Pairwise (fun i j => complexity i ≤ complexity j)
  max_bounds :
    NoisyOrderArgmaxBounds F noise order complexity
  complexity_eq_card :
    ∀ i, i < stage → complexity i = (witnessSet i).card
  witness_positive :
    ∀ i, i < stage → 0 < complexity i →
      NoisyWitnessCandidate F noise (Finset.range (i + 1)) i
        (witnessSet i) (witness i)
  witness_noiseContained :
    ∀ i, i < stage → ∀ j, j ∈ witness i →
      NoiseContainedAt F noise j (witnessSet i)
  witness_other_lower :
    ∀ i, i < stage → ∀ j, j ∈ witness i → j ≠ i →
      j < i ∧ complexity j < complexity i

def setNoisyWitnessSet
    (witnessSet : ℕ → Finset α)
    (target : ℕ) (value : Finset α) : ℕ → Finset α :=
  fun i => if i = target then value else witnessSet i

@[simp] theorem setNoisyWitnessSet_same
    (witnessSet : ℕ → Finset α) (target : ℕ)
    (value : Finset α) :
    setNoisyWitnessSet witnessSet target value target = value := by
  simp [setNoisyWitnessSet]

@[simp] theorem setNoisyWitnessSet_other
    (witnessSet : ℕ → Finset α)
    {target i : ℕ} (value : Finset α) (hi : i ≠ target) :
    setNoisyWitnessSet witnessSet target value i =
      witnessSet i := by
  simp [setNoisyWitnessSet, hi]

/-- One complete outer iteration of the corrected Procedure 2. -/
noncomputable def extendNoisyProcedureStage
    (F : ℕ → Set α) (noise : ℕ → ℕ) {stage : ℕ}
    (current : NoisyProcedureStage F noise stage) :
    NoisyProcedureStage F noise (stage + 1) := by
  classical
  have hOldNodup : current.order.Nodup :=
    (current.order_perm.nodup_iff).mpr List.nodup_range
  have hTarget : stage ∉ current.order := by
    intro hMem
    have : stage ∈ List.range stage :=
      current.order_perm.mem_iff.mp hMem
    simp at this
  let split :
      NoisyInsertionSplit F noise current.complexity
        stage current.order :=
    Classical.choice
      (exists_noisyInsertionSplit
        F noise current.complexity stage current.order
        current.sorted hOldNodup)
  let newValue : ℕ :=
    noisyInsertionScore F noise split.left stage
  let newWitnessSet : Finset α :=
    totalNoisyStepSample F noise
      (noisyInsertionScope split.left stage) stage
  let newWitness : Finset ℕ :=
    totalNoisyStepWitness F noise
      (noisyInsertionScope split.left stage) stage
  let nextComplexity :=
    setComplexity current.complexity stage newValue
  let nextWitnessSet :=
    setNoisyWitnessSet current.witnessSet stage newWitnessSet
  let nextWitness :=
    setWitness current.witness stage newWitness
  refine {
    order := split.left ++ stage :: split.right
    complexity := nextComplexity
    witnessSet := nextWitnessSet
    witness := nextWitness
    order_perm := ?_
    sorted := ?_
    max_bounds := ?_
    complexity_eq_card := ?_
    witness_positive := ?_
    witness_noiseContained := ?_
    witness_other_lower := ?_
  }
  · have hPerm :
        (split.left ++ stage :: split.right).Perm
          (current.order ++ [stage]) :=
      split.newOrder_perm
    have hTail :
        (current.order ++ [stage]).Perm
          (List.range stage ++ [stage]) :=
      List.Perm.append_right [stage] current.order_perm
    simpa [List.range_succ] using hPerm.trans hTail
  · exact split.newOrder_pairwise current.sorted hTarget
  · exact split.orderArgmaxBounds
      hOldNodup hTarget current.max_bounds
  · intro i hiStage
    by_cases hi : i = stage
    · subst i
      simp [nextComplexity, nextWitnessSet, newWitnessSet,
        newValue, noisyInsertionScore, totalNoisyStepComplexity]
    · have hiOld : i < stage := by omega
      simpa [nextComplexity, nextWitnessSet,
        setComplexity, setNoisyWitnessSet, hi] using
        current.complexity_eq_card i hiOld
  · intro i hiStage hiPositive
    by_cases hi : i = stage
    · subst i
      have hiPositive' : 0 < newValue := by
        simpa [nextComplexity, setComplexity] using hiPositive
      have hCandidate :
          NoisyWitnessCandidate F noise
            (noisyInsertionScope split.left stage) stage
            newWitnessSet newWitness := by
        simpa [newValue, newWitnessSet, newWitness,
          noisyInsertionScore] using
          totalNoisyStep_positive_candidate F noise
            (noisyInsertionScope split.left stage) stage
            hiPositive'
      have hScope :
          noisyInsertionScope split.left stage ⊆
            Finset.range (stage + 1) := by
        intro j hj
        simp only [noisyInsertionScope, Finset.mem_insert,
          List.mem_toFinset] at hj
        rcases hj with rfl | hjLeft
        · simp
        · have hjOrder : j ∈ current.order := by
            rw [split.split]
            simp [hjLeft]
          have hjRange : j ∈ List.range stage :=
            current.order_perm.mem_iff.mp hjOrder
          exact Finset.mem_range.mpr
            (Nat.lt_succ_of_lt (List.mem_range.mp hjRange))
      simpa [nextWitnessSet, nextWitness,
        setNoisyWitnessSet, setWitness] using
        hCandidate.mono_scope hScope
    · have hiOld : i < stage := by omega
      have hiPositiveOld : 0 < current.complexity i := by
        simpa [nextComplexity, setComplexity, hi] using hiPositive
      simpa [nextComplexity, nextWitnessSet, nextWitness,
        setComplexity, setNoisyWitnessSet, setWitness, hi] using
        current.witness_positive i hiOld hiPositiveOld
  · intro i hiStage j hjWitness
    by_cases hi : i = stage
    · subst i
      have hjWitness' : j ∈ newWitness := by
        simpa [nextWitness, setWitness] using hjWitness
      by_cases hExists :
          ∃ sample,
            NoisyProcedureSampleCandidate F noise
              (noisyInsertionScope split.left stage) stage sample
      · have hSelected :=
          totalNoisyStepWitness_spec F noise
            (noisyInsertionScope split.left stage) stage hExists
        simpa [nextWitnessSet, setNoisyWitnessSet,
          newWitnessSet] using
          hSelected.2.2.2 j hjWitness'
      · have hNoSelected :
            ¬NoisyProcedureSampleCandidate F noise
              (noisyInsertionScope split.left stage) stage
              (totalNoisyStepSample F noise
                (noisyInsertionScope split.left stage) stage) := by
          intro hSelected
          exact hExists ⟨_, hSelected⟩
        have hEmpty : newWitness = ∅ := by
          simp [newWitness, totalNoisyStepWitness, hNoSelected]
        rw [hEmpty] at hjWitness'
        simp at hjWitness'
    · have hiOld : i < stage := by omega
      simpa [nextWitnessSet, nextWitness,
        setNoisyWitnessSet, setWitness, hi] using
        current.witness_noiseContained i hiOld j
          (by simpa [nextWitness, setWitness, hi] using hjWitness)
  · intro i hiStage j hjWitness hji
    by_cases hi : i = stage
    · subst i
      have hjWitness' : j ∈ newWitness := by
        simpa [nextWitness, setWitness] using hjWitness
      by_cases hExists :
          ∃ sample,
            NoisyProcedureSampleCandidate F noise
              (noisyInsertionScope split.left stage) stage sample
      · have hSelected :=
          totalNoisyStepWitness_spec F noise
            (noisyInsertionScope split.left stage) stage hExists
        have hjScope :
            j ∈ noisyInsertionScope split.left stage :=
          hSelected.1 hjWitness'
        have hjLeft : j ∈ split.left := by
          simpa [noisyInsertionScope, hji] using hjScope
        have hjOrder : j ∈ current.order := by
          rw [split.split]
          simp [hjLeft]
        have hjRange : j ∈ List.range stage :=
          current.order_perm.mem_iff.mp hjOrder
        have hjOld : j < stage := List.mem_range.mp hjRange
        constructor
        · exact hjOld
        · change nextComplexity j < nextComplexity stage
          simpa [nextComplexity, newValue, setComplexity,
            hji] using split.left_lower j hjLeft
      · have hEmpty : newWitness = ∅ := by
          have hNoSelected :
              ¬NoisyProcedureSampleCandidate F noise
                (noisyInsertionScope split.left stage) stage
                (totalNoisyStepSample F noise
                  (noisyInsertionScope split.left stage) stage) := by
            intro hSelected
            exact hExists ⟨_, hSelected⟩
          simp [newWitness, totalNoisyStepWitness, hNoSelected]
        rw [hEmpty] at hjWitness'
        simp at hjWitness'
    · have hiOld : i < stage := by omega
      have hOld :=
        current.witness_other_lower i hiOld j
          (by simpa [nextWitness, setWitness, hi] using hjWitness)
          hji
      have hj : j ≠ stage := by omega
      constructor
      · exact hOld.1
      · simpa [nextComplexity, setComplexity, hi, hj] using hOld.2

/-- The total corrected finite execution of Procedure 2. -/
noncomputable def canonicalNoisyProcedureStage
    (F : ℕ → Set α) (noise : ℕ → ℕ) :
    (stage : ℕ) → NoisyProcedureStage F noise stage
  | 0 => {
      order := []
      complexity := fun _ => 0
      witnessSet := fun _ => ∅
      witness := fun _ => ∅
      order_perm := by simp
      sorted := by simp
      max_bounds := by
        intro before i after h
        simp at h
      complexity_eq_card := by omega
      witness_positive := by omega
      witness_noiseContained := by omega
      witness_other_lower := by omega
    }
  | stage + 1 =>
      extendNoisyProcedureStage F noise
        (canonicalNoisyProcedureStage F noise stage)

theorem extendNoisyProcedureStage_complexity_old
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    {stage i : ℕ}
    (current : NoisyProcedureStage F noise stage)
    (hi : i < stage) :
    (extendNoisyProcedureStage F noise current).complexity i =
      current.complexity i := by
  classical
  simp [extendNoisyProcedureStage, setComplexity,
    Nat.ne_of_lt hi]

/-- The permanent repaired Procedure-2 complexity of one flattened
diagonal coordinate. -/
noncomputable def canonicalNoisyComplexity
    (F : ℕ → Set α) (noise : ℕ → ℕ) (coordinate : ℕ) : ℕ :=
  (canonicalNoisyProcedureStage F noise (coordinate + 1)).complexity
    coordinate

noncomputable def canonicalNoisyWitnessSet
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (coordinate : ℕ) : Finset α :=
  (canonicalNoisyProcedureStage F noise (coordinate + 1)).witnessSet
    coordinate

noncomputable def canonicalNoisyWitness
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (coordinate : ℕ) : Finset ℕ :=
  (canonicalNoisyProcedureStage F noise (coordinate + 1)).witness
    coordinate

theorem canonicalNoisyProcedureStage_complexity_stable
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    {stage coordinate : ℕ} (hCoordinate : coordinate < stage) :
    (canonicalNoisyProcedureStage F noise stage).complexity coordinate =
      canonicalNoisyComplexity F noise coordinate := by
  induction stage with
  | zero => omega
  | succ stage ih =>
      by_cases hEq : coordinate = stage
      · subst coordinate
        rfl
      · have hOld : coordinate < stage := by omega
        calc
          (canonicalNoisyProcedureStage
              F noise (Nat.succ stage)).complexity coordinate =
              (canonicalNoisyProcedureStage
                F noise stage).complexity coordinate := by
                  rw [canonicalNoisyProcedureStage]
                  exact extendNoisyProcedureStage_complexity_old
                    F noise
                    (canonicalNoisyProcedureStage F noise stage)
                    hOld
          _ = canonicalNoisyComplexity F noise coordinate :=
            ih hOld

/-- At the defective printed initialization, the corrected procedure takes
the explicit empty/zero branch. -/
theorem corrected_procedure_2_first_step_zero
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (hInfinite : (F 0).Infinite) :
    totalNoisyStepComplexity F noise {0} 0 = 0 := by
  apply totalNoisyStepComplexity_eq_zero_of_no_candidate
  exact procedure_2_first_step_has_no_candidate
    F noise 0 hInfinite

/-- The total recursive execution supplies all finite witness data required
by Claim B.2.  The empty fallback is harmless: the certificate only asks
for a genuine candidate when its canonical complexity is positive. -/
noncomputable def canonicalNoisyWitnessCertificate
    (F : ℕ → Set α) (noise : ℕ → ℕ) :
    NoisyProcedureWitnessCertificate F noise
      (canonicalNoisyComplexity F noise) := by
  classical
  refine {
    witness := canonicalNoisyWitness F noise
    witnessSet := canonicalNoisyWitnessSet F noise
    complexity_eq_card := ?_
    self_mem := ?_
    core_finite := ?_
    witnessSet_noiseContained := ?_
    other_earlier := ?_
    other_lower := ?_
  }
  · intro coordinate
    let current :=
      canonicalNoisyProcedureStage F noise (coordinate + 1)
    simpa [current, canonicalNoisyComplexity,
      canonicalNoisyWitnessSet] using
      current.complexity_eq_card coordinate (by omega)
  · intro coordinate hPositive
    let current :=
      canonicalNoisyProcedureStage F noise (coordinate + 1)
    have hStored :=
      current.witness_positive coordinate (by omega)
        (by simpa [current, canonicalNoisyComplexity] using hPositive)
    simpa [current, canonicalNoisyWitness] using hStored.2.1
  · intro coordinate hPositive
    let current :=
      canonicalNoisyProcedureStage F noise (coordinate + 1)
    have hStored :=
      current.witness_positive coordinate (by omega)
        (by simpa [current, canonicalNoisyComplexity] using hPositive)
    simpa [current, canonicalNoisyWitness] using hStored.2.2.1
  · intro coordinate other hOther
    let current :=
      canonicalNoisyProcedureStage F noise (coordinate + 1)
    simpa [current, canonicalNoisyWitness,
      canonicalNoisyWitnessSet] using
      current.witness_noiseContained coordinate (by omega)
        other
        (by simpa [current, canonicalNoisyWitness] using hOther)
  · intro coordinate other hOther hNe
    let current :=
      canonicalNoisyProcedureStage F noise (coordinate + 1)
    exact
      (current.witness_other_lower coordinate (by omega) other
        (by simpa [current, canonicalNoisyWitness] using hOther) hNe).1
  · intro coordinate other hOther hNe
    let current :=
      canonicalNoisyProcedureStage F noise (coordinate + 1)
    have hLower :=
      current.witness_other_lower coordinate (by omega) other
        (by simpa [current, canonicalNoisyWitness] using hOther) hNe
    have hOtherStable :
        current.complexity other =
          canonicalNoisyComplexity F noise other :=
      canonicalNoisyProcedureStage_complexity_stable
        F noise (hLower.1.trans (by omega))
    simpa [current, canonicalNoisyComplexity, hOtherStable] using
      hLower.2

/-- Claim B.2 is no longer conditional on an externally supplied
Procedure-2 certificate: the corrected recursive execution constructs it. -/
theorem corrected_procedure_2_claim_B_2
    (F : ℕ → Set α) (noise : ℕ → ℕ) :
    EarlierTradeoff
      (fun coordinate =>
        canonicalNoisyComplexity F noise coordinate + 1)
      (NoisyRealizableTimeVectors F noise) :=
  claim_B_2_noisyWitness_earlierTradeoff
    (canonicalNoisyWitnessCertificate F noise)

theorem corrected_procedure_2_paretoOptimal
    (F : ℕ → Set α) (noise : ℕ → ℕ) :
    ParetoOptimal (NoisyRealizableTimeVectors F noise)
      (fun coordinate =>
        canonicalNoisyComplexity F noise coordinate + 1) :=
  claim_B_2_noisyWitness_paretoOptimal
    (canonicalNoisyWitnessCertificate F noise)

/-! ## The deterministic noisy scan in Theorem 6 -/

/-- The noisy acceptance test supplied to the common greedy-scan kernel. -/
def noisyGreedyAccept
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (coordinate : ℕ) : Prop :=
  NoiseContainedAt F noise coordinate sample ∧
    (indexedIntersection F
      (insert coordinate selected)).Infinite

/-- One source-aligned noisy greedy scan step. -/
noncomputable abbrev noisyGreedyStep
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (coordinate : ℕ) : Finset ℕ :=
  greedyListStepBy (noisyGreedyAccept F noise sample)
    selected coordinate

noncomputable abbrev noisyGreedyScan
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) :
    Finset ℕ → List ℕ → Finset ℕ :=
  greedyListScanBy (noisyGreedyAccept F noise sample)

theorem noisyGreedyScan_append
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (first second : List ℕ) :
    noisyGreedyScan F noise sample selected (first ++ second) =
      noisyGreedyScan F noise sample
        (noisyGreedyScan F noise sample selected first) second :=
  greedyListScanBy_append
    (noisyGreedyAccept F noise sample) selected first second

theorem noisyGreedyStep_subset
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (coordinate : ℕ) :
    selected ⊆
      noisyGreedyStep F noise sample selected coordinate :=
  greedyListStepBy_subset
    (noisyGreedyAccept F noise sample) selected coordinate

theorem noisyGreedyScan_initial_subset
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (order : List ℕ) :
    selected ⊆ noisyGreedyScan F noise sample selected order :=
  greedyListScanBy_initial_subset
    (noisyGreedyAccept F noise sample) selected order

theorem noisyGreedyStep_subset_union
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (coordinate : ℕ) :
    noisyGreedyStep F noise sample selected coordinate ⊆
      insert coordinate selected :=
  greedyListStepBy_subset_insert
    (noisyGreedyAccept F noise sample) selected coordinate

theorem noisyGreedyScan_subset_union
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (order : List ℕ) :
    noisyGreedyScan F noise sample selected order ⊆
      selected ∪ order.toFinset :=
  greedyListScanBy_subset_union
    (noisyGreedyAccept F noise sample) selected order

theorem noisyGreedyStep_noiseContained
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (coordinate : ℕ)
    (hSelected :
      ∀ j ∈ selected,
        NoiseContainedAt F noise j sample) :
    ∀ j ∈ noisyGreedyStep F noise sample selected coordinate,
      NoiseContainedAt F noise j sample := by
  classical
  simp only [noisyGreedyStep, greedyListStepBy, noisyGreedyAccept]
  split
  next hPass =>
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjSelected
    · exact hPass.1
    · exact hSelected j hjSelected
  next =>
    exact hSelected

theorem noisyGreedyScan_noiseContained
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (order : List ℕ)
    (hSelected :
      ∀ j ∈ selected,
        NoiseContainedAt F noise j sample) :
    ∀ j ∈ noisyGreedyScan F noise sample selected order,
      NoiseContainedAt F noise j sample := by
  apply greedyListScanBy_invariant
    (noisyGreedyAccept F noise sample)
    (fun current =>
      ∀ j ∈ current, NoiseContainedAt F noise j sample)
    ?_ hSelected
  intro current coordinate hCurrent
  exact noisyGreedyStep_noiseContained
    F noise sample current coordinate hCurrent

theorem noisyGreedyScan_core_infinite
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α) (selected : Finset ℕ)
    (order : List ℕ)
    (hInfinite :
      (indexedIntersection F selected).Infinite) :
    (indexedIntersection F
      (noisyGreedyScan F noise sample selected order)).Infinite := by
  classical
  apply greedyListScanBy_invariant
    (noisyGreedyAccept F noise sample)
    (fun current => (indexedIntersection F current).Infinite)
    ?_ hInfinite
  intro current coordinate hCurrent
  simp only [greedyListStepBy, noisyGreedyAccept]
  split
  next hPass => exact hPass.2
  next => exact hCurrent

/-- The exact target-selection argument in Theorem 6, now instantiated
against the corrected stage-wide Claim B.3 invariant. -/
theorem target_selected_in_noisyGreedyScan
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (sample : Finset α)
    {order before after : List ℕ}
    {target bound : ℕ}
    (hOrder : order = before ++ target :: after)
    (hArgmax :
      NoisyArgmaxBound F noise
        (insert target before.toFinset) target bound)
    (hTargetNoise :
      NoiseContainedAt F noise target sample)
    (hLarge : bound < sample.card) :
    target ∈
      noisyGreedyScan F noise sample ∅ order := by
  classical
  let selectedBefore :=
    noisyGreedyScan F noise sample ∅ before
  have hSelectedSubset :
      selectedBefore ⊆ before.toFinset := by
    have h :=
      noisyGreedyScan_subset_union
        F noise sample ∅ before
    simpa [selectedBefore] using h
  have hSelectedNoise :
      ∀ coordinate ∈ selectedBefore,
        NoiseContainedAt F noise coordinate sample := by
    apply noisyGreedyScan_noiseContained
    simp
  have hInfinite :
      (indexedIntersection F
        (insert target selectedBefore)).Infinite :=
    theorem_6_target_passes_infiniteIntersection_check
      (F := F) (noise := noise)
      (scopeSet := insert target before.toFinset)
      (selected := selectedBefore)
      (target := target) (complexity := bound)
      (sample := sample)
      (Finset.mem_insert_self target before.toFinset)
      (fun coordinate hcoordinate =>
        Finset.mem_insert_of_mem
          (hSelectedSubset hcoordinate))
      hTargetNoise hSelectedNoise hArgmax hLarge
  rw [hOrder, noisyGreedyScan_append]
  change target ∈
    noisyGreedyScan F noise sample selectedBefore
      (target :: after)
  simp only [noisyGreedyScan, greedyListScanBy, greedyListStepBy,
    noisyGreedyAccept]
  rw [if_pos ⟨hTargetNoise, hInfinite⟩]
  exact
    noisyGreedyScan_initial_subset F noise sample
      (insert target selectedBefore) after
      (Finset.mem_insert_self target selectedBefore)

/-! ## Scheduler-driven deterministic Theorem 6 -/

noncomputable def noisySchedulerTimeVector
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f) :
    TimeVector :=
  fun coordinate =>
    max (schedulerEntryTime f hf coordinate)
      (canonicalNoisyComplexity F noise coordinate + 1)

theorem noisySchedulerTimeVector_positive
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f) :
    PositiveTimeVector
      (noisySchedulerTimeVector F noise f hf) := by
  intro coordinate
  exact le_trans (by omega)
    (Nat.le_max_right _ _)

noncomputable def noisySchedulerScanOrder
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) (t : ℕ) : List ℕ :=
  (canonicalNoisyProcedureStage F noise (f t)).order

/-- The literal finite-prefix scan and fresh common-core output of Theorem
6, instantiated with the corrected Procedure-2 stages. -/
noncomputable def noisySchedulerGenerator
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) : HistoryGenerator α := by
  classical
  exact fun _ xs =>
    let sample := GenLimit.Generic.sequenceSample xs
    let selected :=
      noisyGreedyScan F noise sample ∅
        (noisySchedulerScanOrder F noise f sample.card)
    GenLimit.Support.freshFromInfinite
      (indexedIntersection F selected)
      (noisyGreedyScan_core_infinite
        F noise sample ∅
        (noisySchedulerScanOrder F noise f sample.card)
        (by simpa using
          (Set.infinite_univ : (Set.univ : Set α).Infinite)))
      sample

theorem noisySchedulerGenerator_spec
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) {t : ℕ} (xs : Fin t → α) :
    noisySchedulerGenerator F noise f t xs ∈
        indexedIntersection F
          (noisyGreedyScan F noise
            (GenLimit.Generic.sequenceSample xs) ∅
            (noisySchedulerScanOrder F noise f
              (GenLimit.Generic.sequenceSample xs).card)) ∧
      noisySchedulerGenerator F noise f t xs ∉
        GenLimit.Generic.sequenceSample xs := by
  classical
  simp only [noisySchedulerGenerator]
  exact ⟨GenLimit.Support.freshFromInfinite_mem _ _ _,
    GenLimit.Support.freshFromInfinite_not_mem _ _ _⟩

theorem noisySchedulerGenerator_correct
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f)
    {coordinate t : ℕ} (xs : Fin t → α)
    (hThreshold :
      noisySchedulerTimeVector F noise f hf coordinate ≤ t)
    (hInjective : Function.Injective xs)
    (hTargetNoise :
      NoiseContainedAt F noise coordinate
        (GenLimit.Generic.sequenceSample xs)) :
    noisySchedulerGenerator F noise f t xs ∈ F coordinate ∧
      ∀ k, noisySchedulerGenerator F noise f t xs ≠ xs k := by
  classical
  let sample := GenLimit.Generic.sequenceSample xs
  have hSampleCard : sample.card = t :=
    GenLimit.Generic.sequenceSample_card_of_injective xs hInjective
  have hEntry :
      schedulerEntryTime f hf coordinate ≤ t :=
    (Nat.le_max_left _ _).trans hThreshold
  have hCoordinateScope : coordinate < f t :=
    (schedulerEntryTime_le_iff f hf).mp hEntry
  let current :=
    canonicalNoisyProcedureStage F noise (f t)
  have hCoordinateOrder : coordinate ∈ current.order := by
    apply current.order_perm.mem_iff.mpr
    exact List.mem_range.mpr hCoordinateScope
  obtain ⟨before, after, hOrder⟩ :=
    List.mem_iff_append.mp hCoordinateOrder
  have hScanOrder :
      noisySchedulerScanOrder F noise f sample.card =
        before ++ coordinate :: after := by
    rw [hSampleCard]
    simpa [noisySchedulerScanOrder, current] using hOrder
  have hComplexity :
      current.complexity coordinate =
        canonicalNoisyComplexity F noise coordinate :=
    canonicalNoisyProcedureStage_complexity_stable
      F noise hCoordinateScope
  have hCard :
      canonicalNoisyComplexity F noise coordinate <
        sample.card := by
    have hBound :
        canonicalNoisyComplexity F noise coordinate + 1 ≤ t :=
      (Nat.le_max_right _ _).trans hThreshold
    omega
  have hSelected :
      coordinate ∈
        noisyGreedyScan F noise sample ∅
          (noisySchedulerScanOrder F noise f sample.card) := by
    exact target_selected_in_noisyGreedyScan
      F noise sample hScanOrder
      (by simpa [hComplexity] using
        current.max_bounds before coordinate after hOrder)
      hTargetNoise hCard
  have hSpec :=
    noisySchedulerGenerator_spec F noise f xs
  constructor
  · exact hSpec.1 coordinate hSelected
  · intro k hk
    exact hSpec.2
      (GenLimit.Generic.mem_sequenceSample_iff.mpr
        ⟨k, hk.symm⟩)

/-- Corrected deterministic Theorem 6 at the established finite,
injective-history noisy semantics.  The source initialization repair is
part of the construction, not an unstated assumption. -/
theorem theorem_6_corrected_totalized
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f) :
    AchievesNoisyTimeVector
        (noisySchedulerGenerator F noise f)
        F noise
        (noisySchedulerTimeVector F noise f hf) ∧
      PositiveTimeVector
        (noisySchedulerTimeVector F noise f hf) := by
  constructor
  · intro coordinate t xs hTime hInjective hTargetNoise
    exact noisySchedulerGenerator_correct
      F noise f hf xs hTime hInjective hTargetNoise
  · exact noisySchedulerTimeVector_positive F noise f hf

theorem theorem_6_corrected_timeVector_realizable
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f) :
    noisySchedulerTimeVector F noise f hf ∈
      NoisyRealizableTimeVectors F noise :=
  ⟨noisySchedulerGenerator F noise f,
    (theorem_6_corrected_totalized F noise f hf).1,
    (theorem_6_corrected_totalized F noise f hf).2⟩

/-- The corrected Procedure 2 and deterministic Theorem 6 discharge both
obligations expected by the common exact-Pareto scheduler endgame. -/
noncomputable def corrected_noisy_variantCertificate
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ) :
    VariantSchedulerCertificate
      (NoisyRealizableTimeVectors F noise)
      (canonicalNoisyComplexity F noise) where
  scheduler_realizable := by
    intro f hf
    exact theorem_6_corrected_timeVector_realizable
      F noise f hf
  canonical_tradeoff :=
    corrected_procedure_2_claim_B_2 F noise

/-- Consequently, the finite-sublevel hypothesis of Theorem 8 yields the
exact canonical noisy Pareto vector without any remaining deterministic
Procedure-2 assumption. -/
theorem theorem_8_corrected_deterministic_endgame
    [Infinite α]
    (F : ℕ → Set α) (noise : ℕ → ℕ)
    (hFinite :
      FiniteSublevels (canonicalNoisyComplexity F noise)) :
    variantCanonicalTime
        (canonicalNoisyComplexity F noise) ∈
          NoisyRealizableTimeVectors F noise ∧
      ParetoOptimal (NoisyRealizableTimeVectors F noise)
        (variantCanonicalTime
          (canonicalNoisyComplexity F noise)) :=
  theorem_8_noisy_exactPareto_endgame
    (corrected_noisy_variantCertificate F noise) hFinite

end GenLimit.ParetoGeneration
