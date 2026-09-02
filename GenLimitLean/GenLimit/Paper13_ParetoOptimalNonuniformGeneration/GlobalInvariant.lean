import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.WitnessLowerBound
import GenLimit.Support.Fresh
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Pairwise

/-!
# The global insertion invariant for Pareto generation

This file formalizes the recursive invariant behind Procedure 1 and
Claim 3.2 of Charikar--Pabbaraju,
*Pareto-optimal Non-uniform Language Generation*, arXiv:2510.02795v1.

There is a zero-cardinality edge case in the literal statement of Claim 3.2.
If `C(L_i)` was set to the empty collection because no finite-intersection
candidate existed when `L_i` was inserted, a later disjoint language can
create a candidate of score zero.  The old empty collection is not itself a
candidate (it does not contain `L_i`), so it cannot literally belong to the
displayed arg max.  What the proof and Theorem 4 actually use is the
max-value invariant: every later candidate has score at most `m*(L_i)`.

The lemmas below prove that corrected invariant, including its iteration
through an arbitrary finite list of insertions.  They also isolate the
insertion split produced by the source's right-to-left while loop.
-/

namespace GenLimit.ParetoGeneration

/-- The max-value form of Claim 3.2.  Unlike literal arg-max membership, this
is meaningful even when the stored witness is empty and the maximum is zero.
-/
def MaxScoreBound
    (F : Nat -> Set α) (scopeSet : Finset Nat)
    (target bound : Nat) : Prop :=
  forall witness,
    FiniteIntersectionCandidate F scopeSet target witness ->
      finiteIntersectionScore F witness <= bound

/-- Enlarging the available scope preserves every old candidate. -/
theorem finiteIntersectionCandidate_mono_scope
    (F : Nat -> Set α) {small large : Finset Nat}
    {target : Nat} {witness : Finset Nat}
    (hscope : small ⊆ large)
    (h :
      FiniteIntersectionCandidate F small target witness) :
    FiniteIntersectionCandidate F large target witness :=
  ⟨h.1.trans hscope, h.2⟩

/-- `procedureStepComplexity` is the maximum candidate score, with zero as
the value of the empty search space.
-/
theorem finiteIntersectionScore_le_procedureStepComplexity
    (F : Nat -> Set α) (scopeSet : Finset Nat)
    (target : Nat) {witness : Finset Nat}
    (h :
      FiniteIntersectionCandidate F scopeSet target witness) :
    finiteIntersectionScore F witness <=
      procedureStepComplexity F scopeSet target := by
  classical
  have hexists :
      ∃ candidate,
        FiniteIntersectionCandidate F scopeSet target candidate :=
    ⟨witness, h⟩
  rw [procedureStepComplexity_eq_score F scopeSet target hexists]
  exact (procedureStepWitness_spec F scopeSet target hexists).2 witness h

/-- The Step-(b.i) maximum is monotone under enlargement of the finite
language scope.
-/
theorem procedureStepComplexity_mono
    (F : Nat -> Set α) {small large : Finset Nat}
    (target : Nat) (hscope : small ⊆ large) :
    procedureStepComplexity F small target <=
      procedureStepComplexity F large target := by
  classical
  by_cases hsmall :
      ∃ witness,
        FiniteIntersectionCandidate F small target witness
  · have hlarge :
        ∃ witness,
          FiniteIntersectionCandidate F large target witness := by
      obtain ⟨witness, hwitness⟩ := hsmall
      exact ⟨witness,
        finiteIntersectionCandidate_mono_scope F hscope hwitness⟩
    rw [procedureStepComplexity_eq_score F small target hsmall]
    exact finiteIntersectionScore_le_procedureStepComplexity
      F large target
      (finiteIntersectionCandidate_mono_scope F hscope
        (procedureStepWitness_spec F small target hsmall).1)
  · rw [procedureStepComplexity_eq_zero F small target hsmall]
    exact Nat.zero_le _

/-- At its insertion stage, the selected maximum always satisfies the
corrected max-value invariant.
-/
theorem procedureStep_maxScoreBound
    (F : Nat -> Set α) (scopeSet : Finset Nat)
    (target : Nat) :
    MaxScoreBound F scopeSet target
      (procedureStepComplexity F scopeSet target) := by
  intro witness hwitness
  exact finiteIntersectionScore_le_procedureStepComplexity
    F scopeSet target hwitness

/-- One crossing step in Claim 3.2.

An old target has a score bound in `scopeSet`.  The newly inserted language
is allowed into the old target's scope only after the new language's own
maximum in that enlarged scope was found to be no larger than the old bound.
Every genuinely new old-target candidate contains the new language and is
therefore also a candidate for it.
-/
theorem maxScoreBound_persists_insert
    (F : Nat -> Set α) {scopeSet : Finset Nat}
    {target newIndex bound : Nat}
    (hOld : MaxScoreBound F scopeSet target bound)
    (hCross :
      procedureStepComplexity F (insert newIndex scopeSet) newIndex <=
        bound) :
    MaxScoreBound F (insert newIndex scopeSet) target bound := by
  classical
  intro witness hWitness
  by_cases hnew : newIndex ∈ witness
  · exact (finiteIntersectionScore_le_procedureStepComplexity
      F (insert newIndex scopeSet) newIndex
      ⟨hWitness.1, hnew, hWitness.2.2⟩).trans hCross
  · apply hOld witness
    refine ⟨?_, hWitness.2⟩
    intro j hj
    rcases Finset.mem_insert.mp (hWitness.1 hj) with rfl | hjold
    · exact (hnew hj).elim
    · exact hjold

/-- The corrected max-value invariant iterated through a finite list of
crossings.  `scopes k` is the scope immediately before crossing `newIndices
[k]`; the two equalities make the recursion source-facing rather than
silently replacing Procedure 1 by a bulk union.
-/
theorem maxScoreBound_persists_insertions
    (F : Nat -> Set α) {target bound : Nat}
    (newIndices : List Nat) (scopes : Nat -> Finset Nat)
    (hzero : MaxScoreBound F (scopes 0) target bound)
    (hstep :
      forall k, k < newIndices.length ->
        scopes (k + 1) =
            insert (newIndices.getD k 0) (scopes k) ∧
        procedureStepComplexity F (scopes (k + 1))
          (newIndices.getD k 0) <= bound) :
    MaxScoreBound F (scopes newIndices.length) target bound := by
  induction newIndices generalizing scopes with
  | nil => simpa using hzero
  | cons newIndex tail ih =>
      have hfirst := hstep 0 (by simp)
      have hafter :
          MaxScoreBound F (scopes 1) target bound := by
        rw [hfirst.1]
        exact maxScoreBound_persists_insert F hzero
          (by simpa [hfirst.1] using hfirst.2)
      let shiftedScopes : Nat -> Finset Nat := fun k => scopes (k + 1)
      have htail :
          forall k, k < tail.length ->
            shiftedScopes (k + 1) =
                insert (tail.getD k 0) (shiftedScopes k) ∧
              procedureStepComplexity F (shiftedScopes (k + 1))
                (tail.getD k 0) <= bound := by
        intro k hk
        simpa [shiftedScopes, Nat.add_assoc] using
          hstep (k + 1) (by simpa using Nat.succ_lt_succ hk)
      have := ih shiftedScopes hafter htail
      simpa [shiftedScopes, Nat.add_assoc] using this

/-! ## The insertion split -/

/-- Scope used when the new target currently sits just after `left`. -/
def insertionScope (left : List Nat) (target : Nat) : Finset Nat :=
  insert target left.toFinset

/-- The current `m_check` value in the insertion loop. -/
noncomputable def insertionScore
    (F : Nat -> Set α) (left : List Nat) (target : Nat) : Nat :=
  procedureStepComplexity F (insertionScope left target) target

/-- A completed right-to-left insertion loop.

`oldOrder = left ++ right`; the target is inserted between these lists.
Every language left of the target has strictly smaller finalized
complexity.  Every language crossed into `right` records the exact comparison
that justified its swap.
-/
structure InsertionSplit
    (F : Nat -> Set α) (complexity : Nat -> Nat)
    (target : Nat) (oldOrder : List Nat) where
  left : List Nat
  right : List Nat
  split : oldOrder = left ++ right
  left_lower :
    forall i, i ∈ left ->
      complexity i < insertionScore F left target
  crossed_upper :
    forall before i after,
      right = before ++ i :: after ->
        insertionScore F (left ++ before ++ [i]) target <=
          complexity i

/-- In a list without duplicates, the prefix ending immediately before a
specified occurrence is unique. -/
theorem prefix_eq_of_nodup_decompositions
    {whole before₁ before₂ after₁ after₂ : List Nat} {i : Nat}
    (hNodup : whole.Nodup)
    (h₁ : whole = before₁ ++ i :: after₁)
    (h₂ : whole = before₂ ++ i :: after₂) :
    before₁ = before₂ := by
  have hNodup₁ :
      (before₁ ++ i :: after₁).Nodup := h₁ ▸ hNodup
  have hNodup₂ :
      (before₂ ++ i :: after₂).Nodup := h₂ ▸ hNodup
  have hi₁ : i ∉ before₁ := by
    have hcross := (List.nodup_append.mp hNodup₁).2.2
    intro hi
    exact hcross i hi i (by simp) rfl
  have hi₂ : i ∉ before₂ := by
    have hcross := (List.nodup_append.mp hNodup₂).2.2
    intro hi
    exact hcross i hi i (by simp) rfl
  have hidx₁ : whole.idxOf i = before₁.length := by
    rw [h₁, List.idxOf_append_of_notMem hi₁]
    simp
  have hidx₂ : whole.idxOf i = before₂.length := by
    rw [h₂, List.idxOf_append_of_notMem hi₂]
    simp
  have hlength : before₁.length = before₂.length :=
    hidx₁.symm.trans hidx₂
  exact List.append_inj_left
    (show before₁ ++ (i :: after₁) =
        before₂ ++ (i :: after₂) from h₁.symm.trans h₂)
    hlength

/-- Procedure 1's while loop always produces an insertion split.  The proof
is reverse induction on the old ordering, exactly matching a right-to-left
insertion-sort pass.
-/
theorem exists_insertionSplit
    (F : Nat -> Set α) (complexity : Nat -> Nat)
    (target : Nat) (oldOrder : List Nat)
    (hSorted :
      oldOrder.Pairwise (fun i j => complexity i <= complexity j))
    (hNodup : oldOrder.Nodup) :
    Nonempty (InsertionSplit F complexity target oldOrder) := by
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
      by_cases hstop :
          complexity last <
            insertionScore F (oldOrder ++ [last]) target
      · refine ⟨{
          left := oldOrder ++ [last]
          right := []
          split := by simp
          left_lower := ?_
          crossed_upper := by simp
        }⟩
        intro i hi
        have hle : complexity i <= complexity last := by
          have hpairs := (List.pairwise_append.mp hSorted).2.2
          rcases List.mem_append.mp hi with hiold | hilast
          · exact hpairs i hiold last (by simp)
          · have hilast' : i = last := by simpa using hilast
            subst i
            exact Nat.le_refl _
        exact hle.trans_lt hstop
      · have hOldSorted :
            oldOrder.Pairwise
              (fun i j => complexity i <= complexity j) :=
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
        · intro before i after hdecomp
          have hwholeEq :
              oldOrder ++ [last] =
                prior.left ++ (prior.right ++ [last]) := by
            calc
              oldOrder ++ [last] =
                  (prior.left ++ prior.right) ++ [last] :=
                congrArg (fun xs => xs ++ [last]) prior.split
              _ = prior.left ++ (prior.right ++ [last]) := by
                simp [List.append_assoc]
          have hrightNodup :
              (prior.right ++ [last]).Nodup := by
            have hwholeNodup :
                (prior.left ++ (prior.right ++ [last])).Nodup := by
              exact hwholeEq ▸ hNodup
            exact hwholeNodup.of_append_right
          by_cases hi : i = last
          · subst i
            have hbefore : before = prior.right :=
              prefix_eq_of_nodup_decompositions
                (before₂ := prior.right) (after₂ := [])
                hrightNodup hdecomp (by rfl)
            subst before
            rw [← prior.split]
            exact Nat.le_of_not_gt hstop
          · have hiRight : i ∈ prior.right := by
              have : i ∈ prior.right ++ [last] := by
                rw [hdecomp]
                simp
              simpa [hi] using this
            obtain ⟨priorBefore, priorAfter, hpriorDecomp⟩ :=
              (List.mem_iff_append.mp hiRight)
            have hcanonical :
                prior.right ++ [last] =
                  priorBefore ++ i :: (priorAfter ++ [last]) := by
              rw [hpriorDecomp]
              simp [List.append_assoc]
            have hbefore : before = priorBefore :=
              prefix_eq_of_nodup_decompositions hrightNodup
                hdecomp hcanonical
            subst before
            exact prior.crossed_upper priorBefore i priorAfter
              hpriorDecomp

theorem insertionScope_mono
    {small large : List Nat} {target : Nat}
    (hsub : forall i, i ∈ small -> i ∈ large) :
    insertionScope small target ⊆ insertionScope large target := by
  classical
  intro i hi
  simp only [insertionScope, Finset.mem_insert,
    List.mem_toFinset] at hi ⊢
  exact hi.elim Or.inl (fun h => Or.inr (hsub i h))

/-- Moving the target farther left can only decrease its Step-(b.i) score. -/
theorem insertionScore_mono
    (F : Nat -> Set α) {small large : List Nat} (target : Nat)
    (hsub : forall i, i ∈ small -> i ∈ large) :
    insertionScore F small target <= insertionScore F large target := by
  exact procedureStepComplexity_mono F target
    (insertionScope_mono hsub)

/-- Every language crossed by an insertion has finalized complexity at least
the new target's final complexity.
-/
theorem InsertionSplit.right_upper
    {F : Nat -> Set α} {complexity : Nat -> Nat}
    {target : Nat} {oldOrder : List Nat}
    (split : InsertionSplit F complexity target oldOrder)
    {i : Nat} (hi : i ∈ split.right) :
    insertionScore F split.left target <= complexity i := by
  obtain ⟨before, after, hdecomp⟩ :=
    List.mem_iff_append.mp hi
  have hmono :
      insertionScore F split.left target <=
        insertionScore F
          (split.left ++ before ++ [i]) target := by
    apply insertionScore_mono F target
    intro j hj
    simp only [List.mem_append, List.mem_singleton]
    exact Or.inl (Or.inl hj)
  exact hmono.trans
    (split.crossed_upper before i after hdecomp)

/-! ## Stage-wide max bounds -/

/-- Replace the complexity of the newly inserted target and leave every old
coordinate unchanged.
-/
def setComplexity
    (complexity : Nat -> Nat) (target value : Nat) : Nat -> Nat :=
  fun i => if i = target then value else complexity i

@[simp] theorem setComplexity_same
    (complexity : Nat -> Nat) (target value : Nat) :
    setComplexity complexity target value target = value := by
  simp [setComplexity]

@[simp] theorem setComplexity_other
    (complexity : Nat -> Nat) {target value i : Nat}
    (hi : i ≠ target) :
    setComplexity complexity target value i = complexity i := by
  simp [setComplexity, hi]

/-- Corrected Claim 3.2 simultaneously for every language in an ordering. -/
def OrderMaxScoreBounds
    (F : Nat -> Set α) (order : List Nat)
    (complexity : Nat -> Nat) : Prop :=
  forall before i after,
    order = before ++ i :: after ->
      MaxScoreBound F (insert i before.toFinset) i (complexity i)

/-- One complete insertion-sort pass preserves the corrected Claim 3.2
invariant for every old language and establishes it for the new target.
-/
theorem InsertionSplit.orderMaxScoreBounds
    {F : Nat -> Set α} {complexity : Nat -> Nat}
    {target : Nat} {oldOrder : List Nat}
    (split : InsertionSplit F complexity target oldOrder)
    (hOldNodup : oldOrder.Nodup)
    (htarget : target ∉ oldOrder)
    (hOld : OrderMaxScoreBounds F oldOrder complexity) :
    OrderMaxScoreBounds F
      (split.left ++ target :: split.right)
      (setComplexity complexity target
        (insertionScore F split.left target)) := by
  classical
  have hNewNodup :
      (split.left ++ target :: split.right).Nodup := by
    rw [List.nodup_middle]
    have : (target :: oldOrder).Nodup :=
      List.nodup_cons.mpr ⟨htarget, hOldNodup⟩
    simpa [split.split] using this
  intro before i after hdecomp
  by_cases hitarget : i = target
  · subst i
    have hbefore : before = split.left :=
      prefix_eq_of_nodup_decompositions hNewNodup hdecomp rfl
    subst before
    simpa [insertionScore, insertionScope] using
      procedureStep_maxScoreBound F
        (insertionScope split.left target) target
  · have hiMem :
        i ∈ split.left ++ target :: split.right := by
      rw [hdecomp]
      simp
    have hiSides : i ∈ split.left ∨ i ∈ split.right := by
      simpa [hitarget] using hiMem
    rcases hiSides with hiLeft | hiRight
    · obtain ⟨leftBefore, leftAfter, hleftDecomp⟩ :=
        List.mem_iff_append.mp hiLeft
      have hcanonical :
          split.left ++ target :: split.right =
            leftBefore ++ i ::
              (leftAfter ++ target :: split.right) := by
        rw [hleftDecomp]
        simp [List.append_assoc]
      have hbefore : before = leftBefore :=
        prefix_eq_of_nodup_decompositions hNewNodup
          hdecomp hcanonical
      subst before
      have hOldDecomp :
          oldOrder =
            leftBefore ++ i :: (leftAfter ++ split.right) := by
        calc
          oldOrder = split.left ++ split.right := split.split
          _ = (leftBefore ++ i :: leftAfter) ++ split.right := by
            rw [hleftDecomp]
          _ = leftBefore ++ i :: (leftAfter ++ split.right) := by
            simp [List.append_assoc]
      simpa [setComplexity, hitarget] using
        hOld leftBefore i (leftAfter ++ split.right) hOldDecomp
    · obtain ⟨rightBefore, rightAfter, hrightDecomp⟩ :=
        List.mem_iff_append.mp hiRight
      have hcanonical :
          split.left ++ target :: split.right =
            (split.left ++ target :: rightBefore) ++
              i :: rightAfter := by
        rw [hrightDecomp]
        simp [List.append_assoc]
      have hbefore :
          before = split.left ++ target :: rightBefore :=
        prefix_eq_of_nodup_decompositions hNewNodup
          hdecomp hcanonical
      subst before
      have hOldDecomp :
          oldOrder =
            (split.left ++ rightBefore) ++ i :: rightAfter := by
        calc
          oldOrder = split.left ++ split.right := split.split
          _ = split.left ++
              (rightBefore ++ i :: rightAfter) := by
            rw [hrightDecomp]
          _ = (split.left ++ rightBefore) ++ i :: rightAfter := by
            simp [List.append_assoc]
      have hOldBound :
          MaxScoreBound F
            (insert i (split.left ++ rightBefore).toFinset)
            i (complexity i) :=
        hOld (split.left ++ rightBefore) i rightAfter hOldDecomp
      have hCross :
          procedureStepComplexity F
              (insert target
                (insert i
                  (split.left ++ rightBefore).toFinset))
              target <= complexity i := by
        simpa [insertionScore, insertionScope,
          List.toFinset_append, Finset.insert_comm,
          Finset.union_insert] using
          split.crossed_upper rightBefore i rightAfter hrightDecomp
      have hPersist :=
        maxScoreBound_persists_insert F hOldBound hCross
      simpa [setComplexity, hitarget, List.toFinset_append,
        Finset.insert_comm, Finset.union_insert] using hPersist

theorem pairwise_setComplexity_of_not_mem
    {complexity : Nat -> Nat} {target value : Nat}
    {order : List Nat}
    (htarget : target ∉ order)
    (hSorted :
      order.Pairwise (fun i j => complexity i <= complexity j)) :
    order.Pairwise
      (fun i j =>
        setComplexity complexity target value i <=
          setComplexity complexity target value j) := by
  induction order with
  | nil => simp
  | cons head tail ih =>
      have hparts : target ≠ head ∧ target ∉ tail := by
        simpa using htarget
      have hhead : head ≠ target := by
        exact fun h => hparts.1 h.symm
      have htail : target ∉ tail := hparts.2
      rw [List.pairwise_cons] at hSorted ⊢
      constructor
      · intro j hj
        have hjtarget : j ≠ target := by
          intro h
          subst j
          exact htail hj
        simpa [setComplexity, hhead, hjtarget] using hSorted.1 j hj
      · exact ih htail hSorted.2

/-- The insertion split also proves the usual insertion-sort invariant:
the finalized complexity sequence remains nondecreasing.
-/
theorem InsertionSplit.newOrder_pairwise
    {F : Nat -> Set α} {complexity : Nat -> Nat}
    {target : Nat} {oldOrder : List Nat}
    (split : InsertionSplit F complexity target oldOrder)
    (hOldSorted :
      oldOrder.Pairwise (fun i j => complexity i <= complexity j))
    (htarget : target ∉ oldOrder) :
    (split.left ++ target :: split.right).Pairwise
      (fun i j =>
        setComplexity complexity target
            (insertionScore F split.left target) i <=
          setComplexity complexity target
            (insertionScore F split.left target) j) := by
  have htargetLeft : target ∉ split.left := by
    intro h
    apply htarget
    rw [split.split]
    simp [h]
  have htargetRight : target ∉ split.right := by
    intro h
    apply htarget
    rw [split.split]
    simp [h]
  have hOldSorted' :
      (split.left ++ split.right).Pairwise
        (fun i j => complexity i <= complexity j) := by
    rw [← split.split]
    exact hOldSorted
  have hLeftSorted :
      split.left.Pairwise
        (fun i j => complexity i <= complexity j) :=
    (List.pairwise_append.mp hOldSorted').1
  have hRightSorted :
      split.right.Pairwise
        (fun i j => complexity i <= complexity j) :=
    (List.pairwise_append.mp hOldSorted').2.1
  have hOldCross :
      forall i, i ∈ split.left ->
        forall j, j ∈ split.right ->
          complexity i <= complexity j :=
    (List.pairwise_append.mp hOldSorted').2.2
  rw [List.pairwise_append]
  refine ⟨pairwise_setComplexity_of_not_mem
      htargetLeft hLeftSorted, ?_, ?_⟩
  · rw [List.pairwise_cons]
    constructor
    · intro j hj
      have hjTarget : j ≠ target := by
        intro h
        subst j
        exact htargetRight hj
      simpa [setComplexity, hjTarget] using
        split.right_upper hj
    · exact pairwise_setComplexity_of_not_mem
        htargetRight hRightSorted
  · intro i hi j hj
    rcases List.mem_cons.mp hj with hjTargetEq | hjRight
    · subst j
      have hiTarget : i ≠ target := by
        intro h
        subst i
        exact htargetLeft hi
      simp only [setComplexity_other _ hiTarget,
        setComplexity_same]
      exact Nat.le_of_lt (split.left_lower i hi)
    · have hiTarget : i ≠ target := by
        intro h
        subst i
        exact htargetLeft hi
      have hjTarget : j ≠ target := by
        intro h
        subst j
        exact htargetRight hjRight
      simpa [setComplexity, hiTarget, hjTarget] using
        hOldCross i hi j hjRight

/-- The new ordering is a permutation of the old ordering with the target
appended. -/
theorem InsertionSplit.newOrder_perm
    {F : Nat -> Set α} {complexity : Nat -> Nat}
    {target : Nat} {oldOrder : List Nat}
    (split : InsertionSplit F complexity target oldOrder) :
    (split.left ++ target :: split.right).Perm
      (oldOrder ++ [target]) := by
  have hmove :
      (split.left ++ target :: split.right).Perm
        (split.left ++ (split.right ++ [target])) :=
    List.Perm.append_left split.left
      (List.perm_append_singleton target split.right).symm
  calc
    (split.left ++ target :: split.right).Perm
        (split.left ++ (split.right ++ [target])) := hmove
    _ = (split.left ++ split.right) ++ [target] := by
      simp [List.append_assoc]
    _ = oldOrder ++ [target] :=
      congrArg (fun xs => xs ++ [target]) split.split.symm

/-! ## Certified finite executions of Procedure 1 -/

/-- A finite execution after inserting exactly the original indices
`0, ..., stage-1`.
-/
structure ProcedureStage
    (F : Nat -> Set α) (stage : Nat) where
  order : List Nat
  complexity : Nat -> Nat
  witness : Nat -> Finset Nat
  order_perm : order.Perm (List.range stage)
  sorted :
    order.Pairwise (fun i j => complexity i <= complexity j)
  max_bounds : OrderMaxScoreBounds F order complexity
  witness_positive :
    forall i, i < stage -> 0 < complexity i ->
      FiniteIntersectionCandidate F (Finset.range (i + 1))
        i (witness i) ∧
      finiteIntersectionScore F (witness i) = complexity i
  witness_other_lower :
    forall i, i < stage -> forall j, j ∈ witness i -> j ≠ i ->
      j < i ∧ complexity j < complexity i

def setWitness
    (witness : Nat -> Finset Nat)
    (target : Nat) (value : Finset Nat) : Nat -> Finset Nat :=
  fun i => if i = target then value else witness i

@[simp] theorem setWitness_same
    (witness : Nat -> Finset Nat) (target : Nat)
    (value : Finset Nat) :
    setWitness witness target value target = value := by
  simp [setWitness]

@[simp] theorem setWitness_other
    (witness : Nat -> Finset Nat)
    {target i : Nat} (value : Finset Nat) (hi : i ≠ target) :
    setWitness witness target value i = witness i := by
  simp [setWitness, hi]

/-- One full outer iteration of Procedure 1. -/
noncomputable def extendProcedureStage
    (F : Nat -> Set α) {stage : Nat}
    (current : ProcedureStage F stage) :
    ProcedureStage F (stage + 1) := by
  classical
  have hOldNodup : current.order.Nodup :=
    (current.order_perm.nodup_iff).mpr List.nodup_range
  have htarget : stage ∉ current.order := by
    intro hmem
    have : stage ∈ List.range stage :=
      current.order_perm.mem_iff.mp hmem
    simp at this
  let split : InsertionSplit F current.complexity stage current.order :=
    Classical.choice
      (exists_insertionSplit F current.complexity stage current.order
        current.sorted hOldNodup)
  let newValue : Nat :=
    insertionScore F split.left stage
  let newWitness : Finset Nat :=
    procedureStepWitness F (insertionScope split.left stage) stage
  let nextComplexity :=
    setComplexity current.complexity stage newValue
  let nextWitness :=
    setWitness current.witness stage newWitness
  refine {
    order := split.left ++ stage :: split.right
    complexity := nextComplexity
    witness := nextWitness
    order_perm := ?_
    sorted := ?_
    max_bounds := ?_
    witness_positive := ?_
    witness_other_lower := ?_
  }
  · have hperm :
        (split.left ++ stage :: split.right).Perm
          (current.order ++ [stage]) :=
      split.newOrder_perm
    have htail :
        (current.order ++ [stage]).Perm
          (List.range stage ++ [stage]) :=
      List.Perm.append_right [stage] current.order_perm
    simpa [List.range_succ] using hperm.trans htail
  · exact split.newOrder_pairwise current.sorted htarget
  · exact split.orderMaxScoreBounds hOldNodup htarget current.max_bounds
  · intro i hiStage hiPositive
    by_cases hi : i = stage
    · subst i
      have hiPositive' : 0 < newValue := by
        simpa [nextComplexity, setComplexity] using hiPositive
      have hexists :
          ∃ witness,
            FiniteIntersectionCandidate F
              (insertionScope split.left stage) stage witness := by
        by_contra hnone
        have hzero :=
          procedureStepComplexity_eq_zero F
            (insertionScope split.left stage) stage hnone
        change 0 <
          procedureStepComplexity F
            (insertionScope split.left stage) stage at hiPositive'
        omega
      have hselected :=
        procedureStepWitness_spec F
          (insertionScope split.left stage) stage hexists
      have hscope :
          insertionScope split.left stage ⊆
            Finset.range (stage + 1) := by
        intro j hj
        simp only [insertionScope, Finset.mem_insert,
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
      constructor
      · simpa [nextWitness, setWitness] using
          (finiteIntersectionCandidate_mono_scope F hscope hselected.1)
      · simpa [nextWitness, nextComplexity, setWitness,
          setComplexity, newWitness, newValue, insertionScore] using
          (procedureStepComplexity_eq_score F
            (insertionScope split.left stage) stage hexists).symm
    · have hiOld : i < stage := by omega
      have hiPositiveOld : 0 < current.complexity i := by
        simpa [nextComplexity, setComplexity, hi] using hiPositive
      simpa [nextComplexity, nextWitness, setComplexity,
        setWitness, hi] using
        current.witness_positive i hiOld hiPositiveOld
  · intro i hiStage j hjWitness hji
    by_cases hi : i = stage
    · subst i
      have hjWitness' : j ∈ newWitness := by
        simpa [nextWitness, setWitness] using hjWitness
      by_cases hexists :
          ∃ witness,
            FiniteIntersectionCandidate F
              (insertionScope split.left stage) stage witness
      · have hselected :=
          (procedureStepWitness_spec F
            (insertionScope split.left stage) stage hexists).1
        have hjScope : j ∈ insertionScope split.left stage :=
          hselected.1 hjWitness'
        have hjLeft : j ∈ split.left := by
          simpa [insertionScope, hji] using hjScope
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
      · have hempty :
            newWitness = ∅ := by
          simp [newWitness, procedureStepWitness, hexists]
        rw [hempty] at hjWitness'
        simp at hjWitness'
    · have hiOld : i < stage := by omega
      have hold :=
        current.witness_other_lower i hiOld j
          (by simpa [nextWitness, setWitness, hi] using hjWitness) hji
      have hj : j ≠ stage := by omega
      constructor
      · exact hold.1
      · simpa [nextComplexity, setComplexity, hi, hj] using hold.2

/-- The exact finite execution of Procedure 1 after `stage` insertions. -/
noncomputable def canonicalProcedureStage
    (F : Nat -> Set α) : (stage : Nat) -> ProcedureStage F stage
  | 0 => {
      order := []
      complexity := fun _ => 0
      witness := fun _ => ∅
      order_perm := by simp
      sorted := by simp
      max_bounds := by
        intro before i after h
        simp at h
      witness_positive := by omega
      witness_other_lower := by omega
    }
  | stage + 1 =>
      extendProcedureStage F (canonicalProcedureStage F stage)

/-! ## Claim 3.1 from the constructed finite stage -/

/-- The source's finite-prefix comparison property in overview Theorem 1. -/
def EarlierPrefixTradeoff
    (stage : Nat) (benchmark : TimeVector)
    (Achievable : Set TimeVector) : Prop :=
  forall time, time ∈ Achievable -> forall i, i < stage ->
    time i < benchmark i ->
      ∃ j, j < i ∧ benchmark j < time j

/-- Any competitor improving a coordinate in the finite prefix worsens a
coordinate in the same prefix.
-/
def PrefixParetoOptimal
    (stage : Nat) (Achievable : Set TimeVector)
    (benchmark : TimeVector) : Prop :=
  forall time, time ∈ Achievable ->
    (∃ i, i < stage ∧ time i < benchmark i) ->
      ∃ j, j < stage ∧ benchmark j < time j

theorem earlierPrefixTradeoff_implies_prefixParetoOptimal
    {stage : Nat} {benchmark : TimeVector}
    {Achievable : Set TimeVector}
    (h : EarlierPrefixTradeoff stage benchmark Achievable) :
    PrefixParetoOptimal stage Achievable benchmark := by
  intro time htime himprove
  obtain ⟨i, hiStage, hi⟩ := himprove
  obtain ⟨j, hj, hjWorse⟩ := h time htime i hiStage hi
  exact ⟨j, hj.trans hiStage, hjWorse⟩

/-- A finite set of known cardinality can be presented without repetition
in exactly that many rounds.
-/
noncomputable def finiteSetHistory
    (S : Set α) (hFinite : S.Finite) (n : Nat)
    (hcard : S.ncard = n) : Fin n -> α := by
  classical
  let T := hFinite.toFinset
  have hTcard : T.card = n := by
    rw [← Set.ncard_eq_toFinset_card S hFinite]
    exact hcard
  exact fun k => ((T.equivFinOfCardEq hTcard).symm k).1

theorem finiteSetHistory_injective
    (S : Set α) (hFinite : S.Finite) (n : Nat)
    (hcard : S.ncard = n) :
    Function.Injective (finiteSetHistory S hFinite n hcard) := by
  classical
  let T := hFinite.toFinset
  have hTcard : T.card = n := by
    rw [← Set.ncard_eq_toFinset_card S hFinite]
    exact hcard
  intro i j hij
  apply (T.equivFinOfCardEq hTcard).symm.injective
  apply Subtype.ext
  exact hij

theorem finiteSetHistory_range
    (S : Set α) (hFinite : S.Finite) (n : Nat)
    (hcard : S.ncard = n) :
    Set.range (finiteSetHistory S hFinite n hcard) = S := by
  classical
  let T := hFinite.toFinset
  have hTcard : T.card = n := by
    rw [← Set.ncard_eq_toFinset_card S hFinite]
    exact hcard
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    change ((T.equivFinOfCardEq hTcard).symm k).1 ∈ S
    exact hFinite.mem_toFinset.mp
      ((T.equivFinOfCardEq hTcard).symm k).2
  · intro hx
    let z : T := ⟨x, hFinite.mem_toFinset.mpr hx⟩
    refine ⟨T.equivFinOfCardEq hTcard z, ?_⟩
    change ((T.equivFinOfCardEq hTcard).symm
      (T.equivFinOfCardEq hTcard z)).1 = x
    simp [z]

/-- Claim 3.1 for the actual finite execution produced above. -/
theorem ProcedureStage.earlierPrefixTradeoff
    {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) :
    EarlierPrefixTradeoff stage
      (fun i => current.complexity i + 1)
      (RealizableTimeVectors F) := by
  intro time htime i hiStage himprove
  obtain ⟨G, hAchieves, hPositive⟩ := htime
  change time i < current.complexity i + 1 at himprove
  have hcomplexity : 0 < current.complexity i := by
    have hpos := hPositive i
    omega
  obtain ⟨hCandidate, hscore⟩ :=
    current.witness_positive i hiStage hcomplexity
  let core := indexedIntersection F (current.witness i)
  have hcoreFinite : core.Finite := hCandidate.2.2
  have hcoreCard : core.ncard = current.complexity i := by
    simpa [core, finiteIntersectionScore] using hscore
  let xs : Fin (current.complexity i) -> α :=
    finiteSetHistory core hcoreFinite
      (current.complexity i) hcoreCard
  have hxsInjective : Function.Injective xs :=
    finiteSetHistory_injective core hcoreFinite
      (current.complexity i) hcoreCard
  have hxsRange : Set.range xs = core :=
    finiteSetHistory_range core hcoreFinite
      (current.complexity i) hcoreCard
  have htimeAtWitness : time i <= current.complexity i := by
    omega
  have htargetHistory : forall k, xs k ∈ F i := by
    intro k
    have hk : xs k ∈ core := by
      rw [← hxsRange]
      exact Set.mem_range_self k
    exact hk i hCandidate.2.1
  have hout :=
    hAchieves i (current.complexity i) xs htimeAtWitness
      hxsInjective htargetHistory
  have hmissing :
      ∃ j, j ∈ current.witness i ∧
        G (current.complexity i) xs ∉ F j := by
    by_contra hnone
    push_neg at hnone
    have hintersection :
        G (current.complexity i) xs ∈ core := by
      intro j hj
      exact hnone j hj
    rw [← hxsRange] at hintersection
    obtain ⟨k, hk⟩ := hintersection
    exact hout.2 k hk.symm
  obtain ⟨j, hjWitness, hjMissing⟩ := hmissing
  have hji : j ≠ i := by
    intro h
    subst j
    exact hjMissing hout.1
  obtain ⟨hjEarlier, hjLower⟩ :=
    current.witness_other_lower i hiStage j hjWitness hji
  refine ⟨j, hjEarlier, ?_⟩
  by_contra hnotWorse
  have htimeJ : time j <= current.complexity i := by
    have : time j <= current.complexity j + 1 :=
      Nat.le_of_not_gt hnotWorse
    omega
  have hjHistory : forall k, xs k ∈ F j := by
    intro k
    have hk : xs k ∈ core := by
      rw [← hxsRange]
      exact Set.mem_range_self k
    exact hk j hjWitness
  have houtJ :=
    hAchieves j (current.complexity i) xs htimeJ
      hxsInjective hjHistory
  exact hjMissing houtJ.1

/-- The canonical finite execution lies on the Pareto frontier of every
finite original-language prefix.
-/
theorem ProcedureStage.prefixParetoOptimal
    {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) :
    PrefixParetoOptimal stage (RealizableTimeVectors F)
      (fun i => current.complexity i + 1) :=
  earlierPrefixTradeoff_implies_prefixParetoOptimal
    current.earlierPrefixTradeoff

/-- Procedure 1 itself therefore produces the lower-bound half of overview
Theorem 1 for every requested finite prefix.
-/
theorem canonicalProcedureStage_prefixParetoOptimal
    (F : Nat -> Set α) (stage : Nat) :
    PrefixParetoOptimal stage (RealizableTimeVectors F)
      (fun i =>
        (canonicalProcedureStage F stage).complexity i + 1) :=
  (canonicalProcedureStage F stage).prefixParetoOptimal

/-! ## The frozen-prefix generator for overview Theorem 1 -/

@[simp] theorem indexedIntersection_empty
    (F : Nat -> Set α) :
    indexedIntersection F ∅ = Set.univ := by
  ext x
  simp [indexedIntersection]

@[simp] theorem indexedIntersection_insert
    (F : Nat -> Set α) (i : Nat) (selected : Finset Nat) :
    indexedIntersection F (insert i selected) =
      F i ∩ indexedIntersection F selected := by
  ext x
  simp [indexedIntersection]

/-! ### A predicate-parameterized greedy scan kernel -/

/-- Insert the current item exactly when the supplied acceptance predicate
passes.  The standard and noisy scans below are compatibility wrappers around
this paper-local structural kernel. -/
noncomputable def greedyListStepBy [DecidableEq ι]
    (accept : Finset ι -> ι -> Prop)
    (selected : Finset ι) (i : ι) : Finset ι := by
  classical
  exact if accept selected i then insert i selected else selected

noncomputable def greedyListScanBy [DecidableEq ι]
    (accept : Finset ι -> ι -> Prop) :
    Finset ι -> List ι -> Finset ι
  | selected, [] => selected
  | selected, i :: rest =>
      greedyListScanBy accept
        (greedyListStepBy accept selected i) rest

theorem greedyListScanBy_append [DecidableEq ι]
    (accept : Finset ι -> ι -> Prop)
    (selected : Finset ι) (first second : List ι) :
    greedyListScanBy accept selected (first ++ second) =
      greedyListScanBy accept
        (greedyListScanBy accept selected first) second := by
  induction first generalizing selected with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.cons_append, greedyListScanBy]
      exact ih (greedyListStepBy accept selected i)

theorem greedyListStepBy_subset [DecidableEq ι]
    (accept : Finset ι -> ι -> Prop)
    (selected : Finset ι) (i : ι) :
    selected ⊆ greedyListStepBy accept selected i := by
  classical
  simp only [greedyListStepBy]
  split
  · exact Finset.subset_insert i selected
  · exact Finset.Subset.rfl

theorem greedyListScanBy_initial_subset [DecidableEq ι]
    (accept : Finset ι -> ι -> Prop)
    (selected : Finset ι) (order : List ι) :
    selected ⊆ greedyListScanBy accept selected order := by
  induction order generalizing selected with
  | nil => exact Finset.Subset.rfl
  | cons i rest ih =>
      exact (greedyListStepBy_subset accept selected i).trans
        (ih (greedyListStepBy accept selected i))

theorem greedyListStepBy_subset_insert [DecidableEq ι]
    (accept : Finset ι -> ι -> Prop)
    (selected : Finset ι) (i : ι) :
    greedyListStepBy accept selected i ⊆ insert i selected := by
  classical
  simp only [greedyListStepBy]
  split
  · exact Finset.Subset.rfl
  · exact Finset.subset_insert i selected

theorem greedyListScanBy_subset_union [DecidableEq ι]
    (accept : Finset ι -> ι -> Prop)
    (selected : Finset ι) (order : List ι) :
    greedyListScanBy accept selected order ⊆
      selected ∪ order.toFinset := by
  classical
  induction order generalizing selected with
  | nil => simp [greedyListScanBy]
  | cons i rest ih =>
      intro j hj
      have hj' := ih (greedyListStepBy accept selected i) hj
      have hstep := greedyListStepBy_subset_insert accept selected i
      simp only [List.toFinset_cons, Finset.mem_union,
        Finset.mem_insert] at hj' ⊢
      rcases hj' with hjStep | hjRest
      · rcases Finset.mem_insert.mp (hstep hjStep) with rfl | hjSelected
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hjSelected
      · exact Or.inr (Or.inr hjRest)

/-- Any invariant preserved by one conditional-insertion step is preserved
by the entire scan. -/
theorem greedyListScanBy_invariant [DecidableEq ι]
    (accept : Finset ι -> ι -> Prop)
    (invariant : Finset ι -> Prop)
    (hStep : ∀ selected i, invariant selected ->
      invariant (greedyListStepBy accept selected i))
    {selected : Finset ι} {order : List ι}
    (hInitial : invariant selected) :
    invariant (greedyListScanBy accept selected order) := by
  induction order generalizing selected with
  | nil => exact hInitial
  | cons i rest ih =>
      exact ih (hStep selected i hInitial)

/-! ### Standard Procedure-1 specialization -/

def standardGreedyAccept
    (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (i : Nat) : Prop :=
  (↑sample : Set α) ⊆ F i ∧
    (indexedIntersection F (insert i selected)).Infinite

noncomputable abbrev greedyListStep
    (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (i : Nat) : Finset Nat :=
  greedyListStepBy (standardGreedyAccept F sample) selected i

noncomputable abbrev greedyListScan
    (F : Nat -> Set α) (sample : Finset α) :
    Finset Nat -> List Nat -> Finset Nat :=
  greedyListScanBy (standardGreedyAccept F sample)

theorem greedyListScan_append
    (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (first second : List Nat) :
    greedyListScan F sample selected (first ++ second) =
      greedyListScan F sample
        (greedyListScan F sample selected first) second :=
  greedyListScanBy_append
    (standardGreedyAccept F sample) selected first second

theorem greedyListStep_subset
    (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (i : Nat) :
    selected ⊆ greedyListStep F sample selected i :=
  greedyListStepBy_subset
    (standardGreedyAccept F sample) selected i

theorem greedyListScan_initial_subset
    (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (order : List Nat) :
    selected ⊆ greedyListScan F sample selected order :=
  greedyListScanBy_initial_subset
    (standardGreedyAccept F sample) selected order

theorem greedyListStep_subset_union
    (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (i : Nat) :
    greedyListStep F sample selected i ⊆ insert i selected :=
  greedyListStepBy_subset_insert
    (standardGreedyAccept F sample) selected i

theorem greedyListScan_subset_union
    (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (order : List Nat) :
    greedyListScan F sample selected order ⊆
      selected ∪ order.toFinset :=
  greedyListScanBy_subset_union
    (standardGreedyAccept F sample) selected order

theorem sample_subset_greedyListScan_core
    (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (order : List Nat)
    (hSample :
      (↑sample : Set α) ⊆ indexedIntersection F selected) :
    (↑sample : Set α) ⊆
      indexedIntersection F
        (greedyListScan F sample selected order) := by
  classical
  apply greedyListScanBy_invariant
    (standardGreedyAccept F sample)
    (fun current =>
      (↑sample : Set α) ⊆ indexedIntersection F current)
    ?_ hSample
  intro current i hCurrent
  simp only [greedyListStepBy]
  split
  next h =>
    rw [indexedIntersection_insert]
    exact Set.subset_inter h.1 hCurrent
  next => exact hCurrent

theorem greedyListScan_core_infinite
    [Infinite α] (F : Nat -> Set α) (sample : Finset α)
    (selected : Finset Nat) (order : List Nat)
    (hInfinite : (indexedIntersection F selected).Infinite) :
    (indexedIntersection F
      (greedyListScan F sample selected order)).Infinite := by
  classical
  apply greedyListScanBy_invariant
    (standardGreedyAccept F sample)
    (fun current => (indexedIntersection F current).Infinite)
    ?_ hInfinite
  intro current i hCurrent
  simp only [greedyListStepBy]
  split
  next h => exact h.2
  next => exact hCurrent

/-- The arbitrary-order version of the target-selection argument in
Theorem 4.
-/
theorem target_selected_in_greedyListScan
    (F : Nat -> Set α) (sample : Finset α)
    {order before after : List Nat} {target bound : Nat}
    (hOrder : order = before ++ target :: after)
    (hMax :
      MaxScoreBound F (insert target before.toFinset) target bound)
    (hSample : (↑sample : Set α) ⊆ F target)
    (hcard : bound < sample.card) :
    target ∈ greedyListScan F sample ∅ order := by
  classical
  let selectedBefore :=
    greedyListScan F sample ∅ before
  have hSelectedSubset :
      selectedBefore ⊆ before.toFinset := by
    have h :=
      greedyListScan_subset_union F sample ∅ before
    simpa [selectedBefore] using h
  have hSampleBefore :
      (↑sample : Set α) ⊆
        indexedIntersection F selectedBefore := by
    apply sample_subset_greedyListScan_core F sample ∅ before
    simp
  have hInfinite :
      (indexedIntersection F
        (insert target selectedBefore)).Infinite := by
    by_contra hnot
    have hFinite :
        (indexedIntersection F
          (insert target selectedBefore)).Finite :=
      not_not.mp hnot
    have hCandidate :
        FiniteIntersectionCandidate F
          (insert target before.toFinset) target
          (insert target selectedBefore) := by
      refine ⟨?_, Finset.mem_insert_self _ _, hFinite⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjSelected
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (hSelectedSubset hjSelected)
    have hSampleIntersection :
        (↑sample : Set α) ⊆
          indexedIntersection F
            (insert target selectedBefore) := by
      rw [indexedIntersection_insert]
      exact Set.subset_inter hSample hSampleBefore
    have hlower :
        sample.card <=
          (indexedIntersection F
            (insert target selectedBefore)).ncard := by
      simpa using
        Set.ncard_le_ncard hSampleIntersection hFinite
    have hupper :
        (indexedIntersection F
          (insert target selectedBefore)).ncard <= bound := by
      exact hMax _ hCandidate
    exact (Nat.not_lt_of_ge (hlower.trans hupper)) hcard
  rw [hOrder, greedyListScan_append]
  change target ∈ greedyListScan F sample selectedBefore
    (target :: after)
  simp only [greedyListScan, greedyListScanBy, greedyListStepBy,
    standardGreedyAccept]
  rw [if_pos ⟨hSample, hInfinite⟩]
  exact greedyListScan_initial_subset F sample
    (insert target selectedBefore) after
    (Finset.mem_insert_self _ _)

/-- The scan order used for a requested canonical prefix: first keep the
Procedure-1 order frozen, then append the untouched natural tail.
-/
def frozenScanOrder
    {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) (t : Nat) : List Nat :=
  current.order ++ List.range' stage t

noncomputable def frozenPrefixGenerator
    [Infinite α] {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) : HistoryGenerator α := by
  classical
  exact fun _ xs =>
    let sample := GenLimit.Generic.sequenceSample xs
    let selected :=
      greedyListScan F sample ∅
        (frozenScanOrder current sample.card)
    GenLimit.Support.freshFromInfinite
      (indexedIntersection F selected)
      (greedyListScan_core_infinite F sample ∅
        (frozenScanOrder current sample.card)
        (by simpa using
          (Set.infinite_univ : (Set.univ : Set α).Infinite)))
      sample

theorem frozenPrefixGenerator_spec
    [Infinite α] {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage)
    {t : Nat} (xs : Fin t -> α) :
    frozenPrefixGenerator current t xs ∈
        indexedIntersection F
          (greedyListScan F
            (GenLimit.Generic.sequenceSample xs) ∅
            (frozenScanOrder current
              (GenLimit.Generic.sequenceSample xs).card)) ∧
      frozenPrefixGenerator current t xs ∉
        GenLimit.Generic.sequenceSample xs := by
  classical
  simp only [frozenPrefixGenerator]
  exact ⟨GenLimit.Support.freshFromInfinite_mem _ _ _,
    GenLimit.Support.freshFromInfinite_not_mem _ _ _⟩

/-- Exact canonical bound for every language in the frozen finite prefix. -/
theorem frozenPrefixGenerator_correct_prefix
    [Infinite α] {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage)
    {i t : Nat} (hiStage : i < stage)
    (xs : Fin t -> α)
    (hthreshold : current.complexity i + 1 <= t)
    (hInjective : Function.Injective xs)
    (hTarget : forall k, xs k ∈ F i) :
    frozenPrefixGenerator current t xs ∈ F i ∧
      forall k, frozenPrefixGenerator current t xs ≠ xs k := by
  classical
  let sample := GenLimit.Generic.sequenceSample xs
  have hsampleCard : sample.card = t :=
    GenLimit.Generic.sequenceSample_card_of_injective xs hInjective
  have hiOrder : i ∈ current.order := by
    apply current.order_perm.mem_iff.mpr
    exact List.mem_range.mpr hiStage
  obtain ⟨before, after, hOrder⟩ :=
    List.mem_iff_append.mp hiOrder
  have hScanOrder :
      frozenScanOrder current sample.card =
        before ++ i ::
          (after ++ List.range' stage sample.card) := by
    simp only [frozenScanOrder]
    rw [hOrder]
    simp [List.append_assoc]
  have hSampleTarget :
      (↑sample : Set α) ⊆ F i :=
    GenLimit.Generic.sequenceSample_subset_of_pointwise hTarget
  have hcard : current.complexity i < sample.card := by
    omega
  have hiSelected :
      i ∈ greedyListScan F sample ∅
        (frozenScanOrder current sample.card) := by
    exact target_selected_in_greedyListScan F sample
      hScanOrder
      (current.max_bounds before i after hOrder)
      hSampleTarget hcard
  have hspec := frozenPrefixGenerator_spec current xs
  constructor
  · exact hspec.1 i hiSelected
  · intro k hk
    exact hspec.2
      (GenLimit.Generic.mem_sequenceSample_iff.mpr ⟨k, hk.symm⟩)

/-- Prefix immediately before a natural-tail target. -/
def frozenTailPrefix
    {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) (i : Nat) : List Nat :=
  current.order ++ List.range' stage (i - stage)

/-- A complete achieved time vector.  On the requested finite prefix this is
exactly `m*(L_i)+1`; outside it, a direct finite-search bound is used only to
guarantee non-uniform generation.
-/
noncomputable def frozenTimeVector
    {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) : TimeVector :=
  fun i =>
    if i < stage then current.complexity i + 1
    else
      max (i - stage + 1)
        (procedureStepComplexity F
          (insert i (frozenTailPrefix current i).toFinset) i + 1)

theorem frozenTimeVector_positive
    {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) :
    PositiveTimeVector (frozenTimeVector current) := by
  intro i
  simp only [frozenTimeVector]
  split
  · omega
  · exact le_trans (by omega)
      (Nat.le_max_right _ _)

theorem frozenTimeVector_matchesPrefix
    {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) :
    MatchesPrefix stage (frozenTimeVector current)
      (fun i => current.complexity i + 1) := by
  intro i hi
  simp [frozenTimeVector, hi]

/-- Correctness for a target in the untouched natural tail. -/
theorem frozenPrefixGenerator_correct_tail
    [Infinite α] {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage)
    {i t : Nat} (hiStage : stage <= i)
    (xs : Fin t -> α)
    (hthreshold :
      max (i - stage + 1)
        (procedureStepComplexity F
          (insert i (frozenTailPrefix current i).toFinset) i + 1) <= t)
    (hInjective : Function.Injective xs)
    (hTarget : forall k, xs k ∈ F i) :
    frozenPrefixGenerator current t xs ∈ F i ∧
      forall k, frozenPrefixGenerator current t xs ≠ xs k := by
  classical
  let sample := GenLimit.Generic.sequenceSample xs
  let d := i - stage
  let q := t - (d + 1)
  have hd : stage + d = i := by
    dsimp [d]
    omega
  have hentry : d + 1 <= t := by
    exact (Nat.le_max_left _ _).trans hthreshold
  have ht : d + 1 + q = t := by
    dsimp [q]
    omega
  have hrange :
      List.range' stage t =
        List.range' stage d ++
          i :: List.range' (i + 1) q := by
    calc
      List.range' stage t =
          List.range' stage (d + 1 + q) := by rw [ht]
      _ = List.range' stage (d + 1) ++
          List.range' (stage + (d + 1)) q := by
        simp
      _ = (List.range' stage d ++ [stage + d]) ++
          List.range' (stage + (d + 1)) q := by
        rw [List.range'_1_concat]
      _ = List.range' stage d ++
          i :: List.range' (i + 1) q := by
        have hstart : stage + (d + 1) = i + 1 := by omega
        rw [hd, hstart]
        simp [List.append_assoc]
  have hsampleCard : sample.card = t :=
    GenLimit.Generic.sequenceSample_card_of_injective xs hInjective
  have hScanOrder :
      frozenScanOrder current sample.card =
        frozenTailPrefix current i ++
          i :: List.range' (i + 1) q := by
    simp only [frozenScanOrder, frozenTailPrefix]
    rw [hsampleCard, hrange]
    simp [d, List.append_assoc]
  have hSampleTarget :
      (↑sample : Set α) ⊆ F i :=
    GenLimit.Generic.sequenceSample_subset_of_pointwise hTarget
  have hcard :
      procedureStepComplexity F
        (insert i (frozenTailPrefix current i).toFinset) i <
          sample.card := by
    have :=
      (Nat.le_max_right (i - stage + 1)
        (procedureStepComplexity F
          (insert i (frozenTailPrefix current i).toFinset) i + 1)).trans
        hthreshold
    omega
  have hiSelected :
      i ∈ greedyListScan F sample ∅
        (frozenScanOrder current sample.card) := by
    exact target_selected_in_greedyListScan F sample
      hScanOrder
      (procedureStep_maxScoreBound F
        (insert i (frozenTailPrefix current i).toFinset) i)
      hSampleTarget hcard
  have hspec := frozenPrefixGenerator_spec current xs
  constructor
  · exact hspec.1 i hiSelected
  · intro k hk
    exact hspec.2
      (GenLimit.Generic.mem_sequenceSample_iff.mpr ⟨k, hk.symm⟩)

theorem frozenPrefixGenerator_achieves
    [Infinite α] {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) :
    AchievesTimeVector (frozenPrefixGenerator current) F
      (frozenTimeVector current) := by
  intro i t xs htime hInjective hTarget
  by_cases hi : i < stage
  · apply frozenPrefixGenerator_correct_prefix current hi xs
      (by simpa [frozenTimeVector, hi] using htime)
      hInjective hTarget
  · apply frozenPrefixGenerator_correct_tail current
      (Nat.le_of_not_gt hi) xs
      (by simpa [frozenTimeVector, hi] using htime)
      hInjective hTarget

theorem frozenTimeVector_realizable
    [Infinite α] {F : Nat -> Set α} {stage : Nat}
    (current : ProcedureStage F stage) :
    frozenTimeVector current ∈ RealizableTimeVectors F :=
  ⟨frozenPrefixGenerator current,
    frozenPrefixGenerator_achieves current,
    frozenTimeVector_positive current⟩

theorem prefixParetoOptimal_of_matchesPrefix
    {stage : Nat} {Achievable : Set TimeVector}
    {actual benchmark : TimeVector}
    (hmatch : MatchesPrefix stage actual benchmark)
    (hPareto :
      PrefixParetoOptimal stage Achievable benchmark) :
    PrefixParetoOptimal stage Achievable actual := by
  intro time htime himprove
  obtain ⟨i, hiStage, hi⟩ := himprove
  have hi' : time i < benchmark i := by
    simpa [hmatch i hiStage] using hi
  obtain ⟨j, hjStage, hj⟩ :=
    hPareto time htime ⟨i, hiStage, hi'⟩
  exact ⟨j, hjStage, by simpa [hmatch j hjStage] using hj⟩

/-- Overview Theorem 1, at the semantic finite-history level.

For every requested finite prefix, the recursively constructed Procedure-1
times are achieved by one non-uniform generator on the entire family, and
the achieved time vector satisfies the source's finite-prefix Pareto
comparison.
-/
theorem overview_theorem_1_semantic
    [Infinite α] (F : Nat -> Set α) (stage : Nat) :
    ∃ G : HistoryGenerator α, ∃ time : TimeVector,
      AchievesTimeVector G F time ∧
      PositiveTimeVector time ∧
      MatchesPrefix stage time
        (fun i =>
          (canonicalProcedureStage F stage).complexity i + 1) ∧
      PrefixParetoOptimal stage
        (RealizableTimeVectors F) time := by
  let current := canonicalProcedureStage F stage
  refine ⟨frozenPrefixGenerator current,
    frozenTimeVector current,
    frozenPrefixGenerator_achieves current,
    frozenTimeVector_positive current,
    frozenTimeVector_matchesPrefix current, ?_⟩
  exact prefixParetoOptimal_of_matchesPrefix
    (frozenTimeVector_matchesPrefix current)
    current.prefixParetoOptimal

/-! ## The zero-score defect in literal Claim 3.2 -/

theorem procedureStepWitness_eq_empty_of_noCandidate
    (F : Nat -> Set α) (scopeSet : Finset Nat) (target : Nat)
    (hnone :
      ¬(∃ witness,
        FiniteIntersectionCandidate F scopeSet target witness)) :
    procedureStepWitness F scopeSet target = ∅ := by
  classical
  simp [procedureStepWitness, hnone]

/-- A stored empty witness can never itself be a candidate, because every
candidate is required to contain its target.
-/
theorem empty_not_finiteIntersectionCandidate
    (F : Nat -> Set α) (scopeSet : Finset Nat) (target : Nat) :
    ¬FiniteIntersectionCandidate F scopeSet target ∅ := by
  intro h
  simpa using h.2.1

/-- Precise diagnostic for the literal Claim 3.2 statement.

If no candidate existed at insertion but a candidate exists in a later
scope, Procedure 1 stored the empty witness.  The later arg-max problem is
nonempty, but that stored witness is not one of its feasible points.  Hence
the paper's displayed membership in `arg max` is false in this case, even
though the max-value invariant proved above remains true.
-/
theorem literal_claim_3_2_empty_witness_obstruction
    (F : Nat -> Set α) {initialScope laterScope : Finset Nat}
    {target : Nat}
    (hnone :
      ¬(∃ witness,
        FiniteIntersectionCandidate F initialScope target witness))
    (hlater :
      ∃ witness,
        FiniteIntersectionCandidate F laterScope target witness) :
    (∃ witness,
        FiniteIntersectionCandidate F laterScope target witness) ∧
      ¬FiniteIntersectionCandidate F laterScope target
        (procedureStepWitness F initialScope target) := by
  refine ⟨hlater, ?_⟩
  rw [procedureStepWitness_eq_empty_of_noCandidate
    F initialScope target hnone]
  exact empty_not_finiteIntersectionCandidate F laterScope target

/-! ### A concrete two-language execution -/

/-- Two disjoint infinite languages.  Indices zero and one are the only
indices used below; all positive indices name the right-hand ray.
-/
def disjointInfiniteFamily : Nat -> Set (Sum Nat Nat)
  | 0 => Set.range Sum.inl
  | _ + 1 => Set.range Sum.inr

theorem disjointInfiniteFamily_zero_infinite :
    (disjointInfiniteFamily 0).Infinite := by
  simpa [disjointInfiniteFamily] using
    (Set.infinite_range_of_injective
      (Sum.inl_injective :
        Function.Injective (Sum.inl : Nat -> Sum Nat Nat)))

theorem disjointInfiniteFamily_one_infinite :
    (disjointInfiniteFamily 1).Infinite := by
  simpa [disjointInfiniteFamily] using
    (Set.infinite_range_of_injective
      (Sum.inr_injective :
        Function.Injective (Sum.inr : Nat -> Sum Nat Nat)))

theorem disjointInfiniteFamily_pair_intersection :
    indexedIntersection disjointInfiniteFamily {0, 1} = ∅ := by
  ext x
  constructor
  · intro hx
    have hx0 := hx 0 (by simp)
    have hx1 := hx 1 (by simp)
    rcases hx0 with ⟨n, rfl⟩
    simp [disjointInfiniteFamily] at hx1
  · simp

theorem disjointInfiniteFamily_initial_noCandidate :
    ¬(∃ witness,
      FiniteIntersectionCandidate disjointInfiniteFamily {0} 0 witness) := by
  rintro ⟨witness, hscope, htarget, hfinite⟩
  have hwitness : witness = {0} := by
    ext i
    constructor
    · intro hi
      have hiscope := hscope hi
      simpa using hiscope
    · intro hi
      have hi0 : i = 0 := by simpa using hi
      simpa [hi0] using htarget
  have hintersection :
      indexedIntersection disjointInfiniteFamily witness =
        disjointInfiniteFamily 0 := by
    rw [hwitness]
    ext x
    simp [indexedIntersection]
  exact disjointInfiniteFamily_zero_infinite
    (by simpa [hintersection] using hfinite)

theorem disjointInfiniteFamily_later_candidate :
    FiniteIntersectionCandidate disjointInfiniteFamily {0, 1} 0 {0, 1} := by
  refine ⟨Finset.Subset.rfl, by simp, ?_⟩
  rw [disjointInfiniteFamily_pair_intersection]
  exact Set.finite_empty

/-- In the source procedure, language zero initially stores the empty
witness.  After the disjoint language is swapped in front of it, the
displayed feasible arg-max family is nonempty, but the stored empty witness
is infeasible.  This is a concrete counterexample to literal Claim 3.2.
-/
theorem literal_claim_3_2_counterexample :
    (∃ witness,
      FiniteIntersectionCandidate disjointInfiniteFamily {0, 1} 0 witness) ∧
    ¬FiniteIntersectionCandidate disjointInfiniteFamily {0, 1} 0
      (procedureStepWitness disjointInfiniteFamily {0} 0) := by
  exact literal_claim_3_2_empty_witness_obstruction
    disjointInfiniteFamily
    disjointInfiniteFamily_initial_noCandidate
    ⟨{0, 1}, disjointInfiniteFamily_later_candidate⟩

end GenLimit.ParetoGeneration
