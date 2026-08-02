import GenLimit.BoundedMemory.Definitions
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.Extension.Linear

/-!
# Incremental approximate identification

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Definitions 13--15 and Theorem 5.2.

This file formalizes the paper's last-guess learner.  Its only persistent
state is its previous language index.  The source first topologically sorts
the finite collection by strict almost-containment and then advances by one
index whenever the current example is absent from the current hypothesis.

The final theorem includes the topological relabeling: for every nonempty
finite indexed family it produces an enumeration of exactly the same
collection and an incremental learner which approximately identifies every
target.  This is a semantic theorem.  It makes no claim that membership or
the nonconstructively selected linear extension is computable.
-/

namespace GenLimit.BoundedMemory

universe u

section AlmostContainment

variable {α : Type u}

/-- Definition 14: `A ≼_F B` means that `A \ B` is finite. -/
def AlmostContained (A B : Set α) : Prop :=
  (A \ B).Finite

/-- Definition 14: equality modulo a finite symmetric difference. -/
def AlmostEquivalent (A B : Set α) : Prop :=
  AlmostContained A B ∧ AlmostContained B A

/-- The strict almost-containment relation used in the proof of Theorem 5.2. -/
def StrictAlmostContained (A B : Set α) : Prop :=
  AlmostContained A B ∧ ¬AlmostContained B A

theorem almostContained_refl (A : Set α) :
    AlmostContained A A := by
  simp [AlmostContained]

theorem almostContained_trans {A B C : Set α}
    (hAB : AlmostContained A B) (hBC : AlmostContained B C) :
    AlmostContained A C := by
  apply (hAB.union hBC).subset
  intro x hx
  by_cases hxB : x ∈ B
  · exact Set.mem_union_right _ ⟨hxB, hx.2⟩
  · exact Set.mem_union_left _ ⟨hx.1, hxB⟩

theorem almostEquivalent_refl (A : Set α) :
    AlmostEquivalent A A :=
  ⟨almostContained_refl A, almostContained_refl A⟩

theorem almostEquivalent_symm {A B : Set α}
    (h : AlmostEquivalent A B) :
    AlmostEquivalent B A :=
  ⟨h.2, h.1⟩

theorem almostEquivalent_trans {A B C : Set α}
    (hAB : AlmostEquivalent A B) (hBC : AlmostEquivalent B C) :
    AlmostEquivalent A C :=
  ⟨almostContained_trans hAB.1 hBC.1,
    almostContained_trans hBC.2 hAB.2⟩

theorem strictAlmostContained_irrefl (A : Set α) :
    ¬StrictAlmostContained A A := by
  intro h
  exact h.2 (almostContained_refl A)

theorem strictAlmostContained_trans {A B C : Set α}
    (hAB : StrictAlmostContained A B)
    (hBC : StrictAlmostContained B C) :
    StrictAlmostContained A C := by
  refine ⟨almostContained_trans hAB.1 hBC.1, ?_⟩
  intro hCA
  exact hBC.2 (almostContained_trans hCA hAB.1)

end AlmostContainment

section TopologicalRelabeling

variable {α : Type u} {N : ℕ}

/-- The original finite index type equipped with the partial order generated
by strict almost-containment.  Almost-equivalent or incomparable languages
remain incomparable in this partial order. -/
structure AlmostOrder (langs : Fin (N + 1) → Set α) where
  val : Fin (N + 1)
deriving DecidableEq

@[ext]
theorem AlmostOrder.ext
    {langs : Fin (N + 1) → Set α} {i j : AlmostOrder langs}
    (h : i.val = j.val) :
    i = j := by
  cases i
  cases j
  simp_all

def almostOrderEquiv
    (langs : Fin (N + 1) → Set α) :
    Fin (N + 1) ≃ AlmostOrder langs where
  toFun := AlmostOrder.mk
  invFun := AlmostOrder.val
  left_inv _ := rfl
  right_inv x := by cases x; rfl

instance instFintypeAlmostOrder
    (langs : Fin (N + 1) → Set α) :
    Fintype (AlmostOrder langs) :=
  Fintype.ofEquiv (Fin (N + 1)) (almostOrderEquiv langs)

def almostOrderLinearExtensionEquiv
    (langs : Fin (N + 1) → Set α) :
    AlmostOrder langs ≃ LinearExtension (AlmostOrder langs) where
  toFun := fun i => i
  invFun := fun i => i
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeLinearExtensionAlmostOrder
    (langs : Fin (N + 1) → Set α) :
    Fintype (LinearExtension (AlmostOrder langs)) :=
  Fintype.ofEquiv (AlmostOrder langs)
    (almostOrderLinearExtensionEquiv langs)

noncomputable instance instPartialOrderAlmostOrder
    (langs : Fin (N + 1) → Set α) :
    PartialOrder (AlmostOrder langs) where
  le i j :=
    i = j ∨
      StrictAlmostContained
        (langs i.val)
        (langs j.val)
  le_refl i := Or.inl rfl
  le_trans i j k hij hjk := by
    rcases hij with rfl | hij
    · exact hjk
    rcases hjk with rfl | hjk
    · exact Or.inr hij
    exact Or.inr (strictAlmostContained_trans hij hjk)
  le_antisymm i j hij hji := by
    rcases hij with hij | hij
    · exact hij
    rcases hji with hji | hji
    · exact hji.symm
    exact (hij.2 hji.1).elim

/-- A linear extension of strict almost-containment, enumerated by
`Fin (N+1)` in increasing order. -/
noncomputable def almostOrderIso
    (langs : Fin (N + 1) → Set α) :
    Fin (N + 1) ≃o LinearExtension (AlmostOrder langs) :=
  Fintype.orderIsoFinOfCardEq _ (by
    calc
      Fintype.card (LinearExtension (AlmostOrder langs)) =
          Fintype.card (AlmostOrder langs) :=
        Fintype.card_congr (almostOrderLinearExtensionEquiv langs).symm
      _ = Fintype.card (Fin (N + 1)) :=
        Fintype.card_congr (almostOrderEquiv langs).symm
      _ = N + 1 := Fintype.card_fin _)

/-- The original index occupying position `i` in the selected topological
ordering. -/
noncomputable def relabeledIndex
    (langs : Fin (N + 1) → Set α) (i : Fin (N + 1)) :
    Fin (N + 1) :=
  (show AlmostOrder langs from almostOrderIso langs i).val

/-- The source family after topological relabeling. -/
noncomputable def topologicallyRelabeled
    (langs : Fin (N + 1) → Set α) :
    Fin (N + 1) → Set α :=
  fun i => langs (relabeledIndex langs i)

theorem relabeledIndex_bijective
    (langs : Fin (N + 1) → Set α) :
    Function.Bijective (relabeledIndex langs) := by
  let e := almostOrderIso langs
  constructor
  · intro i j hij
    apply e.injective
    apply AlmostOrder.ext
    simpa [relabeledIndex, e] using hij
  · intro j
    let wrapped : LinearExtension (AlmostOrder langs) :=
      AlmostOrder.mk j
    obtain ⟨i, hi⟩ := e.surjective wrapped
    refine ⟨i, ?_⟩
    have := congrArg (fun x : AlmostOrder langs => x.val) hi
    simpa [wrapped, relabeledIndex, e] using this

theorem range_topologicallyRelabeled
    (langs : Fin (N + 1) → Set α) :
    Set.range (topologicallyRelabeled langs) = Set.range langs := by
  apply Set.Subset.antisymm
  · rintro K ⟨i, rfl⟩
    exact ⟨relabeledIndex langs i, rfl⟩
  · rintro K ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := (relabeledIndex_bijective langs).2 j
    exact ⟨i, by simp [topologicallyRelabeled, hi]⟩

/-- The selected enumeration is a genuine topological ordering of strict
almost-containment. -/
theorem strictAlmostContained_implies_lt_relabel
    (langs : Fin (N + 1) → Set α) {i j : Fin (N + 1)}
    (hij :
      StrictAlmostContained
        (topologicallyRelabeled langs i)
        (topologicallyRelabeled langs j)) :
    i < j := by
  let e := almostOrderIso langs
  have hpartial :
      (show AlmostOrder langs from e i) ≤
        (show AlmostOrder langs from e j) :=
    Or.inr (by simpa [topologicallyRelabeled] using hij)
  have hlinear :
      e i ≤ e j := by
    change
      toLinearExtension (show AlmostOrder langs from e i) ≤
        toLinearExtension (show AlmostOrder langs from e j)
    exact
      (toLinearExtension (α := AlmostOrder langs)).monotone hpartial
  have hne : e i ≠ e j := by
    intro heq
    have hijEq : i = j := e.injective heq
    subst j
    exact strictAlmostContained_irrefl
      (topologicallyRelabeled langs i) hij
  exact e.lt_iff_lt.mp (lt_of_le_of_ne hlinear hne)

end TopologicalRelabeling

section IncrementalRun

variable {α : Type u} {N : ℕ}

/-- Definition 13: an incremental learner remembers only its previous
output and combines it with the current example. -/
abbrev IncrementalLearner (α ι : Type*) :=
  ι → α → ι

/-- The state strictly after `t` observations.  State `0` is the initial
guess, matching the paper's `i₀`. -/
def incrementalRun
    (learner : IncrementalLearner α ι) (initial : ι)
    (stream : ℕ → α) : ℕ → ι
  | 0 => initial
  | t + 1 => learner (incrementalRun learner initial stream t) (stream t)

@[simp]
theorem incrementalRun_zero
    (learner : IncrementalLearner α ι) (initial : ι)
    (stream : ℕ → α) :
    incrementalRun learner initial stream 0 = initial :=
  rfl

@[simp]
theorem incrementalRun_succ
    (learner : IncrementalLearner α ι) (initial : ι)
    (stream : ℕ → α) (t : ℕ) :
    incrementalRun learner initial stream (t + 1) =
      learner (incrementalRun learner initial stream t) (stream t) :=
  rfl

/-- Capped successor on the paper's ordered finite index set. -/
def nextIndex (i : Fin (N + 1)) : Fin (N + 1) :=
  if h : i.val < N then
    ⟨i.val + 1, by omega⟩
  else
    i

theorem nextIndex_eq_self_iff (i : Fin (N + 1)) :
    nextIndex i = i ↔ i = Fin.last N := by
  unfold nextIndex
  split_ifs with h
  · constructor
    · intro heq
      have := congrArg Fin.val heq
      simp at this
    · intro hi
      subst i
      simp at h
  · have hi : i = Fin.last N := by
      apply Fin.ext
      simp
      omega
    simp [hi]

theorem nextIndex_val_le (i : Fin (N + 1)) :
    (nextIndex i).val ≤ i.val + 1 := by
  unfold nextIndex
  split_ifs <;> simp

theorem nextIndex_ge (i : Fin (N + 1)) :
    i ≤ nextIndex i := by
  unfold nextIndex
  split_ifs with h
  · exact Fin.le_iff_val_le_val.mpr (Nat.le_succ _)
  · exact le_rfl

/-- The literal update rule from the proof of Theorem 5.2. -/
noncomputable def orderedIncrementalLearner
    (langs : Fin (N + 1) → Set α) :
    IncrementalLearner α (Fin (N + 1)) := by
  classical
  exact fun i x => if x ∈ langs i then i else nextIndex i

theorem orderedIncrementalLearner_ge
    (langs : Fin (N + 1) → Set α) (i : Fin (N + 1)) (x : α) :
    i ≤ orderedIncrementalLearner langs i x := by
  classical
  simp only [orderedIncrementalLearner]
  split_ifs
  · exact le_rfl
  · exact nextIndex_ge i

theorem orderedIncrementalLearner_val_le_succ
    (langs : Fin (N + 1) → Set α) (i : Fin (N + 1)) (x : α) :
    (orderedIncrementalLearner langs i x).val ≤ i.val + 1 := by
  classical
  simp only [orderedIncrementalLearner]
  split_ifs
  · omega
  · exact nextIndex_val_le i

theorem orderedIncrementalRun_monotone
    (langs : Fin (N + 1) → Set α) (stream : ℕ → α) :
    Monotone
      (incrementalRun
        (orderedIncrementalLearner langs) (0 : Fin (N + 1)) stream) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [incrementalRun_succ]
  exact orderedIncrementalLearner_ge _ _ _

theorem orderedIncrementalRun_step_le
    (langs : Fin (N + 1) → Set α) (stream : ℕ → α) (t : ℕ) :
    (incrementalRun
      (orderedIncrementalLearner langs) (0 : Fin (N + 1)) stream
      (t + 1)).val ≤
    (incrementalRun
      (orderedIncrementalLearner langs) (0 : Fin (N + 1)) stream t).val + 1 := by
  rw [incrementalRun_succ]
  exact orderedIncrementalLearner_val_le_succ _ _ _

/-- Any monotone sequence in a finite `Fin` type eventually stabilizes.
This is the finite-state compactness step used in the source proof. -/
theorem monotone_fin_eventually_constant
    {n : ℕ} (f : ℕ → Fin (n + 1)) (hf : Monotone f) :
    ∃ T m, ∀ t, T ≤ t → f t = m := by
  classical
  let reached : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun i => ∃ t, f t = i
  have hReached : reached.Nonempty := by
    refine ⟨f 0, ?_⟩
    simp [reached]
  let m := reached.max' hReached
  have hmMem : m ∈ reached := Finset.max'_mem reached hReached
  obtain ⟨T, hT⟩ : ∃ T, f T = m := by
    simpa [reached] using (Finset.mem_filter.mp hmMem).2
  refine ⟨T, m, ?_⟩
  intro t ht
  apply le_antisymm
  · apply Finset.le_max' reached (f t)
    simp [reached]
  · simpa [hT] using hf ht

/-- A walk starting at zero and increasing by at most one cannot skip an
intermediate index. -/
theorem adjacent_run_hits
    (f : ℕ → Fin (N + 1))
    (h0 : f 0 = 0)
    (hstep : ∀ t, (f (t + 1)).val ≤ (f t).val + 1)
    {z : Fin (N + 1)} {T : ℕ} (hz : z.val ≤ (f T).val) :
    ∃ t, t ≤ T ∧ f t = z := by
  induction T with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      apply Fin.ext
      have : (f 0).val = 0 := by simp [h0]
      omega
  | succ T ih =>
      by_cases hzT : z.val ≤ (f T).val
      · obtain ⟨t, ht, htz⟩ := ih hzT
        exact ⟨t, ht.trans (Nat.le_succ T), htz⟩
      · refine ⟨T + 1, le_rfl, ?_⟩
        apply Fin.ext
        have hs := hstep T
        omega

end IncrementalRun

section TheoremFiveTwo

variable {α : Type u} {N : ℕ}

/-- Definition 15 for one target run. -/
def ApproximatelyIdentifiesRun
    (langs : Fin (N + 1) → Set α)
    (learner : IncrementalLearner α (Fin (N + 1)))
    (initial target : Fin (N + 1))
    (stream : ℕ → α) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    AlmostEquivalent
      (langs (incrementalRun learner initial stream t))
      (langs target)

/-- A finite indexed collection is approximately identifiable by a
last-guess learner. -/
def IncrementallyApproximatelyIdentifiable
    (langs : Fin (N + 1) → Set α) : Prop :=
  ∃ learner : IncrementalLearner α (Fin (N + 1)),
    ∃ initial,
      ∀ target stream,
        GenLimit.Generic.Presents stream (langs target) →
          ApproximatelyIdentifiesRun
            langs learner initial target stream

theorem ordered_run_target_absorbing
    (langs : Fin (N + 1) → Set α)
    {target : Fin (N + 1)} {stream : ℕ → α}
    (hIn : GenLimit.Generic.StreamIn stream (langs target))
    {t : ℕ}
    (ht :
      incrementalRun
        (orderedIncrementalLearner langs) (0 : Fin (N + 1)) stream t =
        target) :
    ∀ s, t ≤ s →
      incrementalRun
        (orderedIncrementalLearner langs) (0 : Fin (N + 1)) stream s =
        target := by
  classical
  intro s hts
  induction s, hts using Nat.le_induction with
  | base => exact ht
  | succ s hts ih =>
      rw [incrementalRun_succ, ih]
      rw [orderedIncrementalLearner,
        if_pos (hIn (show stream s ∈ Set.range stream from ⟨s, rfl⟩))]

/-- Theorem 5.2 for a family already placed in the source's topological
ordering. -/
theorem theorem_5_2_ordered
    (langs : Fin (N + 1) → Set α)
    (hTopo : ∀ {i j},
      StrictAlmostContained (langs i) (langs j) → i < j) :
    IncrementallyApproximatelyIdentifiable langs := by
  classical
  let learner := orderedIncrementalLearner langs
  refine ⟨learner, (0 : Fin (N + 1)), ?_⟩
  intro target stream hP
  let run :=
    incrementalRun learner (0 : Fin (N + 1)) stream
  have hMono : Monotone run := by
    simpa [run, learner] using
      orderedIncrementalRun_monotone langs stream
  obtain ⟨T, final, hStable⟩ :=
    monotone_fin_eventually_constant run hMono
  have hFinalAt : run T = final := hStable T le_rfl
  have hFinalLeTarget : final ≤ target := by
    by_contra hnot
    have hTargetLeFinal : target.val ≤ (run T).val := by
      rw [hFinalAt]
      omega
    obtain ⟨t, htT, htTarget⟩ :=
      adjacent_run_hits run (by simp [run])
        (by
          intro s
          simpa [run, learner] using
            orderedIncrementalRun_step_le langs stream s)
        hTargetLeFinal
    have hAbsorb :=
      ordered_run_target_absorbing langs
        (GenLimit.Generic.streamIn_of_presents hP) htTarget T
        htT
    have : run T = target := by
      simpa [run, learner] using hAbsorb
    rw [hFinalAt] at this
    exact hnot (this.le)
  have hTargetToFinal :
      AlmostContained (langs target) (langs final) := by
    by_cases hEq : final = target
    · rw [hEq]
      exact almostContained_refl _
    · have hFinalNotLast : final ≠ Fin.last N := by
        intro hLast
        have hLastLeTarget : (Fin.last N : Fin (N + 1)) ≤ target := by
          simpa [hLast] using hFinalLeTarget
        have hTargetLast : target = Fin.last N := le_antisymm
          (Fin.le_last target) hLastLeTarget
        exact hEq (hLast.trans hTargetLast.symm)
      have hTailIn :
          ∀ s, T ≤ s → stream s ∈ langs final := by
        intro s hs
        have hState : run s = final := hStable s hs
        have hNext : run (s + 1) = final :=
          hStable (s + 1) (hs.trans (Nat.le_succ s))
        have hStep :
            orderedIncrementalLearner langs final (stream s) = final := by
          simpa [run, learner, hState] using hNext
        by_contra hx
        have hNextEq : nextIndex final = final := by
          simpa [orderedIncrementalLearner, hx] using hStep
        exact hFinalNotLast ((nextIndex_eq_self_iff final).mp hNextEq)
      apply (Set.finite_range fun s : Fin T => stream s).subset
      intro x hx
      have hxTarget : x ∈ langs target := hx.1
      rw [← hP] at hxTarget
      obtain ⟨s, hsx⟩ := hxTarget
      have hslt : s < T := by
        by_contra hnot
        have hxFinal := hTailIn s (Nat.le_of_not_gt hnot)
        exact hx.2 (hsx ▸ hxFinal)
      exact ⟨⟨s, hslt⟩, hsx⟩
  have hFinalToTarget :
      AlmostContained (langs final) (langs target) := by
    by_contra hnot
    have hStrict :
        StrictAlmostContained (langs target) (langs final) :=
      ⟨hTargetToFinal, hnot⟩
    have hlt : target < final := hTopo hStrict
    exact (not_lt_of_ge hFinalLeTarget) hlt
  refine ⟨T, ?_⟩
  intro t ht
  have hrun : run t = final := hStable t ht
  simpa [ApproximatelyIdentifiesRun, run, learner, hrun,
    AlmostEquivalent] using
    (show AlmostEquivalent (langs final) (langs target) from
      ⟨hFinalToTarget, hTargetToFinal⟩)

/-- Theorem 5.2, including the finite topological relabeling.

The output family enumerates exactly the same set of languages as the input
family.  The source assumes every language is infinite; that assumption is
retained literally, although the approximate-identification argument does
not use it. -/
theorem theorem_5_2
    (raw : Fin (N + 1) → Set α)
    (_hInfinite : ∀ i, (raw i).Infinite) :
    ∃ langs : Fin (N + 1) → Set α,
      Set.range langs = Set.range raw ∧
      IncrementallyApproximatelyIdentifiable langs := by
  let langs := topologicallyRelabeled raw
  refine ⟨langs, range_topologicallyRelabeled raw, ?_⟩
  apply theorem_5_2_ordered
  intro i j hij
  exact strictAlmostContained_implies_lt_relabel raw hij

end TheoremFiveTwo

end GenLimit.BoundedMemory
