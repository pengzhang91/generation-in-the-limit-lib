import GenLimit.Paper29_MistakeBoundedLanguageGeneration.CountableWeightedRun
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedMaximizer
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# The deterministic Modified-Greedy algorithm

This module formalizes the deterministic mistake-counting argument in
Section 6.2 of Kleinberg--Peale--Reingold,
*Mistake-Bounded Language Generation* (arXiv:2605.10809v1).

We use zero-based indices.  Thus paper language `Lᵢ` is Lean language
`language (i - 1)`, and at Lean round `t` the algorithm scans indices
`0, ..., t`.  It begins with the points outside the observations strictly
before round `t`.  A history-consistent language is intersected into the
current candidate set exactly when the intersection is nonempty.

The central checked charging lemma says that a mistake on target index `i`
at a round `t ≥ i` exposes an earlier index `j < i` which was consistent
before round `t` but rejects the new observation at round `t`.  Such an
index can be charged only once.  Consequently there are at most `i`
post-activation mistakes and at most `2 * i` mistakes in total.  In the
paper's one-based notation this is exactly the `2(i - 1)` component of
Lemma 6.2.

The selector is semantic and noncomputable: an arbitrary member of the
nonempty final candidate set is chosen.  No effective enumeration or
runtime claim is made here.
-/

namespace GenLimit.MistakeBounded

open GenLimit.Generic

attribute [local instance] Classical.propDecidable

/-- The observations strictly before round `t` all belong to language `i`. -/
def modifiedGreedyConsistent
    (language : ℕ → Set α) (observed : ℕ → α)
    (t i : ℕ) : Prop :=
  ∀ s, s < t → observed s ∈ language i

/-- Candidate points after scanning the first `k` language indices at
round `t`.

The initial candidates are precisely the points not previously observed.
At step `k`, language `k` is intersected in exactly when it is
history-consistent and the proposed intersection is nonempty. -/
noncomputable def modifiedGreedyCandidates
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) : ℕ → Set α
  | 0 => {x | x ∉ GenLimit.Generic.sample observed t}
  | k + 1 =>
      let current := modifiedGreedyCandidates language observed t k
      if modifiedGreedyConsistent language observed t k ∧
          (current ∩ language k).Nonempty then
        current ∩ language k
      else
        current

/-- The indices whose languages have actually been intersected into the
candidate set after the first `k` scan steps. -/
noncomputable def modifiedGreedySelected
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | k + 1 =>
      if modifiedGreedyConsistent language observed t k ∧
          (modifiedGreedyCandidates language observed t k ∩
            language k).Nonempty then
        insert k (modifiedGreedySelected language observed t k)
      else
        modifiedGreedySelected language observed t k

@[simp] theorem modifiedGreedyCandidates_zero
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) :
    modifiedGreedyCandidates language observed t 0 =
      {x | x ∉ GenLimit.Generic.sample observed t} := by
  rfl

theorem modifiedGreedyCandidates_succ
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) :
    modifiedGreedyCandidates language observed t (k + 1) =
      if modifiedGreedyConsistent language observed t k ∧
          (modifiedGreedyCandidates language observed t k ∩
            language k).Nonempty then
        modifiedGreedyCandidates language observed t k ∩ language k
      else
        modifiedGreedyCandidates language observed t k := by
  rfl

@[simp] theorem modifiedGreedySelected_zero
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) :
    modifiedGreedySelected language observed t 0 = ∅ := by
  rfl

theorem modifiedGreedySelected_succ
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) :
    modifiedGreedySelected language observed t (k + 1) =
      if modifiedGreedyConsistent language observed t k ∧
          (modifiedGreedyCandidates language observed t k ∩
            language k).Nonempty then
        insert k (modifiedGreedySelected language observed t k)
      else
        modifiedGreedySelected language observed t k := by
  rfl

/-- Only indices strictly below the scan length can be selected. -/
theorem modifiedGreedySelected_subset_range
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) :
    modifiedGreedySelected language observed t k ⊆ Finset.range k := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      rw [modifiedGreedySelected_succ]
      split
      · intro j hj
        simp only [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · simp
        · exact Finset.mem_range.mpr
            ((Finset.mem_range.mp (ih hj)).trans
              (Nat.lt_succ_self k))
      · intro j hj
        exact Finset.mem_range.mpr
          ((Finset.mem_range.mp (ih hj)).trans
            (Nat.lt_succ_self k))

/-- Every selected language was consistent with the history available at
the round. -/
theorem modifiedGreedySelected_consistent
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) {j : ℕ}
    (hj : j ∈ modifiedGreedySelected language observed t k) :
    modifiedGreedyConsistent language observed t j := by
  classical
  induction k with
  | zero => simp at hj
  | succ k ih =>
      rw [modifiedGreedySelected_succ] at hj
      by_cases hguard :
          modifiedGreedyConsistent language observed t k ∧
            (modifiedGreedyCandidates language observed t k ∩
              language k).Nonempty
      · rw [if_pos hguard] at hj
        simp only [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact hguard.1
        · exact ih hj
      · rw [if_neg hguard] at hj
        exact ih hj

/-- Exact representation of the candidate set: a point survives iff it is
fresh and belongs to every language selected so far. -/
theorem mem_modifiedGreedyCandidates_iff
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) (x : α) :
    x ∈ modifiedGreedyCandidates language observed t k ↔
      x ∉ GenLimit.Generic.sample observed t ∧
      ∀ j ∈ modifiedGreedySelected language observed t k,
        x ∈ language j := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      rw [modifiedGreedyCandidates_succ,
        modifiedGreedySelected_succ]
      by_cases hguard :
          modifiedGreedyConsistent language observed t k ∧
            (modifiedGreedyCandidates language observed t k ∩
              language k).Nonempty
      · rw [if_pos hguard, if_pos hguard]
        constructor
        · rintro ⟨hcurrent, hxk⟩
          have hold := ih.mp hcurrent
          refine ⟨hold.1, ?_⟩
          intro j hj
          simp only [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hxk
          · exact hold.2 j hj
        · rintro ⟨hfresh, hall⟩
          refine ⟨ih.mpr ⟨hfresh, ?_⟩, ?_⟩
          · intro j hj
            exact hall j (Finset.mem_insert_of_mem hj)
          · exact hall k (Finset.mem_insert_self k _)
      · rw [if_neg hguard, if_neg hguard]
        exact ih

/-- The intersection of the target with a finite collection of earlier
languages.  This is the set whose finite cardinality is measured by the
paper's non-uniform complexity `m(Lᵢ)`. -/
def modifiedGreedyFiniteIntersection
    (language : ℕ → Set α) (target : ℕ)
    (earlier : Finset ℕ) : Set α :=
  {x |
    x ∈ language target ∧
    ∀ j ∈ earlier, x ∈ language j}

/-- Upper-bound form of Definition 5.

`NonuniformComplexityAtMost language target m` says that every finite
intersection of the target with languages whose indices precede `target`
has cardinality at most `m`.  Unlike a literal maximum, this form also
behaves cleanly when there is no finite intersection. -/
def NonuniformComplexityAtMost
    (language : ℕ → Set α) (target m : ℕ) : Prop :=
  ∀ earlier : Finset ℕ,
    earlier ⊆ Finset.range target →
    (modifiedGreedyFiniteIntersection
      language target earlier).Finite →
    Set.ncard (modifiedGreedyFiniteIntersection
      language target earlier) ≤ m

/-- If the target intersection is empty when it is considered, then the
target together with the actually selected earlier languages contains
exactly the already observed points. -/
theorem modifiedGreedyFiniteIntersection_eq_sample_of_empty
    (language : ℕ → Set α) (observed : ℕ → α)
    (target t : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (hempty :
      ¬(modifiedGreedyCandidates language observed t target ∩
        language target).Nonempty) :
    modifiedGreedyFiniteIntersection language target
        (modifiedGreedySelected language observed t target) =
      (↑(GenLimit.Generic.sample observed t) : Set α) := by
  ext x
  constructor
  · intro hx
    by_contra hfresh
    have hcandidate :
        x ∈ modifiedGreedyCandidates language observed t target :=
      (mem_modifiedGreedyCandidates_iff
        language observed t target x).mpr
        ⟨hfresh, hx.2⟩
    exact hempty ⟨x, hcandidate, hx.1⟩
  · intro hx
    obtain ⟨s, hst, hsx⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hx
    refine ⟨?_, ?_⟩
    · rw [← hsx]
      exact hTarget s
    · intro j hj
      rw [← hsx]
      exact
        (modifiedGreedySelected_consistent
          language observed t target hj) s hst

/-- Every scan step can only shrink the current candidate set. -/
theorem modifiedGreedyCandidates_succ_subset
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) :
    modifiedGreedyCandidates language observed t (k + 1) ⊆
      modifiedGreedyCandidates language observed t k := by
  rw [modifiedGreedyCandidates_succ]
  split
  · exact Set.inter_subset_left
  · exact Set.Subset.rfl

/-- Scanning more languages can only shrink the candidate set. -/
theorem modifiedGreedyCandidates_antitone
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) {k m : ℕ} (hkm : k ≤ m) :
    modifiedGreedyCandidates language observed t m ⊆
      modifiedGreedyCandidates language observed t k := by
  induction m, hkm using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ m hkm ih =>
      exact (modifiedGreedyCandidates_succ_subset
        language observed t m).trans ih

/-- Every candidate remains fresh from the observations before the round. -/
theorem modifiedGreedyCandidates_fresh
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) :
    modifiedGreedyCandidates language observed t k ⊆
      {x | x ∉ GenLimit.Generic.sample observed t} := by
  induction k with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
      exact (modifiedGreedyCandidates_succ_subset
        language observed t k).trans ih

/-- On an infinite universe the initial fresh set is nonempty, and every
accepted intersection is explicitly required to remain nonempty. -/
theorem modifiedGreedyCandidates_nonempty
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) :
    (modifiedGreedyCandidates language observed t k).Nonempty := by
  induction k with
  | zero =>
      obtain ⟨x, hx⟩ :=
        exists_fresh_of_infinite (GenLimit.Generic.sample observed t)
      exact ⟨x, hx⟩
  | succ k ih =>
      rw [modifiedGreedyCandidates_succ]
      split
      next h => exact h.2
      next _ => exact ih

/-- The semantic output of Modified-Greedy at zero-based round `t`. -/
noncomputable def modifiedGreedyGenerated
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) : α :=
  Classical.choose
    (modifiedGreedyCandidates_nonempty
      language observed t (t + 1))

/-- The selected output belongs to the final candidate set. -/
theorem modifiedGreedyGenerated_mem
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) :
    modifiedGreedyGenerated language observed t ∈
      modifiedGreedyCandidates language observed t (t + 1) :=
  Classical.choose_spec
    (modifiedGreedyCandidates_nonempty
      language observed t (t + 1))

/-- Modified-Greedy never repeats an earlier observation. -/
theorem modifiedGreedyGenerated_not_mem_sample
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) :
    modifiedGreedyGenerated language observed t ∉
      GenLimit.Generic.sample observed t := by
  exact modifiedGreedyCandidates_fresh language observed t (t + 1)
    (modifiedGreedyGenerated_mem language observed t)

/-- If the target intersection is nonempty when target `i` is scanned, then
every later candidate, and hence the round output, belongs to that target. -/
theorem modifiedGreedyGenerated_mem_target_of_nonempty
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (t i : ℕ)
    (hi : i ≤ t)
    (hconsistent : modifiedGreedyConsistent language observed t i)
    (hnonempty :
      (modifiedGreedyCandidates language observed t i ∩
        language i).Nonempty) :
    modifiedGreedyGenerated language observed t ∈ language i := by
  have hstep :
      modifiedGreedyCandidates language observed t (i + 1) =
        modifiedGreedyCandidates language observed t i ∩
          language i := by
    rw [modifiedGreedyCandidates_succ,
      if_pos ⟨hconsistent, hnonempty⟩]
  have hsubset :
      modifiedGreedyCandidates language observed t (t + 1) ⊆
        modifiedGreedyCandidates language observed t (i + 1) :=
    modifiedGreedyCandidates_antitone language observed t
      (Nat.succ_le_succ hi)
  have hout := hsubset
    (modifiedGreedyGenerated_mem language observed t)
  rw [hstep] at hout
  exact hout.2

/-- Therefore a mistake after the target has entered the scan means that
the target intersection was empty at the instant it was considered. -/
theorem modifiedGreedy_target_intersection_empty_of_mistake
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (t i : ℕ)
    (hi : i ≤ t)
    (hconsistent : modifiedGreedyConsistent language observed t i)
    (hmistake : modifiedGreedyGenerated language observed t ∉ language i) :
    ¬(modifiedGreedyCandidates language observed t i ∩
      language i).Nonempty := by
  intro hnonempty
  exact hmistake
    (modifiedGreedyGenerated_mem_target_of_nonempty
      language observed t i hi hconsistent hnonempty)

/-- If a point starts in the fresh candidate set but is absent after `k`
scan steps, one of the accepted earlier intersections removed it. -/
theorem exists_modifiedGreedy_eliminator
    (language : ℕ → Set α) (observed : ℕ → α)
    (t k : ℕ) {x : α}
    (hfresh : x ∉ GenLimit.Generic.sample observed t)
    (hout : x ∉ modifiedGreedyCandidates language observed t k) :
    ∃ j < k,
      modifiedGreedyConsistent language observed t j ∧
      (modifiedGreedyCandidates language observed t j ∩
        language j).Nonempty ∧
      x ∉ language j := by
  induction k with
  | zero =>
      exact False.elim (hout (by simpa using hfresh))
  | succ k ih =>
      rw [modifiedGreedyCandidates_succ] at hout
      by_cases hguard :
          modifiedGreedyConsistent language observed t k ∧
            (modifiedGreedyCandidates language observed t k ∩
              language k).Nonempty
      · rw [if_pos hguard] at hout
        by_cases hcurrent :
            x ∈ modifiedGreedyCandidates language observed t k
        · refine ⟨k, Nat.lt_succ_self k, hguard.1, hguard.2, ?_⟩
          intro hxLanguage
          exact hout ⟨hcurrent, hxLanguage⟩
        · obtain ⟨j, hj, hc, hn, hxj⟩ := ih hcurrent
          exact ⟨j, hj.trans (Nat.lt_succ_self k), hc, hn, hxj⟩
      · rw [if_neg hguard] at hout
        obtain ⟨j, hj, hc, hn, hxj⟩ := ih hout
        exact ⟨j, hj.trans (Nat.lt_succ_self k), hc, hn, hxj⟩

/-- Exact Section 6.2 charging step.

If the target is `i`, the presentation is injective and target-consistent,
and Modified-Greedy makes a mistake at a round `t ≥ i`, then some earlier
language `j < i` was consistent with every observation before `t` but
rejects the new observation at `t`.  It is therefore permanently eliminated
at that round. -/
theorem modifiedGreedy_mistake_has_earlier_eliminator
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (t : ℕ)
    (hactive : target ≤ t)
    (hmistake :
      modifiedGreedyGenerated language observed t ∉ language target) :
    ∃ j < target,
      modifiedGreedyConsistent language observed t j ∧
      observed t ∉ language j := by
  have htargetConsistent :
      modifiedGreedyConsistent language observed t target := by
    intro s _hs
    exact hTarget s
  have hempty :=
    modifiedGreedy_target_intersection_empty_of_mistake
      language observed t target hactive htargetConsistent hmistake
  have hcurrentObservationFresh :
      observed t ∉ GenLimit.Generic.sample observed t := by
    intro hmem
    obtain ⟨s, hst, hstEq⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hmem
    have : s = t := hInjective hstEq
    omega
  have hnotCandidate :
      observed t ∉
        modifiedGreedyCandidates language observed t target := by
    intro hmem
    exact hempty ⟨observed t, hmem, hTarget t⟩
  obtain ⟨j, hj, hconsistent, _hnonempty, hjRejects⟩ :=
    exists_modifiedGreedy_eliminator
      language observed t target
      hcurrentObservationFresh hnotCandidate
  exact ⟨j, hj, hconsistent, hjRejects⟩

/-- A post-activation mistake can occur only at a round no larger than the
target's non-uniform intersection complexity. -/
theorem modifiedGreedy_mistake_round_le_complexity
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target m : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (hComplexity :
      NonuniformComplexityAtMost language target m)
    (t : ℕ)
    (hactive : target ≤ t)
    (hmistake :
      modifiedGreedyGenerated language observed t ∉ language target) :
    t ≤ m := by
  have htargetConsistent :
      modifiedGreedyConsistent language observed t target := by
    intro s _hs
    exact hTarget s
  have hempty :=
    modifiedGreedy_target_intersection_empty_of_mistake
      language observed t target hactive htargetConsistent hmistake
  let selected :=
    modifiedGreedySelected language observed t target
  let core :=
    modifiedGreedyFiniteIntersection language target selected
  have hselected : selected ⊆ Finset.range target := by
    exact modifiedGreedySelected_subset_range
      language observed t target
  have hcoreEq :
      core = (↑(GenLimit.Generic.sample observed t) : Set α) := by
    exact modifiedGreedyFiniteIntersection_eq_sample_of_empty
      language observed target t hTarget hempty
  have hcoreFinite : core.Finite := by
    rw [hcoreEq]
    exact Finset.finite_toSet _
  have hbound : Set.ncard core ≤ m :=
    hComplexity selected hselected hcoreFinite
  have hsampleCard :
      (GenLimit.Generic.sample observed t).card = t :=
    GenLimit.Generic.sample_card_of_injective observed hInjective t
  have hcoreCard : Set.ncard core = t := by
    rw [hcoreEq, Set.ncard_coe_finset, hsampleCard]
  rwa [hcoreCard] at hbound

/-- Once the target has entered the scan and the number of prior
observations exceeds its finite-intersection complexity, Modified-Greedy
must output inside the target. -/
theorem modifiedGreedyGenerated_mem_target_after_complexity
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target m : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (hComplexity :
      NonuniformComplexityAtMost language target m)
    (t : ℕ)
    (hactive : target ≤ t)
    (hlarge : m < t) :
    modifiedGreedyGenerated language observed t ∈ language target := by
  by_contra hmistake
  have hsmall :=
    modifiedGreedy_mistake_round_le_complexity
      language observed hInjective target m hTarget hComplexity
      t hactive hmistake
  omega

/-- Exact semantic form of Lemma 6.3.

In zero-based notation, target index `target` is considered from round
`target`, and no mistakes occur once the round is also strictly larger than
the non-uniform complexity `m`.  Thus the no-more-mistakes threshold is
`max target (m + 1)`, corresponding to the paper's one-based
`max {i - 1, m(Lᵢ) + 1}` last-mistake bound. -/
theorem lemma_6_3_modifiedGreedy_last_mistake
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target m : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (hComplexity :
      NonuniformComplexityAtMost language target m) :
    LastMistakeBefore
      (countableTargetTrace language
        (modifiedGreedyGenerated language observed) target)
      (max target (m + 1)) := by
  intro t ht
  have hactive : target ≤ t :=
    (Nat.le_max_left target (m + 1)).trans ht
  have hlarge : m < t := by
    exact (Nat.lt_succ_self m).trans_le
      ((Nat.le_max_right target (m + 1)).trans ht)
  have hmem :=
    modifiedGreedyGenerated_mem_target_after_complexity
      language observed hInjective target m hTarget hComplexity
      t hactive hlarge
  simp [countableTargetTrace, hmem]

/-- Any finite collection of post-activation mistake rounds injects into the
earlier language indices. -/
theorem modifiedGreedy_postActivationMistakes_card_le
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (rounds : Finset ℕ)
    (hrounds :
      ∀ t ∈ rounds,
        target ≤ t ∧
        modifiedGreedyGenerated language observed t ∉ language target) :
    rounds.card ≤ target := by
  classical
  have hExists :
      ∀ t, ∃ j,
        t ∈ rounds →
          j < target ∧
          modifiedGreedyConsistent language observed t j ∧
          observed t ∉ language j := by
    intro t
    by_cases ht : t ∈ rounds
    · obtain ⟨j, hj, hc, hr⟩ :=
        modifiedGreedy_mistake_has_earlier_eliminator
          language observed hInjective target hTarget t
          (hrounds t ht).1 (hrounds t ht).2
      exact ⟨j, fun _ => ⟨hj, hc, hr⟩⟩
    · exact ⟨0, fun h => False.elim (ht h)⟩
  let charge : ℕ → ℕ := fun t => Classical.choose (hExists t)
  have hcharge :
      ∀ t, t ∈ rounds →
        charge t < target ∧
        modifiedGreedyConsistent language observed t (charge t) ∧
        observed t ∉ language (charge t) := by
    intro t ht
    exact Classical.choose_spec (hExists t) ht
  have hmaps : Set.MapsTo charge rounds (Finset.range target) := by
    intro t ht
    exact Finset.mem_range.mpr (hcharge t ht).1
  have hinjective : Set.InjOn charge rounds := by
    intro s hs t ht heq
    by_contra hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · have hmem :
          observed s ∈ language (charge t) :=
        (hcharge t ht).2.1 s hlt
      rw [← heq] at hmem
      exact (hcharge s hs).2.2 hmem
    · have hmem :
          observed t ∈ language (charge s) :=
        (hcharge s hs).2.1 t hgt
      rw [heq] at hmem
      exact (hcharge t ht).2.2 hmem
  simpa using
    (Finset.card_le_card_of_injOn charge hmaps hinjective)

/-- Mistake rounds strictly before a finite horizon. -/
noncomputable def modifiedGreedyMistakeRounds
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (target horizon : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range horizon).filter fun t =>
    modifiedGreedyGenerated language observed t ∉ language target

/-- Post-activation mistakes before any horizon are at most the number of
languages preceding the target. -/
theorem modifiedGreedy_postActivationMistakes_le
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (horizon : ℕ) :
    ((modifiedGreedyMistakeRounds
        language observed target horizon).filter
      fun t => target ≤ t).card ≤ target := by
  classical
  apply modifiedGreedy_postActivationMistakes_card_le
    language observed hInjective target hTarget
  intro t ht
  simp only [Finset.mem_filter] at ht
  exact ⟨ht.2, (Finset.mem_filter.mp ht.1).2⟩

/-- The concrete `2 * target` mistake bound before every horizon.

There are at most `target` pre-activation rounds, and the injective charging
argument gives at most `target` later mistakes.  Translating from zero-based
Lean target `target` to one-based paper target `i = target + 1`, this is the
printed `2(i - 1)` bound in Lemma 6.2. -/
theorem modifiedGreedy_totalMistakes_le_two_mul
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (horizon : ℕ) :
    (modifiedGreedyMistakeRounds
      language observed target horizon).card ≤ 2 * target := by
  classical
  let mistakes :=
    modifiedGreedyMistakeRounds language observed target horizon
  let later := mistakes.filter fun t => target ≤ t
  have hsubset :
      mistakes ⊆ Finset.range target ∪ later := by
    intro t ht
    by_cases hti : t < target
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hti)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨ht, Nat.le_of_not_gt hti⟩)
  have hlater : later.card ≤ target := by
    simpa [mistakes, later] using
      modifiedGreedy_postActivationMistakes_le
        language observed hInjective target hTarget horizon
  calc
    mistakes.card ≤ (Finset.range target ∪ later).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.range target).card + later.card :=
      Finset.card_union_le _ _
    _ ≤ target + target := by
      simpa using Nat.add_le_add_left hlater target
    _ = 2 * target := by omega

/-- Trace-level form of the `2(i - 1)` component of Lemma 6.2. -/
theorem lemma_6_2_modifiedGreedy_mistake_bound
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hTarget : ∀ s, observed s ∈ language target) :
    TotalMistakesAtMost
      (countableTargetTrace language
        (modifiedGreedyGenerated language observed) target)
      (2 * target) := by
  intro horizon
  classical
  simpa [mistakeCount, modifiedGreedyMistakeRounds,
    countableTargetTrace] using
    modifiedGreedy_totalMistakes_le_two_mul
      language observed hInjective target hTarget horizon

/-- Full deterministic content of Lemma 6.2.

The total number of mistakes is bounded both by `2 * target` and by the
no-more-mistakes threshold from Lemma 6.3.  Their minimum is the paper's
`min {2(i - 1), max {i - 1, m(Lᵢ) + 1}}` after translating the one-based
paper index `i` to the zero-based Lean index `target = i - 1`. -/
theorem lemma_6_2_modifiedGreedy_complete
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target m : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (hComplexity :
      NonuniformComplexityAtMost language target m) :
    TotalMistakesAtMost
      (countableTargetTrace language
        (modifiedGreedyGenerated language observed) target)
      (min (2 * target) (max target (m + 1))) := by
  have htwice :=
    lemma_6_2_modifiedGreedy_mistake_bound
      language observed hInjective target hTarget
  have hlast :=
    lemma_6_3_modifiedGreedy_last_mistake
      language observed hInjective target m hTarget hComplexity
  have htime :=
    lastMistakeBefore_implies_totalMistakesAtMost hlast
  intro horizon
  exact Nat.le_min.mpr ⟨htwice horizon, htime horizon⟩

end GenLimit.MistakeBounded
