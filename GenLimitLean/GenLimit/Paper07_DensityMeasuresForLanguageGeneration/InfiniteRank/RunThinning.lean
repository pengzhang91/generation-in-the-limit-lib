import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.LongCharge

/-!
# Arbitrary one-point thinning of ordered runs

Kleinberg--Wei's long-run argument removes the first *chronologically seen*
position of each long bad run.  That position need not be the first position
of the run in the target's fixed ordering.  This module therefore uses an
arbitrary thinning certificate rather than deleting a canonically ordered
endpoint.

The certificate pairs every omitted position with an adjacent retained
position, injectively.  It gives the required half-mass bound in every
prefix, with one boundary point, and it accounts explicitly for any finite
set on which the eventual dynamic charge is not yet available.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
namespace RunThinning

/-- Positions, in the fixed ordering of `K`, occupied by strings of `Long`. -/
def orderedPositions (K : OrderedLanguage) (Long : Language) : Set ℕ :=
  K.enumeration ⁻¹' Long

/-- Undirected adjacency in the fixed ordering. -/
def Adjacent (i j : ℕ) : Prop :=
  i + 1 = j ∨ j + 1 = i

/-- Two positions belong to the same maximal consecutive `P`-run exactly
when the whole closed interval between them lies in `P`. -/
def SameRun (P : Set ℕ) (i j : ℕ) : Prop :=
  ∀ k, min i j ≤ k → k ≤ max i j → k ∈ P

/-- Every maximal consecutive `P`-run is non-singleton. -/
def HasNoSingletonRuns (P : Set ℕ) : Prop :=
  ∀ ⦃i : ℕ⦄, i ∈ P → ∃ j, j ∈ P ∧ Adjacent i j

/-- No maximal consecutive `P`-run contains two omitted positions. -/
def AtMostOneOmittedPerRun (P retained : Set ℕ) : Prop :=
  ∀ ⦃i j : ℕ⦄,
    i ∈ P → i ∉ retained →
    j ∈ P → j ∉ retained →
    SameRun P i j → i = j

/-- Two `P`-positions adjacent to one common `P`-position lie in the same
maximal consecutive run. -/
theorem sameRun_of_common_adjacent
    {P : Set ℕ} {i j m : ℕ}
    (hi : i ∈ P) (hj : j ∈ P) (hm : m ∈ P)
    (him : Adjacent i m) (hjm : Adjacent j m) :
    SameRun P i j := by
  intro k hkLower hkUpper
  rcases him with him | hmi <;> rcases hjm with hjm | hmj
  · have hij : i = j := by omega
    subst j
    have hk : k = i := by omega
    simpa [hk] using hi
  · have horder : i ≤ j := by omega
    rw [min_eq_left horder] at hkLower
    rw [max_eq_right horder] at hkUpper
    have hk : k = i ∨ k = m ∨ k = j := by omega
    rcases hk with rfl | rfl | rfl
    · exact hi
    · exact hm
    · exact hj
  · have horder : j ≤ i := by omega
    rw [min_eq_right horder] at hkLower
    rw [max_eq_left horder] at hkUpper
    have hk : k = j ∨ k = m ∨ k = i := by omega
    rcases hk with rfl | rfl | rfl
    · exact hj
    · exact hm
    · exact hi
  · have hij : i = j := by omega
    subst j
    have hk : k = i := by omega
    simpa [hk] using hi

/-- Adjacent `P`-positions lie in the same maximal consecutive run. -/
theorem sameRun_of_adjacent
    {P : Set ℕ} {i j : ℕ}
    (hi : i ∈ P) (hj : j ∈ P) (hij : Adjacent i j) :
    SameRun P i j := by
  intro k hkLower hkUpper
  rcases hij with hij | hji
  · have horder : i ≤ j := by omega
    rw [min_eq_left horder] at hkLower
    rw [max_eq_right horder] at hkUpper
    have hk : k = i ∨ k = j := by omega
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  · have horder : j ≤ i := by omega
    rw [min_eq_right horder] at hkLower
    rw [max_eq_left horder] at hkUpper
    have hk : k = j ∨ k = i := by omega
    rcases hk with rfl | rfl
    · exact hj
    · exact hi

/-- A structural certificate for thinning arbitrary non-singleton ordered
runs.

Every omitted point has an adjacent retained mate, and different omissions
have different mates.  Deleting one point from each disjoint non-singleton
consecutive run yields precisely this local accounting obligation. -/
structure Certificate (P retained : Set ℕ) where
  retained_subset : retained ⊆ P
  mate : ℕ → ℕ
  omitted_mate_mem :
    ∀ ⦃i : ℕ⦄, i ∈ P → i ∉ retained → mate i ∈ retained
  omitted_mate_adjacent :
    ∀ ⦃i : ℕ⦄, i ∈ P → i ∉ retained →
      mate i + 1 = i ∨ i + 1 = mate i
  omitted_mate_injective :
    Set.InjOn mate (P \ retained)

/-- Natural maximal-run hypotheses produce the adjacent-mate certificate.

This is the semantic bridge for the paper's deletion rule: the deleted point
may be selected by chronological presentation order, since no hypothesis
relates that choice to the fixed ordering within its run. -/
noncomputable def Certificate.ofMaximalRuns
    {P retained : Set ℕ}
    (hsubset : retained ⊆ P)
    (hNoSingleton : HasNoSingletonRuns P)
    (hAtMostOne : AtMostOneOmittedPerRun P retained) :
    Certificate P retained := by
  classical
  have hexists :
      ∀ i : ℕ, ∃ j : ℕ,
        i ∈ P → i ∉ retained → j ∈ retained ∧ Adjacent i j := by
    intro i
    by_cases hi : i ∈ P ∧ i ∉ retained
    · rcases hNoSingleton hi.1 with ⟨j, hjP, hij⟩
      have hjRetained : j ∈ retained := by
        by_contra hjNotRetained
        have hsame : SameRun P i j :=
          sameRun_of_adjacent hi.1 hjP hij
        have heq : i = j :=
          hAtMostOne hi.1 hi.2 hjP hjNotRetained hsame
        subst j
        rcases hij with hij | hji <;> omega
      exact ⟨j, fun _ _ => ⟨hjRetained, hij⟩⟩
    · exact ⟨0, fun hiP hiNot => (hi ⟨hiP, hiNot⟩).elim⟩
  choose mate hmate using hexists
  refine
    { retained_subset := hsubset
      mate := mate
      omitted_mate_mem := ?_
      omitted_mate_adjacent := ?_
      omitted_mate_injective := ?_ }
  · intro i hiP hiNot
    exact (hmate i hiP hiNot).1
  · intro i hiP hiNot
    rcases (hmate i hiP hiNot).2 with hnext | hprevious
    · exact Or.inr hnext
    · exact Or.inl hprevious
  · intro i hi j hj heq
    have hmi := hmate i hi.1 hi.2
    have hmj := hmate j hj.1 hj.2
    have hmP : mate i ∈ P := hsubset hmi.1
    have hjAdjacent : Adjacent j (mate i) := by
      simpa [heq] using hmj.2
    exact hAtMostOne hi.1 hi.2 hj.1 hj.2
      (sameRun_of_common_adjacent
        hi.1 hj.1 hmP hmi.2 hjAdjacent)

/-- Omitted positions in `[0,n)` inject into retained positions in `[0,n)`,
apart from the sole possible mate at the right boundary `n`. -/
theorem omittedPrefix_le_retainedPrefix_add_one
    {P retained : Set ℕ} (C : Certificate P retained) (n : ℕ) :
    positionPrefixCount (P \ retained) n ≤
      positionPrefixCount retained n + 1 := by
  classical
  let source : Finset ℕ :=
    (Finset.range n).filter fun i => i ∈ P \ retained
  let inside : Finset ℕ :=
    (Finset.range n).filter fun i => i ∈ retained
  let target : Finset ℕ := insert n inside
  have hmaps : Set.MapsTo C.mate source target := by
    intro i hi
    have hi' : i < n ∧ i ∈ P ∧ i ∉ retained := by
      simpa [source] using hi
    have hmate : C.mate i ∈ retained :=
      C.omitted_mate_mem hi'.2.1 hi'.2.2
    by_cases hlt : C.mate i < n
    · simp [target, inside, hlt, hmate]
    · have heq : C.mate i = n := by
        rcases C.omitted_mate_adjacent hi'.2.1 hi'.2.2 with
          hprevious | hnext
        · omega
        · omega
      simp [target, heq]
  have hinj : Set.InjOn C.mate source := by
    intro i hi j hj hij
    apply C.omitted_mate_injective
    · have hi' : i < n ∧ i ∈ P ∧ i ∉ retained := by
        simpa [source] using hi
      exact hi'.2
    · have hj' : j < n ∧ j ∈ P ∧ j ∉ retained := by
        simpa [source] using hj
      exact hj'.2
    · exact hij
  have hcard : source.card ≤ target.card :=
    card_le_of_injective_charge source target C.mate hmaps hinj
  have hnInside : n ∉ inside := by
    simp [inside]
  have htarget : target.card = inside.card + 1 := by
    simp [target, hnInside]
  simpa [source, inside, target, positionPrefixCount, htarget] using hcard

/-- A certified arbitrary one-point-per-run thinning retains at least half
of every ordered prefix, up to one boundary point. -/
theorem positionPrefixCount_le_two_retained_add_one
    {P retained : Set ℕ} (C : Certificate P retained) (n : ℕ) :
    positionPrefixCount P n ≤
      2 * positionPrefixCount retained n + 1 := by
  classical
  let all : Finset ℕ :=
    (Finset.range n).filter fun i => i ∈ P
  let kept : Finset ℕ :=
    (Finset.range n).filter fun i => i ∈ retained
  let omitted : Finset ℕ :=
    (Finset.range n).filter fun i => i ∈ P \ retained
  have hpartition : all = kept ∪ omitted := by
    ext i
    simp only [all, kept, omitted, Finset.mem_filter, Finset.mem_range,
      Finset.mem_union, Set.mem_diff]
    constructor
    · intro hi
      by_cases hir : i ∈ retained
      · exact Or.inl ⟨hi.1, hir⟩
      · exact Or.inr ⟨hi.1, hi.2, hir⟩
    · rintro (hi | hi)
      · exact ⟨hi.1, C.retained_subset hi.2⟩
      · exact ⟨hi.1, hi.2.1⟩
  have hdisjoint : Disjoint kept omitted := by
    rw [Finset.disjoint_left]
    intro i hiKept hiOmitted
    have hiKept' : i < n ∧ i ∈ retained := by
      simpa [kept] using hiKept
    have hiOmitted' : i < n ∧ i ∈ P ∧ i ∉ retained := by
      simpa [omitted] using hiOmitted
    exact hiOmitted'.2.2 hiKept'.2
  have hsplit : all.card = kept.card + omitted.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
  have homitted : omitted.card ≤ kept.card + 1 := by
    simpa [omitted, kept, positionPrefixCount] using
      omittedPrefix_le_retainedPrefix_add_one C n
  change all.card ≤ 2 * kept.card + 1
  omega

/-- Removing a finite exceptional set costs at most its cardinality in every
prefix count. -/
theorem positionPrefixCount_le_diff_finset_add_card
    (retained : Set ℕ) (exceptions : Finset ℕ) (n : ℕ) :
    positionPrefixCount retained n ≤
      positionPrefixCount (retained \ (exceptions : Set ℕ)) n +
        exceptions.card := by
  classical
  let all : Finset ℕ :=
    (Finset.range n).filter fun i => i ∈ retained
  let kept : Finset ℕ :=
    (Finset.range n).filter
      fun i => i ∈ retained \ (exceptions : Set ℕ)
  have hsub : all ⊆ kept ∪ exceptions := by
    intro i hi
    have hi' : i < n ∧ i ∈ retained := by
      simpa [all] using hi
    by_cases hiex : i ∈ exceptions
    · exact Finset.mem_union_right kept hiex
    · apply Finset.mem_union_left exceptions
      simpa [kept, hiex] using hi'
  calc
    positionPrefixCount retained n = all.card := by
      simp [all, positionPrefixCount]
    _ ≤ (kept ∪ exceptions).card :=
      Finset.card_le_card hsub
    _ ≤ kept.card + exceptions.card :=
      Finset.card_union_le kept exceptions
    _ = positionPrefixCount
          (retained \ (exceptions : Set ℕ)) n +
          exceptions.card := by
      simp [kept, positionPrefixCount]

/-- Arbitrary run thinning followed by removal of finitely many exceptional
positions.  The safe error is `2 * |exceptions| + 1`. -/
theorem positionPrefixCount_le_two_diff_finset_add_error
    {P retained : Set ℕ} (C : Certificate P retained)
    (exceptions : Finset ℕ) (n : ℕ) :
    positionPrefixCount P n ≤
      2 * positionPrefixCount
          (retained \ (exceptions : Set ℕ)) n +
        (2 * exceptions.card + 1) := by
  have hhalf :=
    positionPrefixCount_le_two_retained_add_one C n
  have hremove :=
    positionPrefixCount_le_diff_finset_add_card
      retained exceptions n
  omega

/-- Fixed-order prefix counts are position counts of the corresponding
preimage. -/
theorem prefixCount_eq_positionPrefixCount_orderedPositions
    (K : OrderedLanguage) (Long : Language) (n : ℕ) :
    K.prefixCount Long n =
      positionPrefixCount (orderedPositions K Long) n := by
  classical
  simp [OrderedLanguage.prefixCount, positionPrefixCount,
    orderedPositions]

end RunThinning

namespace LongBadCharge

/-- Construct a long-bad charge from an arbitrary-run thinning certificate,
a finite exceptional set, and the paper-specific injective backward output
charge.  All static thinning and finite-prefix accounting are discharged. -/
noncomputable def ofRunThinning
    (K : OrderedLanguage) (Output Long : Language)
    (retained : Set ℕ)
    (C :
      RunThinning.Certificate
        (RunThinning.orderedPositions K Long) retained)
    (exceptions : Finset ℕ)
    (charge : ℕ → ℕ)
    (charge_earlier :
      ∀ ⦃i : ℕ⦄,
        i ∈ retained \ (exceptions : Set ℕ) → charge i < i)
    (charge_output :
      ∀ ⦃i : ℕ⦄,
        i ∈ retained \ (exceptions : Set ℕ) →
          K.enumeration (charge i) ∈ Output)
    (charge_injective :
      Set.InjOn charge (retained \ (exceptions : Set ℕ))) :
    LongBadCharge K Output Long where
  retained := retained \ (exceptions : Set ℕ)
  charge := charge
  longError := 2 * exceptions.card + 1
  retained_long := by
    intro i hi
    exact C.retained_subset hi.1
  half_mass := Filter.Eventually.of_forall fun n => by
    rw [RunThinning.prefixCount_eq_positionPrefixCount_orderedPositions]
    exact
      RunThinning.positionPrefixCount_le_two_diff_finset_add_error
        C exceptions n
  charge_earlier := charge_earlier
  charge_output := charge_output
  charge_injective := charge_injective

/-- Initial-cutoff specialization.  Discarding every retained position below
`cutoff` yields the explicit safe error `2 * cutoff + 1`. -/
noncomputable def ofRunThinningAfter
    (K : OrderedLanguage) (Output Long : Language)
    (retained : Set ℕ)
    (C :
      RunThinning.Certificate
        (RunThinning.orderedPositions K Long) retained)
    (cutoff : ℕ)
    (charge : ℕ → ℕ)
    (charge_earlier :
      ∀ ⦃i : ℕ⦄, i ∈ retained → cutoff ≤ i → charge i < i)
    (charge_output :
      ∀ ⦃i : ℕ⦄, i ∈ retained → cutoff ≤ i →
        K.enumeration (charge i) ∈ Output)
    (charge_injective :
      Set.InjOn charge {i | i ∈ retained ∧ cutoff ≤ i}) :
    LongBadCharge K Output Long := by
  let certificate :=
    ofRunThinning
      K Output Long retained C (Finset.range cutoff) charge
      (by
        intro i hi
        exact charge_earlier hi.1 (by simpa using hi.2))
      (by
        intro i hi
        exact charge_output hi.1 (by simpa using hi.2))
      (by
        intro i hi j hj hij
        apply charge_injective
        · exact ⟨hi.1, by simpa using hi.2⟩
        · exact ⟨hj.1, by simpa using hj.2⟩
        · exact hij)
  simpa using certificate

end LongBadCharge
end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
