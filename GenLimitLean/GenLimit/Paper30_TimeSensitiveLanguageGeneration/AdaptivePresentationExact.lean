import GenLimit.Paper30_TimeSensitiveLanguageGeneration.AdaptivePresentation
import Mathlib.Data.List.GetD

/-!
# Exactness of the sparse adaptive presentation

The ordinary least-unused rounds enumerate every target point not claimed by
the generator.  The exponentially sparse catch-up rounds enumerate every
target point that the generator did claim.  Together these two mechanisms
make the adaptive stream an exact presentation of the ordered target.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei

theorem adaptiveGCGRun_outputs_getD
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {n t : ℕ} (hnt : n < t) (fallback : ℕ) :
    (adaptiveGCGRun F O t).outputs.getD n fallback =
      adaptiveGCGOutput F O n := by
  rw [adaptiveGCGRun_outputs_eq]
  rw [List.getD_eq_getElem _ _ (by simpa using hnt)]
  simp

theorem adaptivePresentation_eq_least_of_not_catchup
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {t : ℕ} (hcatch : ¬IsCatchupRound t) :
    adaptivePresentation F O t =
      leastUnusedTarget O (adaptiveUsed (adaptiveGCGRun F O t)) := by
  classical
  simp [adaptivePresentation, adaptiveAnnouncement, hcatch]

theorem adaptivePresentation_not_mem_used_of_not_catchup
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {t : ℕ} (hcatch : ¬IsCatchupRound t) :
    adaptivePresentation F O t ∉ adaptiveUsed (adaptiveGCGRun F O t) := by
  rw [adaptivePresentation_eq_least_of_not_catchup F O hcatch]
  exact leastUnusedTarget_fresh O _

theorem adaptivePresentation_ne_prior_of_not_catchup
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {s t : ℕ} (hst : s < t) (hcatch : ¬IsCatchupRound t) :
    adaptivePresentation F O t ≠ adaptivePresentation F O s := by
  intro heq
  apply adaptivePresentation_not_mem_used_of_not_catchup F O hcatch
  apply Finset.mem_union_left
  rw [adaptiveGCGRun_observations_eq]
  simp
  exact ⟨s, hst, heq.symm⟩

theorem odd_not_catchup (k : ℕ) :
    ¬IsCatchupRound (2 * k + 1) := by
  rintro ⟨n, hn⟩
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by
    simp [pow_succ, Nat.mul_comm]
  omega

theorem odd_adaptivePresentation_injective
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    Function.Injective
      (fun k => adaptivePresentation F O (2 * k + 1)) := by
  intro a b hab
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · have htime : 2 * a + 1 < 2 * b + 1 := by omega
    exfalso
    exact (adaptivePresentation_ne_prior_of_not_catchup F O htime
      (odd_not_catchup b)) hab.symm
  · rfl
  · have htime : 2 * b + 1 < 2 * a + 1 := by omega
    exfalso
    exact (adaptivePresentation_ne_prior_of_not_catchup F O htime
      (odd_not_catchup a)) hab

/-- The repaired GCG is fresh against the current and all earlier adaptive
announcements, and never repeats one of its own outputs. -/
theorem adaptiveGCG_freshPlay
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    FreshPlay (adaptivePresentation F O) (adaptiveGCGOutput F O) := by
  have hout : adaptiveGCGOutput F O =
      totalizedGCGOutput F (adaptivePresentation F O) := by
    funext t
    exact adaptiveGCGOutput_eq_totalized F O t
  rw [hout]
  exact totalizedGCG_freshPlay F (adaptivePresentation F O)

theorem adaptiveGCGOutput_injective
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    Function.Injective (adaptiveGCGOutput F O) :=
  (adaptiveGCG_freshPlay F O).generator_injective

theorem adaptivePresentation_at_scheduled_output
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (n : ℕ)
    (hmem : adaptiveGCGOutput F O n ∈ O.carrier) :
    adaptivePresentation F O (2 ^ (n + 1)) =
      adaptiveGCGOutput F O n := by
  classical
  have hcatch : IsCatchupRound (2 ^ (n + 1)) := ⟨n, rfl⟩
  have hnt : n < 2 ^ (n + 1) := index_lt_scheduled_time n
  have hcandidate :
      catchupCandidate O (adaptiveGCGRun F O (2 ^ (n + 1)))
          (2 ^ (n + 1)) = adaptiveGCGOutput F O n := by
    simp only [catchupCandidate, catchupIndex_scheduled]
    exact adaptiveGCGRun_outputs_getD F O hnt _
  simp [adaptivePresentation, adaptiveAnnouncement, hcatch,
    hcandidate, hmem]

theorem target_rank_unused_of_never_announced_or_generated
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {j t : ℕ}
    (hadv : ∀ q, adaptivePresentation F O q ≠ O.enumeration j)
    (hgen : ∀ q, adaptiveGCGOutput F O q ≠ O.enumeration j) :
    UnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)) j := by
  intro hused
  rcases Finset.mem_union.mp hused with hobserved | houtput
  · rw [adaptiveGCGRun_observations_eq] at hobserved
    simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hobserved
    obtain ⟨q, hqt, hq⟩ := hobserved
    exact hadv q hq
  · rw [adaptiveGCGRun_outputs_eq] at houtput
    simp only [List.mem_toFinset, List.mem_map, List.mem_range] at houtput
    obtain ⟨q, hqt, hq⟩ := houtput
    exact hgen q hq

theorem odd_adaptivePresentation_mem_lower_prefix_of_never
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {j k : ℕ}
    (hadv : ∀ q, adaptivePresentation F O q ≠ O.enumeration j)
    (hgen : ∀ q, adaptiveGCGOutput F O q ≠ O.enumeration j) :
    adaptivePresentation F O (2 * k + 1) ∈
      targetPrefix O.enumeration j := by
  let t := 2 * k + 1
  have hnotCatch : ¬IsCatchupRound t := odd_not_catchup k
  have hjUnused :
      UnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)) j :=
    target_rank_unused_of_never_announced_or_generated F O hadv hgen
  have hle :
      leastUnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)) ≤ j :=
    leastUnusedTargetRank_min O _ hjUnused
  have hne :
      leastUnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)) ≠ j := by
    intro heq
    apply hadv t
    rw [adaptivePresentation_eq_least_of_not_catchup F O hnotCatch]
    exact congrArg O.enumeration heq
  change adaptivePresentation F O (2 * k + 1) ∈
    sequencePrefix O.enumeration j
  rw [mem_sequencePrefix_iff]
  refine ⟨leastUnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)),
    lt_of_le_of_ne hle hne, ?_⟩
  rw [adaptivePresentation_eq_least_of_not_catchup F O hnotCatch]
  rfl

/-- Every target point not generated by the repaired GCG must occur on an
ordinary least-unused adversary round. -/
theorem target_mem_adaptivePresentation_of_not_generated
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {x : ℕ} (hx : x ∈ O.carrier)
    (hgen : x ∉ Set.range (adaptiveGCGOutput F O)) :
    x ∈ Set.range (adaptivePresentation F O) := by
  obtain ⟨j, hj⟩ : ∃ j, O.enumeration j = x := by
    rw [← O.range_enumeration] at hx
    exact hx
  by_contra hadvRange
  have hadv : ∀ q, adaptivePresentation F O q ≠ O.enumeration j := by
    intro q hq
    apply hadvRange
    exact ⟨q, hq.trans hj⟩
  have hgen' : ∀ q, adaptiveGCGOutput F O q ≠ O.enumeration j := by
    intro q hq
    apply hgen
    exact ⟨q, hq.trans hj⟩
  have hinfinite :
      (Set.range fun k => adaptivePresentation F O (2 * k + 1)).Infinite :=
    Set.infinite_range_of_injective
      (odd_adaptivePresentation_injective F O)
  have hsubset :
      Set.range (fun k => adaptivePresentation F O (2 * k + 1)) ⊆
        (↑(targetPrefix O.enumeration j) : Set ℕ) := by
    rintro _ ⟨k, rfl⟩
    exact odd_adaptivePresentation_mem_lower_prefix_of_never F O hadv hgen'
  exact (targetPrefix O.enumeration j).finite_toSet.not_infinite
    (hinfinite.mono hsubset)

/-- The sparse adaptive stream is an exact presentation of the target. -/
theorem adaptivePresentation_presents
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    Presents (adaptivePresentation F O) O.carrier := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact adaptivePresentation_mem_target F O t
  · intro x hx
    by_cases hgen : x ∈ Set.range (adaptiveGCGOutput F O)
    · obtain ⟨n, hn⟩ := hgen
      refine ⟨2 ^ (n + 1), ?_⟩
      rw [adaptivePresentation_at_scheduled_output F O n]
      · exact hn
      · simpa [hn] using hx
    · exact target_mem_adaptivePresentation_of_not_generated F O hx hgen

end GenLimit.TimeSensitive
