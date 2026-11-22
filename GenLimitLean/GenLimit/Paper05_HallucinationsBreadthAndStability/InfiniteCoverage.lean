import GenLimit.Paper01_LanguageGeneration.DistinctOutputs
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.BreadthClaim52
import GenLimit.Paper05_HallucinationsBreadthAndStability.StabilityGap
import GenLimit.Support.FullSupportDistribution

/-! # Infinite coverage in Sections 8.1 and 8.2 -/

namespace GenLimit.BreadthCharacterizations

/-- At a fixed training history, the random seed raises the initial cutoff
of the finite membership-query scan. -/
def coverageDraw (O : OracleFamily) (xs : List ℕ) (seed : ℕ) :=
  KM.DistinctOutputs.queryStep O (Generic.historyThenFallback xs 0) xs.length seed

noncomputable def coverageLaw (O : OracleFamily) (xs : List ℕ) : PMF ℕ :=
  DiscreteIID.positiveGeometric.map (coverageDraw O xs)

theorem coverageLaw_support (O : OracleFamily) (xs : List ℕ) :
    (coverageLaw O xs).support = Set.range (coverageDraw O xs) := by
  ext x
  simp only [coverageLaw, PMF.support_map, Set.mem_image, Set.mem_range]
  exact ⟨fun ⟨r,_,hr⟩ => ⟨r,hr⟩, fun ⟨r,hr⟩ => ⟨r,DiscreteIID.positiveGeometric_support _,hr⟩⟩

private theorem draw_bounds (O : OracleFamily) (xs : List ℕ) (r : ℕ) :
    max (r+1) ((sample (Generic.historyThenFallback xs 0) xs.length).sup id + 1) ≤ coverageDraw O xs r := by
  unfold coverageDraw KM.DistinctOutputs.queryStep
  split
  · exact Nat.le_sub_one_of_lt (O.roundCounter_gt _ _)
  · exact le_rfl

private theorem draw_infinite (O : OracleFamily) (xs : List ℕ) :
    (Set.range (coverageDraw O xs)).Infinite := by
  intro hf
  obtain ⟨b,hb⟩ := hf.bddAbove
  have hh := hb (Set.mem_range_self b)
  have hlt : b < coverageDraw O xs b := (Nat.le_max_left ..).trans (draw_bounds O xs b)
  omega

private theorem observed_eq (s : ℕ → ℕ) (t : ℕ) :
    sample (Generic.historyThenFallback (textPrefix s t) 0) t = sample s t := by
  apply sample_eq_of_eq_on_prefix
  intro n hn
  simp [Generic.historyThenFallback, textPrefix, hn, List.get_eq_getElem]

/-- Proposition 8.4 with a normalized law and membership access alone. -/
theorem proposition_8_4 (O : OracleFamily) :
    IsInfiniteCoverageGenerator (fun xs => (coverageLaw O xs).support) O.language := by
  intro z s hp
  obtain ⟨T,hT⟩ := target_eventually_critical (C := O.language) hp
  refine ⟨max T (z+1), fun t ht => ?_⟩
  let xs := textPrefix s t
  let s' := Generic.historyThenFallback xs 0
  have he : sample s' t = sample s t := observed_eq s t
  have hg : Generic.sample s t = sample s t := by
    ext x; rw [Generic.mem_sample_iff, mem_sample_iff]
  have hz : Critical O.language s' t z := by
    simpa only [Critical, Consistent, he] using hT t ((Nat.le_max_left ..).trans ht)
  have hzt : z < t := (Nat.le_max_right ..).trans ht
  have hc : O.HasConsistent s' t :=
    ⟨z,O.mem_consistentCandidates.mpr ⟨hzt,O.consistentAt_iff.mpr hz.1⟩⟩
  change (coverageLaw O xs).support ⊆ O.language z ∧ Disjoint (coverageLaw O xs).support
    (↑(Generic.sample s t) : Set ℕ) ∧ (coverageLaw O xs).support.Infinite
  rw [coverageLaw_support]
  refine ⟨?_, Set.disjoint_left.mpr ?_, draw_infinite O xs⟩
  · rintro x ⟨r,rfl⟩
    let b := max (r+1) ((sample s' t).sup id + 1)
    let q := O.roundCounter s' t hc b
    have hcrit := critical_finitelyCritical hz q
    have hm := O.mem_finitePrefix.mp (O.roundCounter_output_mem_selectedPrefix hc b)
    have hle := O.selected_max hc hzt (O.finitelyCriticalAt_iff.mpr hcrit)
    have hr : coverageDraw O xs r = q-1 := by simp [coverageDraw, KM.DistinctOutputs.queryStep, xs, s', hc, q, b]
    rw [hr]
    exact finitelyCritical_prefix_subset hle hcrit (O.selected_finitelyCritical hc) _ hm.1 hm.2
  · rintro x ⟨r,rfl⟩ hseen
    have hs : coverageDraw O xs r ∈ sample s' xs.length := by simpa only [show xs.length = t from textPrefix_length s t, he, hg, Finset.mem_coe] using hseen
    have hle := Finset.le_sup (s := sample s' xs.length) (f := id) hs
    exact (Nat.not_lt_of_ge hle) ((Nat.le_max_right ..).trans (draw_bounds O xs r))

/-- Theorem 8.7 with precisely Example 8.6's full language and co-singletons. -/
theorem theorem_8_7 :
    WeakAngluinCondition CharikarPabbaraju.coSingletonNatFamily ∧
    ¬ ∃ G, IsStableGenerator G CharikarPabbaraju.coSingletonNatFamily ∧
      IsInfiniteCoverageGenerator G CharikarPabbaraju.coSingletonNatFamily := by
  refine ⟨?_, no_stable_infiniteCoverage_for_infinite_family _ CharikarPabbaraju.coSingletonNatFamily_infinite⟩
  intro i
  refine ⟨∅, by simp, ?_⟩
  intro j _ _
  cases j with
  | zero => simp [CharikarPabbaraju.coSingletonNatFamily]
  | succ j =>
    apply (Set.finite_singleton j).subset
    rintro x ⟨_,h⟩
    simpa [CharikarPabbaraju.coSingletonNatFamily] using h

end GenLimit.BreadthCharacterizations
