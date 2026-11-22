import GenLimit.Paper05_HallucinationsBreadthAndStability.SharedSupport
import GenLimit.Paper05_HallucinationsBreadthAndStability.StableAndUnambiguous

/-! # The finite-hallucination and unrestricted columns of Figures 3 and 4

Rows count target words missed by the support. These tables count observed
words as well. The rightmost column is a permission to hallucinate without
a bound. The literal requirement of infinitely many errors is also checked.
-/

namespace GenLimit.BreadthCharacterizations

/-- With weak tell-tales a single hypothesis stabilizes to a superset of
the target with only finitely many extra words. -/
theorem stable_superset_of_weak {F : Generic.LanguageFamily α} (hw : WeakAngluinCondition F) :
    ∃ G : SupportAlgorithm α, IsStableGenerator G F ∧
      EventuallyGeneratesWith (fun xs K ↦ K ⊆ G xs ∧ (G xs \ K).Finite) F := by
  classical
  choose T ht using hw
  let A := fun i (_ : ℕ) ↦ T i
  let select := Angluin.semanticLearner F A
  have converge (z : ℕ) (s : ℕ → α) (hp : Generic.Presents s (F z)) :
      ∃ j, F z ⊆ F j ∧ (F j \ F z).Finite ∧ ∃ N, ∀ t ≥ N, select (textPrefix s t) = j := by
    let good := fun i ↦ (T i : Set α) ⊆ F z ∧ F z ⊆ F i
    have ex : ∃ i, good i := ⟨z,(ht z).1,Set.Subset.rfl⟩
    let j := Nat.find ex
    have hj : good j := Nat.find_spec ex
    have finite : (F j \ F z).Finite := by
      rcases eq_or_lt_of_le hj.2 with e | h
      · simp [e]
      · exact (ht j).2 z hj.1 h
    have sampleSub (t) : (Generic.sample s t : Set α) ⊆ F z :=
      fun _ h ↦ Generic.mem_language_of_mem_sample_of_presents hp h
    obtain ⟨M,hM⟩ := Generic.finset_eventually_subset_sample hp (T j) hj.1
    have exclude (i) (hi : i < j) : ∃ N, ∀ t ≥ N, ¬ Angluin.StageEligible F A (textPrefix s t) i := by
      by_cases h : F z ⊆ F i
      · refine ⟨0,fun t _ he ↦ Nat.find_min ex hi ⟨?_,h⟩⟩
        have htell : T i ⊆ Generic.sample s t := by simpa only [Angluin.historySample_textPrefix] using he.2.1
        exact fun x hx ↦ sampleSub t (htell hx)
      · obtain ⟨x,hx,hout⟩ := Set.not_subset.mp h
        obtain ⟨N,hN⟩ := Generic.eventually_mem_sample_of_presents hp hx
        refine ⟨N,fun t ht he ↦ hout (he.2.2 ?_)⟩
        simpa only [Angluin.historySample_textPrefix] using hN t ht
    obtain ⟨N,hN⟩ := Angluin.eventually_all_lt exclude
    refine ⟨j,hj.2,finite,max j (max N M),fun t bound ↦ ?_⟩
    have eligible : Angluin.StageEligible F A (textPrefix s t) j := by
      rw [Angluin.StageEligible,textPrefix_length,Angluin.historySample_textPrefix]
      exact ⟨by omega,hM.trans (Generic.sample_mono (by omega : M ≤ t)),(sampleSub t).trans hj.2⟩
    exact le_antisymm (Angluin.semanticLearner_le_of_eligible eligible)
      (le_of_not_gt (fun h ↦ hN t (by omega) _ h (Angluin.semanticLearner_eligible ⟨j,eligible⟩)))
  refine ⟨fun xs ↦ F (select xs),?_,?_⟩
  · intro z s hp
    obtain ⟨j,_,_,N,hN⟩ := converge z s hp
    exact ⟨N,fun t u ht hu ↦ congrArg F ((hN t ht).trans (hN u hu).symm)⟩
  · intro z s hp
    obtain ⟨j,hsub,hfin,N,hN⟩ := converge z s hp
    refine ⟨N, fun t ht ↦ ?_⟩
    change F z ⊆ F (select (textPrefix s t)) ∧ (F (select (textPrefix s t)) \ F z).Finite
    rw [hN t ht]
    exact ⟨hsub,hfin⟩

/-- The upper two rows in the finite-hallucination column. The exact row
requires containment of the whole target, the approximate row permits a
finite set of omissions. Either row can additionally require stability. -/
def FiniteErrorCell (F : Generic.LanguageFamily α) (stable exact : Bool) : Prop :=
  ∃ G : SupportAlgorithm α, (stable = true → IsStableGenerator G F) ∧
    EventuallyGeneratesWith (fun xs K ↦
      (if exact then K ⊆ G xs else (K \ G xs).Finite) ∧ (G xs \ K).Finite) F

theorem figures_3_4_finite_hallucinations [Countable α] {F : Generic.LanguageFamily α}
    (hi : ∀ i, (F i).Infinite) (stable exact : Bool) :
    FiniteErrorCell F stable exact ↔ WeakAngluinCondition F := by
  constructor
  · rintro ⟨G,_,works⟩
    apply theorem_3_10 (fun i ↦ (hi i).nonempty) (hP := works)
    intro xs i j _ _ large small
    have missing : (F i \ G xs).Finite := by
      cases exact with
      | false => exact large.1
      | true => exact Set.finite_empty.subset (fun x hx ↦ (hx.2 (large.1 hx.1)).elim)
    apply (missing.union small.2).subset
    intro x hx
    by_cases h : x ∈ G xs
    · exact Or.inr ⟨h,hx.2⟩
    · exact Or.inl ⟨hx.1,h⟩
  · intro hw
    obtain ⟨G,st,works⟩ := stable_superset_of_weak hw
    refine ⟨G,fun _ ↦ st,fun z s hp ↦ ?_⟩
    obtain ⟨N,hN⟩ := works z s hp
    refine ⟨N,fun t ht ↦ ⟨?_,(hN t ht).2⟩⟩
    cases exact with
    | true => exact (hN t ht).1
    | false => exact Set.finite_empty.subset (fun x hx ↦ (hx.2 ((hN t ht).1 hx.1)).elim)

/-- The rightmost column allows arbitrarily many hallucinations. The stable
full-domain support misses no words and meets every infinite target infinitely. -/
theorem figures_3_4_unrestricted (F : Generic.LanguageFamily α) (hi : ∀ i, (F i).Infinite) :
    ∃ G : SupportAlgorithm α, IsStableGenerator G F ∧ EventuallyGeneratesWith
      (fun xs K ↦ K ⊆ G xs ∧ (K \ G xs).Finite ∧ (K ∩ G xs).Infinite) F := by
  refine ⟨fun _ ↦ Set.univ, fun _ _ _ ↦ ⟨0,fun _ _ _ _ ↦ rfl⟩,
    fun i s _ ↦ ⟨0,fun t _ ↦ ?_⟩⟩
  simpa using And.intro (Set.subset_univ (F i)) (And.intro (Set.finite_empty : (∅ : Set α).Finite) (hi i))

/-- The literal equality to infinity printed under the rightmost column
cannot be required universally, since the full target has no outside words. -/
theorem infinite_errors_impossible_on_full_target (U : Set α) : ¬ (U \ Set.univ).Infinite := by simp

/-- The bottom row of Figure 3 permits zero or finitely many hallucinations.
The last critical language is eventually an infinite sublanguage. -/
theorem figure_3_infinite_present (F : Generic.LanguageFamily α) (hi : ∀ i, (F i).Infinite) :
    SampleAllowingInfiniteCoverage (approximateFocusAlgorithm F) F := by
  intro z s hp
  obtain ⟨T,hT⟩ := CharikarPabbaraju.exhaustiveTarget_eventually_critical hp
  refine ⟨max z T,fun t ht ↦ ?_⟩
  rw [supportAt_approximateFocusAlgorithm]
  have hz := hT t ((Nat.le_max_right ..).trans ht)
  have hc := CharikarPabbaraju.exhaustiveFocus_spec ((Nat.le_max_left ..).trans ht) hz
  exact ⟨CharikarPabbaraju.exhaustiveHistoryCritical_subset_of_le hc.2.2 hz hc.2.1,hi _⟩

end GenLimit.BreadthCharacterizations
