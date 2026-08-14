import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Feedback
import GenLimit.Paper02_LearningTheory.Closure
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Denumerable

/-!
# Charikar--Pabbaraju Example 10

The example fixes a partition of `ℕ` into finite blocks of strictly increasing
size, and adjoins to each block either all negative even integers or all
negative odd integers. The resulting countable class has infinite closure
dimension, but one target-membership query distinguishes the two sides and
permits uniform generation with feedback.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-- The partition data fixed in Example 10. -/
structure ExampleTenPartition where
  block : ℕ → Finset ℕ
  coversUniquely : ∀ n : ℕ, ∃! d : ℕ, n ∈ block d
  strictlyGrowing : StrictMono (fun d => (block d).card)

noncomputable def exampleTenIndexEquiv :
    ℕ ≃ (Σ d : ℕ, Fin (d + 1)) :=
  Classical.choice inferInstance

noncomputable def canonicalExampleTenBlock (d : ℕ) : Finset ℕ :=
  Finset.univ.map
    { toFun := fun k : Fin (d + 1) =>
        exampleTenIndexEquiv.symm ⟨d, k⟩
      inj' := by
        intro a b hab
        have hsigma := exampleTenIndexEquiv.symm.injective hab
        cases hsigma
        rfl }

@[simp] theorem canonicalExampleTenBlock_card (d : ℕ) :
    (canonicalExampleTenBlock d).card = d + 1 := by
  simp [canonicalExampleTenBlock]

/-- A concrete witness that the partition data required by Example 10 is
nonvacuous. It partitions `ℕ` by transporting the fibers `Fin (d+1)` through
a countable equivalence. -/
noncomputable def canonicalExampleTenPartition : ExampleTenPartition where
  block := canonicalExampleTenBlock
  coversUniquely := by
    intro n
    let p := exampleTenIndexEquiv n
    refine ⟨p.1, ?_, ?_⟩
    · simp only [canonicalExampleTenBlock, Finset.mem_map,
        Finset.mem_univ, true_and]
      exact ⟨p.2, by simp [p]⟩
    · intro d hd
      simp only [canonicalExampleTenBlock, Finset.mem_map,
        Finset.mem_univ, true_and] at hd
      obtain ⟨k, hk⟩ := hd
      have heq := congrArg exampleTenIndexEquiv hk
      have hsigma : (⟨d, k⟩ : Σ d : ℕ, Fin (d + 1)) = p := by
        simpa [p] using heq
      exact congrArg (fun q : Σ d : ℕ, Fin (d + 1) => q.1) hsigma
  strictlyGrowing := by
    intro a b hab
    simp only [canonicalExampleTenBlock_card]
    omega

def exampleTenBlock
    (P : ExampleTenPartition) (d : ℕ) : Finset ℤ :=
  (P.block d).map ⟨Int.ofNat, Int.ofNat_injective⟩

@[simp] theorem exampleTenBlock_card
    (P : ExampleTenPartition) (d : ℕ) :
    (exampleTenBlock P d).card = (P.block d).card := by
  simp [exampleTenBlock]

theorem exampleTenBlock_card_ge
    (P : ExampleTenPartition) (d : ℕ) :
    d ≤ (exampleTenBlock P d).card := by
  rw [exampleTenBlock_card]
  exact P.strictlyGrowing.id_le d

theorem exampleTenBlock_nonnegative
    {P : ExampleTenPartition} {d : ℕ} {z : ℤ}
    (hz : z ∈ exampleTenBlock P d) : 0 ≤ z := by
  simp only [exampleTenBlock, Finset.mem_map] at hz
  obtain ⟨n, _hn, rfl⟩ := hz
  exact Int.natCast_nonneg n

/-- All strictly negative even integers. -/
def negativeEvenIntegers : Set ℤ :=
  Set.range (fun n : ℕ => -(2 * (n : ℤ) + 2))

/-- All strictly negative odd integers. -/
def negativeOddIntegers : Set ℤ :=
  Set.range (fun n : ℕ => -(2 * (n : ℤ) + 1))

theorem negativeEvenIntegers_infinite :
    negativeEvenIntegers.Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  simp only at h
  omega

theorem negativeOddIntegers_infinite :
    negativeOddIntegers.Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  simp only at h
  omega

theorem negativeEvenIntegers_negative
    {z : ℤ} (hz : z ∈ negativeEvenIntegers) : z < 0 := by
  change z ∈ Set.range (fun n : ℕ => -(2 * (n : ℤ) + 2)) at hz
  obtain ⟨n, rfl⟩ := hz
  change -(2 * (n : ℤ) + 2) < 0
  omega

theorem negativeOddIntegers_negative
    {z : ℤ} (hz : z ∈ negativeOddIntegers) : z < 0 := by
  change z ∈ Set.range (fun n : ℕ => -(2 * (n : ℤ) + 1)) at hz
  obtain ⟨n, rfl⟩ := hz
  change -(2 * (n : ℤ) + 1) < 0
  omega

theorem negativeParity_disjoint :
    Disjoint negativeEvenIntegers negativeOddIntegers := by
  rw [Set.disjoint_left]
  intro z hzE hzO
  change z ∈ Set.range (fun n : ℕ => -(2 * (n : ℤ) + 2)) at hzE
  change z ∈ Set.range (fun n : ℕ => -(2 * (n : ℤ) + 1)) at hzO
  obtain ⟨m, rfl⟩ := hzE
  obtain ⟨n, hn⟩ := hzO
  change -(2 * (n : ℤ) + 1) = -(2 * (m : ℤ) + 2) at hn
  omega

theorem negTwo_mem_negativeEven :
    (-2 : ℤ) ∈ negativeEvenIntegers :=
  ⟨0, rfl⟩

theorem negTwo_not_mem_negativeOdd :
    (-2 : ℤ) ∉ negativeOddIntegers := by
  change (-2 : ℤ) ∉
    Set.range (fun n : ℕ => -(2 * (n : ℤ) + 1))
  rintro ⟨n, hn⟩
  change -(2 * (n : ℤ) + 1) = -(2 : ℤ) at hn
  omega

def exampleTenEvenLanguage
    (P : ExampleTenPartition) (d : ℕ) : Set ℤ :=
  negativeEvenIntegers ∪ (exampleTenBlock P d : Set ℤ)

def exampleTenOddLanguage
    (P : ExampleTenPartition) (d : ℕ) : Set ℤ :=
  negativeOddIntegers ∪ (exampleTenBlock P d : Set ℤ)

def exampleTenClass
    (P : ExampleTenPartition) : Generic.LanguageClass ℤ :=
  {K | (∃ d, K = exampleTenEvenLanguage P d) ∨
    ∃ d, K = exampleTenOddLanguage P d}

theorem exampleTenEvenLanguage_mem
    (P : ExampleTenPartition) (d : ℕ) :
    exampleTenEvenLanguage P d ∈ exampleTenClass P :=
  Or.inl ⟨d, rfl⟩

theorem exampleTenOddLanguage_mem
    (P : ExampleTenPartition) (d : ℕ) :
    exampleTenOddLanguage P d ∈ exampleTenClass P :=
  Or.inr ⟨d, rfl⟩

theorem exampleTenClass_countable
    (P : ExampleTenPartition) :
    (exampleTenClass P).Countable := by
  let code : Bool × ℕ → Set ℤ :=
    fun p => if p.1 then exampleTenOddLanguage P p.2
      else exampleTenEvenLanguage P p.2
  apply (Set.countable_range code).mono
  intro K hK
  rcases hK with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact ⟨(false, d), by simp [code]⟩
  · exact ⟨(true, d), by simp [code]⟩

theorem exampleTenClass_uus
    (P : ExampleTenPartition) : UUS (exampleTenClass P) := by
  intro K hK
  rcases hK with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact negativeEvenIntegers_infinite.mono Set.subset_union_left
  · exact negativeOddIntegers_infinite.mono Set.subset_union_left

theorem commonCore_exampleTenClass_eq
    (P : ExampleTenPartition) (d : ℕ) :
    commonCore (exampleTenClass P) (exampleTenBlock P d) =
      (exampleTenBlock P d : Set ℤ) := by
  apply Set.Subset.antisymm
  · intro z hz
    have hEven :
        exampleTenEvenLanguage P d ∈
          versionSpace (exampleTenClass P) (exampleTenBlock P d) := by
      refine ⟨exampleTenEvenLanguage_mem P d, ?_⟩
      exact fun _ hx => Or.inr hx
    have hOdd :
        exampleTenOddLanguage P d ∈
          versionSpace (exampleTenClass P) (exampleTenBlock P d) := by
      refine ⟨exampleTenOddLanguage_mem P d, ?_⟩
      exact fun _ hx => Or.inr hx
    have hzEven := hz _ hEven
    have hzOdd := hz _ hOdd
    rcases hzEven with hzE | hzBlock
    · rcases hzOdd with hzO | hzBlock
      · exact (Set.disjoint_left.mp negativeParity_disjoint hzE hzO).elim
      · exact hzBlock
    · exact hzBlock
  · exact sample_subset_commonCore

theorem exampleTenClass_infiniteClosureDimension
    (P : ExampleTenPartition) :
    HasInfiniteClosureDimension (exampleTenClass P) := by
  intro d
  refine ⟨exampleTenBlock P d, exampleTenBlock_card_ge P d, ?_, ?_⟩
  · exact ⟨exampleTenEvenLanguage P d,
      exampleTenEvenLanguage_mem P d, fun _ hx => Or.inr hx⟩
  · rw [commonCore_exampleTenClass_eq]
    exact (exampleTenBlock P d).finite_toSet

theorem exampleTenClass_not_uniformlyGeneratable
    (P : ExampleTenPartition) :
    ¬GenLimit.LiRamanTewari.UniformlyGeneratable (exampleTenClass P) :=
  GenLimit.LiRamanTewari.closure_dimension_necessity (exampleTenClass_uus P)
    (exampleTenClass_infiniteClosureDimension P)

/-! ## The one-query feedback generator -/

private theorem historyInputFinset_insert_finite
    (h : List (FeedbackRound ℤ)) (x : ℤ) :
    ((↑(insert x (feedbackHistoryInputFinset h)) : Set ℤ)).Finite :=
  (insert x (feedbackHistoryInputFinset h)).finite_toSet

noncomputable def exampleTenFeedbackStrategy :
    FeedbackGeneratorStrategy ℤ := by
  classical
  exact
    { query := fun _h _x => -2
      output := fun h x _y a =>
        match a with
        | false =>
            Classical.choose
              (negativeOddIntegers_infinite.diff
                (historyInputFinset_insert_finite h x)).nonempty
        | true =>
            Classical.choose
              (negativeEvenIntegers_infinite.diff
                (historyInputFinset_insert_finite h x)).nonempty }

theorem exampleTenFeedbackStrategy_output_spec
    (h : List (FeedbackRound ℤ)) (x y : ℤ) (a : Bool) :
    (exampleTenFeedbackStrategy.output h x y a) ∈
      (if a then negativeEvenIntegers else negativeOddIntegers) \
      (↑(insert x (feedbackHistoryInputFinset h)) : Set ℤ) := by
  classical
  cases a with
  | false =>
      simpa only [exampleTenFeedbackStrategy, Bool.false_eq_true, if_false]
        using Classical.choose_spec
          (negativeOddIntegers_infinite.diff
            (historyInputFinset_insert_finite h x)).nonempty
  | true =>
      simpa only [exampleTenFeedbackStrategy, if_true]
        using Classical.choose_spec
          (negativeEvenIntegers_infinite.diff
            (historyInputFinset_insert_finite h x)).nonempty

private theorem feedbackSampleThrough_subset_currentInputFinset
    (A : FeedbackAdversaryStrategy ℤ)
    (G : FeedbackGeneratorStrategy ℤ) (t : ℕ) :
    (↑(feedbackSampleThrough A G t) : Set ℤ) ⊆
      (↑(insert (feedbackInput A G t)
        (feedbackHistoryInputFinset (feedbackHistory A G t))) :
          Set ℤ) := by
  intro z hz
  obtain ⟨s, hs, hsz⟩ := Generic.mem_sample_iff.mp hz
  rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hst | rfl
  · apply Finset.mem_insert_of_mem
    rw [feedbackHistoryInputFinset_eq_sample]
    exact Generic.mem_sample_iff.mpr ⟨s, hst, hsz⟩
  · exact Finset.mem_insert.mpr (Or.inl hsz.symm)

theorem exampleTenClass_uniformlyGeneratableWithFeedback
    (P : ExampleTenPartition) :
    UniformlyGeneratableWithFeedback (exampleTenClass P) := by
  classical
  refine ⟨exampleTenFeedbackStrategy, 0, ?_⟩
  intro K hKC A hAK t _hcard
  rcases hKC with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have hanswer :
        feedbackAnswer A exampleTenFeedbackStrategy t = true := by
      apply (hAK.2 t).mpr
      change (-2 : ℤ) ∈ exampleTenEvenLanguage P d
      exact Or.inl negTwo_mem_negativeEven
    have hout := exampleTenFeedbackStrategy_output_spec
      (feedbackHistory A exampleTenFeedbackStrategy t)
      (feedbackInput A exampleTenFeedbackStrategy t)
      (feedbackQuery A exampleTenFeedbackStrategy t)
      (feedbackAnswer A exampleTenFeedbackStrategy t)
    have hout' :
        feedbackOutput A exampleTenFeedbackStrategy t ∈
          (if feedbackAnswer A exampleTenFeedbackStrategy t then
            negativeEvenIntegers else negativeOddIntegers) \
          (↑(insert (feedbackInput A exampleTenFeedbackStrategy t)
            (feedbackHistoryInputFinset
              (feedbackHistory A exampleTenFeedbackStrategy t))) :
            Set ℤ) := by
      exact hout
    rw [hanswer] at hout'
    simp only [if_true] at hout'
    refine ⟨Or.inl hout'.1, ?_⟩
    exact fun hz => hout'.2
      (feedbackSampleThrough_subset_currentInputFinset
        A exampleTenFeedbackStrategy t hz)
  · have hanswer :
        feedbackAnswer A exampleTenFeedbackStrategy t = false := by
      cases h : feedbackAnswer A exampleTenFeedbackStrategy t with
      | false => rfl
      | true =>
          have hmem := (hAK.2 t).mp h
          change (-2 : ℤ) ∈ exampleTenOddLanguage P d at hmem
          rcases hmem with hOdd | hBlock
          · exact (negTwo_not_mem_negativeOdd hOdd).elim
          · exact
              (not_lt_of_ge (exampleTenBlock_nonnegative hBlock)
                (by omega)).elim
    have hout := exampleTenFeedbackStrategy_output_spec
      (feedbackHistory A exampleTenFeedbackStrategy t)
      (feedbackInput A exampleTenFeedbackStrategy t)
      (feedbackQuery A exampleTenFeedbackStrategy t)
      (feedbackAnswer A exampleTenFeedbackStrategy t)
    have hout' :
        feedbackOutput A exampleTenFeedbackStrategy t ∈
          (if feedbackAnswer A exampleTenFeedbackStrategy t then
            negativeEvenIntegers else negativeOddIntegers) \
          (↑(insert (feedbackInput A exampleTenFeedbackStrategy t)
            (feedbackHistoryInputFinset
              (feedbackHistory A exampleTenFeedbackStrategy t))) :
            Set ℤ) := by
      exact hout
    rw [hanswer] at hout'
    refine ⟨Or.inl hout'.1, ?_⟩
    exact fun hz => hout'.2
      (feedbackSampleThrough_subset_currentInputFinset
        A exampleTenFeedbackStrategy t hz)

/-! ## Paper-facing concrete instance -/

noncomputable def canonicalExampleTenClass : Generic.LanguageClass ℤ :=
  exampleTenClass canonicalExampleTenPartition

theorem example10_countable :
    canonicalExampleTenClass.Countable :=
  exampleTenClass_countable canonicalExampleTenPartition

theorem example10_infiniteClosureDimension :
    HasInfiniteClosureDimension canonicalExampleTenClass :=
  exampleTenClass_infiniteClosureDimension canonicalExampleTenPartition

theorem example10_not_uniformlyGeneratable_withoutFeedback :
    ¬GenLimit.LiRamanTewari.UniformlyGeneratable canonicalExampleTenClass :=
  exampleTenClass_not_uniformlyGeneratable canonicalExampleTenPartition

theorem example10_uniformlyGeneratableWithFeedback :
    UniformlyGeneratableWithFeedback canonicalExampleTenClass :=
  exampleTenClass_uniformlyGeneratableWithFeedback
    canonicalExampleTenPartition

end GenLimit.CharikarPabbaraju
