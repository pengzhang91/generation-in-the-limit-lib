import GenLimit.Paper05_HallucinationsBreadthAndStability.IncreasingCoverage
import GenLimit.Paper05_HallucinationsBreadthAndStability.EffectiveBreadth
import GenLimit.Paper03_HallucinationAndModeCollapse.FiniteIdentificationComputation
import GenLimit.Core.ClosureDimension

/-! # The sample-allowing versions of Proposition 8.10 and Corollary 8.11 -/

namespace GenLimit.BreadthCharacterizations

open GenLimit.DiscreteIID GenLimit.Generic GenLimit.HallucinationModeCollapse GenLimit.Support

/-- Definition 8.9 answers membership in the intersection of the version space. -/
structure VSI (H : Generic.LanguageClass ℕ) where
  query : Finset ℕ → ℕ → Bool
  spec : ∀ S x, query S x = true ↔ x ∈ commonCore H S

/-- Accumulate the first d+1 distinct observations, then freeze. -/
def frozenStep (d : ℕ) (S : Finset ℕ) (x : ℕ) := if d < S.card then S else insert x S

private theorem frozen (d : ℕ) (S : Finset ℕ) (xs : List ℕ)
    (h : d < S.card) : xs.foldl (frozenStep d) S = S := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, frozenStep, if_pos h] using ih

private theorem frozen_spec (d : ℕ) (S : Finset ℕ) (xs : List ℕ) :
    let R := xs.foldl (frozenStep d) S
    R ⊆ S ∪ xs.toFinset ∧ (d < R.card ∨ R = S ∪ xs.toFinset) := by
  induction xs generalizing S with
  | nil => simp
  | cons x xs ih =>
    by_cases h : d < S.card
    · rw [frozen d S _ h]
      exact ⟨Finset.subset_union_left,Or.inl h⟩
    · simp only [List.foldl_cons,frozenStep,if_neg h]
      have he : insert x S ∪ xs.toFinset = S ∪ (x::xs).toFinset := by ext; simp
      simpa only [← he] using ih (insert x S)

private def frozenFallback (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.min' h else 0

noncomputable def frozenCoverageLaw {H : Generic.LanguageClass ℕ} (V : VSI H) (d : ℕ)
    (xs : List ℕ) : PMF ℕ :=
  let S := xs.foldl (frozenStep d) ∅
  positiveGeometric.map (fun x => if V.query S x then x else frozenFallback S)

/-- From the first history containing d+1 distinct words onwards, every
extension has this same infinite valid support. Each seed uses one VSI query. -/
theorem proposition_8_10_sampleAllowing (H : Generic.LanguageClass ℕ) (V : VSI H) (d : ℕ)
    (hd : ClosureDimensionAtMost H d) (K : Set ℕ) (hK : K ∈ H) (xs : List ℕ)
    (hxs : ∀ x ∈ xs, x ∈ K) (hsize : d < xs.toFinset.card) :
    ∃ U : Set ℕ, U.Infinite ∧ U ⊆ K ∧ ∀ ys : List ℕ, (frozenCoverageLaw V d (xs++ys)).support = U := by
  classical
  let S := xs.foldl (frozenStep d) ∅
  obtain ⟨h₁,h₂⟩ := frozen_spec d ∅ xs
  have hsub : S ⊆ xs.toFinset := by simpa using h₁
  have large : d < S.card := h₂.elim id (fun e => by change d < (xs.foldl (frozenStep d) ∅).card; rwa [e,Finset.empty_union])
  have hS : (↑S : Set ℕ) ⊆ K := fun _ hx => hxs _ (List.mem_toFinset.mp (hsub hx))
  have hV : K ∈ versionSpace H S := ⟨hK,hS⟩
  let U := commonCore H S
  refine ⟨U,hd S large ⟨K,hV⟩,fun x hx => hx K hV,fun ys => ?_⟩
  have hsne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hmin : frozenFallback S ∈ S := by simpa [frozenFallback,hsne] using S.min'_mem hsne
  have base : frozenFallback S ∈ U := fun _ h => h.2 hmin
  simp only [frozenCoverageLaw, List.foldl_append,show xs.foldl (frozenStep d) ∅ = S from rfl,
    frozen d S ys large, PMF.support_map]
  ext x
  constructor
  · rintro ⟨y,_,rfl⟩
    change (if V.query S y then y else frozenFallback S) ∈ U
    split <;> first | exact (V.spec _ _).mp ‹_› | exact base
  · intro hx
    exact ⟨x,positiveGeometric_support x,if_pos ((V.spec _ _).mpr hx)⟩

/-- A finite list of language indices implements the VSI query with
bounded membership tests on the data and the candidate word. -/
def finiteVSI (O : OracleFamily) (m : ℕ)
    (covers : ∀ i, ∃ j < m, O.language j = O.language i) : VSI (Set.range O.language) where
  query S x := decide (∀ j ∈ Finset.range m, (∀ y ∈ S, O.query j y = true) → O.query j x = true)
  spec S x := by
    simp only [decide_eq_true_eq,Finset.mem_range,O.query_spec]
    constructor
    · rintro h _ ⟨⟨i,rfl⟩,hs⟩
      obtain ⟨j,hj,eq⟩ := covers i
      rw [← eq]
      exact h j hj (fun y hy => eq.symm ▸ hs hy)
    · intro h j _ hs
      exact h _ ⟨Set.mem_range_self j,fun y hy => hs y hy⟩

/-- Corollary 8.11(2) under sample-allowing coverage. The finite list of
indices realizes the intersection query using language membership alone. -/
theorem finite_stableCoverage_membership (O : OracleFamily) (m : ℕ)
    (covers : ∀ i, ∃ j < m, O.language j = O.language i) :
    ∃ d, HasClosureDimension (Set.range O.language) d ∧ ∀ i (xs : List ℕ),
      (∀ x ∈ xs, x ∈ O.language i) → d < xs.toFinset.card →
      ∃ U : Set ℕ, U.Infinite ∧ U ⊆ O.language i ∧ ∀ ys : List ℕ,
        (frozenCoverageLaw (finiteVSI O m covers) d (xs++ys)).support = U := by
  have hf : (Set.range O.language).Finite := by
    apply ((Finset.range m).finite_toSet.image O.language).subset
    rintro _ ⟨i,rfl⟩
    obtain ⟨j,hj,he⟩ := covers i
    exact ⟨j,Finset.mem_range.mpr hj,he⟩
  obtain ⟨d,hd⟩ := finite_language_class_has_finite_closure_dimension hf
  exact ⟨d,hd,fun i xs => proposition_8_10_sampleAllowing _ _ _ hd.1 _ (Set.mem_range_self i) xs⟩

/-- Corollary 8.11(1) with whole-target support: the finite version-space
membership learner eventually selects precisely the right language. -/
theorem finite_stableWhole_membership (O : OracleFamily) (hfin : (Set.range O.language).Finite) :
    let A := finiteVersionSpaceLearner (familyMembership O)
    let G := identifiedRepeatingBreadth O A
    IsWholeTargetGenerator (lawSupport G) O.language ∧ IsStableGenerator (lawSupport G) O.language ∧
      (Computable₂ O.query → HasComputableSampler G) := by
  let A := finiteVersionSpaceLearner (familyMembership O)
  have whole : IsWholeTargetGenerator (lawSupport (identifiedRepeatingBreadth O A)) O.language := by
    intro i s hp
    obtain ⟨W,hW,N,h⟩ := finiteVersionSpace_finiteWitness (familyMembership O)
      (finiteRange_positiveSubsetWitness _ hfin) i
    obtain ⟨M,hM⟩ := Generic.finset_eventually_subset_sample hp W hW
    refine ⟨max N M,fun t ht => ?_⟩
    change (identifiedRepeatingBreadth O A (textPrefix s t)).support = O.language i
    rw [identifiedRepeatingBreadth_support]
    apply h _ (by rw [textPrefix_length]; omega)
    · intro x hx
      obtain ⟨k,_,rfl⟩ := mem_textPrefix_iff.mp hx
      exact hp ▸ Set.mem_range_self k
    · intro x hx
      exact mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp (Generic.sample_mono (by omega : M ≤ t) (hM hx)))
  exact ⟨whole,wholeTargetGenerator_isStable whole,fun ho =>
    identifiedRepeatingBreadth_computableSampler O ho _ (finiteVersionSpaceLearner_computable _ ho)⟩

end GenLimit.BreadthCharacterizations
