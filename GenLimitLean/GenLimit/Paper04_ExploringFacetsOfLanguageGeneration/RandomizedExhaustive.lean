import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.RegularRayEncoding
import GenLimit.Support.PredicateLock
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-! # Corollary 5.1, randomized exhaustive generation -/

namespace GenLimit.CharikarPabbaraju

open MeasureTheory

/-- An event has probability strictly above half when some measurable
subevent has probability strictly above half. For measurable events this
is precisely the usual probability inequality. -/
def Majority {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Ω → Prop) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ 1/2 < μ.real E ∧ ∀ ω ∈ E, P ω

private theorem majority_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {P Q : Ω → Prop} (h : Majority μ P) (hp : ∀ ω, P ω → Q ω) : Majority μ Q := by
  obtain ⟨E, hm, hv, he⟩ := h
  exact ⟨E, hm, hv, fun ω hω => hp ω (he ω hω)⟩

private theorem majorities_intersect {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P Q : Ω → Prop} (hp : Majority μ P) (hq : Majority μ Q) :
    ∃ ω, P ω ∧ Q ω := by
  obtain ⟨E, hE, hμE, he⟩ := hp
  obtain ⟨D, _, hμD, hd⟩ := hq
  by_contra hn
  have hdis : D ⊆ Eᶜ := fun ω hω hωE => hn ⟨ω, he ω hωE, hd ω hω⟩
  have hle := measureReal_mono (μ := μ) hdis
  rw [measureReal_compl hE, measureReal_univ_eq_one] at hle
  linarith

/-- The random tape chooses a deterministic history-dependent machine. No
independence between the machine's decisions at different times is required. -/
def MajorityExhaustive {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Ω → ExhaustiveAlgorithm α) (C : Generic.LanguageClass α) : Prop :=
  ∀ K ∈ C, ∀ s, Generic.Presents s K → ∃ T, ∀ t ≥ T,
    Majority μ (fun ω => ExhaustiveCorrectAt (A ω) K s t)

private def future (A : ExhaustiveAlgorithm α) (xs : List α) : Set α :=
  Set.range (A xs.length xs.get)

private theorem future_prefix (A : ExhaustiveAlgorithm α) (s : ℕ → α) (t : ℕ) :
    future A (textPrefix s t) = generateOnly A s t := by
  change Set.range (learnerOfFiniteHistory A (textPrefix s t)) = _
  rw [textPrefix_eq_ofFn, learnerOfFiniteHistory_ofFn]
  rfl

/-- Theorem 3's regular family over a binary alphabet defeats a randomized
machine even when the required per-time success probability is only above half. -/
theorem corollary_5_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ExhaustiveAlgorithm (List Bool)) : ¬ MajorityExhaustive μ A signedUnaryRayClass := by
  intro hg
  let P := fun xs K => Majority μ (fun ω => (K \ future (A ω) xs).Finite ∧
    (future (A ω) xs \ K).Finite)
  have learns : ∀ K ∈ signedUnaryRayClass, ∀ s, Generic.Presents s K →
      ∃ T, ∀ t ≥ T, P (textPrefix s t) K := by
    intro K hK s hp
    obtain ⟨T, hT⟩ := hg K hK s hp
    refine ⟨T, fun t ht => majority_mono (hT t ht) (fun ω hw => ?_)⟩
    rw [future_prefix]
    have h := exhaustiveCorrectAt_implies_relaxed hw
    rw [RelaxedExhaustiveCorrectAt, Set.symmDiff_def] at h
    exact ⟨h.subset Set.subset_union_right, hw.1⟩
  obtain ⟨T, _, hboth⟩ := Support.finite_witness_compatible signedUnaryRayClass
    (fun K hK => (signedUnaryRayClass_languages_infinite K hK).nonempty)
    P learns (show Set.univ ∈ signedUnaryRayClass from Or.inl rfl)
  obtain ⟨L, hL, hTL, hsub, hinf⟩ := signedUnaryRayClass_no_finite_weak_telltale T
  obtain ⟨xs, _, hU, hL'⟩ := hboth L hL hTL hsub.subset
  obtain ⟨ω, hu, hl⟩ := majorities_intersect hU hL'
  apply hinf ((hu.1.union hl.2).subset ?_)
  intro x hx
  by_cases hf : x ∈ future (A ω) xs
  · exact Or.inr ⟨hf, hx.2⟩
  · exact Or.inl ⟨hx.1, hf⟩

end GenLimit.CharikarPabbaraju
