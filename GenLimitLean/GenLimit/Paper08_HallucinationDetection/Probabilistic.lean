import GenLimit.Paper08_HallucinationDetection.Reductions
import GenLimit.Paper08_HallucinationDetection.NegativeExamples
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! # Detection on random presentations

Section 1 does not specify a distribution or a rate. Here convergence means
almost-sure eventual correctness, with a separate null set allowed for each
candidate set. A collection of admissible laws may be specified per target.
Independent draws from any discrete law with the given support are examples.
-/
namespace GenLimit.HallucinationDetection

open MeasureTheory ProbabilityTheory Filter

/-- Almost-sure identification and detection for any prescribed collection
of laws supported almost surely on presentations of their respective targets. -/
theorem probabilistic_detection_iff_identification {α : Type*} [MeasurableSpace α]
    [Countable α] [Nonempty α] (C : Generic.LanguageFamily α)
    (laws : ℕ → Set (Measure (ℕ → α)))
    (hp : ∀ z, ∀ μ ∈ laws z, ∀ᵐ s ∂μ, Generic.Presents s (C z)) :
    (∃ D : Detector α, ∀ z, ∀ μ ∈ laws z, ∀ G : Set α, ∀ᵐ s ∂μ,
      ∃ T, ∀ t ≥ T, DetectorCorrectAt D G (C z) s t) ↔
    (∃ M : Angluin.SemanticIdentifier α, ∀ z, ∀ μ ∈ laws z,
      ∀ᵐ s ∂μ, IdentifiesInLimit C M s (C z)) := by
  constructor
  · rintro ⟨D,hD⟩
    refine ⟨identifierFromDetector C D, ?_⟩
    intro z μ hμ
    have hall := ae_all_iff.mpr (fun i : ℕ ↦ hD z μ hμ (C i))
    filter_upwards [hp z μ hμ, hall] with s hs hd
    exact identifierFromDetector_correct_on_stream C D hs hd
  · rintro ⟨M,hM⟩
    obtain ⟨e,he⟩ := exists_surjective_nat α
    refine ⟨detectorFromIdentifier C e M, ?_⟩
    intro z μ hμ G
    filter_upwards [hM z μ hμ] with s hs
    exact detectorFromIdentifier_correct_on_stream C e he M hs G

/-- An iid stream on a countable discrete space presents its PMF support with
probability one, including when that support is finite. -/
theorem iid_presents_support {α : Type*} [Countable α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (p : PMF α) :
    ∀ᵐ s ∂Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure), Generic.Presents s p.support := by
  classical
  let μ := Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have coord (i : ℕ) := measurePreserving_eval_infinitePi (fun _ : ℕ ↦ p.toMeasure) i
  have hin : ∀ᵐ s ∂μ, ∀ i, s i ∈ p.support := by
    apply ae_all_iff.mpr
    intro i
    apply (coord i).quasiMeasurePreserving.ae
    exact (mem_ae_iff_prob_eq_one (.of_discrete)).2
      ((p.toMeasure_apply_eq_one_iff (.of_discrete)).2 Set.Subset.rfl)
  have hit (x : p.support) : ∀ᵐ s ∂μ, (x : α) ∈ Set.range s := by
    let S (i : ℕ) : Set (ℕ → α) := Function.eval i ⁻¹' {x.val}
    have hm (i) : MeasurableSet (S i) := (measurable_pi_apply _) (.singleton _)
    have hprob (i) : μ (S i) = p x := by
      rw [show μ (S i) = p.toMeasure {x.val} from (coord i).measure_preimage (.singleton _)]
      exact p.toMeasure_apply_singleton _ (.singleton _)
    have hi : iIndepSet S μ := by
      apply (iIndepSet_iff_meas_biInter hm).2
      intro F
      exact (iIndepFun_infinitePi (μ := fun _ : ℕ ↦ p.toMeasure)
        (X := fun _ ↦ @id α) (fun _ ↦ measurable_id)).measure_inter_preimage_eq_mul
          F (sets := fun _ ↦ {x.val}) (fun _ _ ↦ .singleton _)
    have hsum : (∑' i, μ (S i)) = ⊤ := by
      simp_rw [hprob]
      exact ENNReal.tsum_const_eq_top_of_ne_zero x.property
    have ha : limsup S atTop ∈ ae μ := (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hm)).2
      (measure_limsup_eq_one hm hi hsum)
    filter_upwards [ha] with s hs
    obtain ⟨i,hi⟩ := (mem_limsup_iff_frequently_mem.mp hs).exists
    exact ⟨i,hi⟩
  filter_upwards [hin, ae_all_iff.mpr hit] with s hs hall
  exact Set.Subset.antisymm (Set.range_subset_iff.mpr hs) (fun x hx ↦ hall ⟨x,hx⟩)

/-- In the iid model each target can have any distribution with that support. -/
def IIDDetectable (C : Generic.LanguageFamily ℕ) : Prop :=
  ∃ D : Detector ℕ, ∀ z (p : PMF ℕ), p.support = C z → ∀ G : Set ℕ,
    ∀ᵐ s ∂Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure),
      ∃ T, ∀ t ≥ T, DetectorCorrectAt D G (C z) s t

def IIDIdentifiable (C : Generic.LanguageFamily ℕ) : Prop :=
  ∃ M : Angluin.SemanticIdentifier ℕ, ∀ z (p : PMF ℕ), p.support = C z →
    ∀ᵐ s ∂Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure), IdentifiesInLimit C M s (C z)

theorem iid_detectable_iff_identifiable (C : Generic.LanguageFamily ℕ) :
    IIDDetectable C ↔ IIDIdentifiable C := by
  let laws (z : ℕ) : Set (Measure (ℕ → ℕ)) :=
    {μ | ∃ p : PMF ℕ, p.support = C z ∧ μ = Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)}
  have hh := probabilistic_detection_iff_identification C laws (by
    rintro z μ ⟨p,hp,rfl⟩
    simpa [← hp] using iid_presents_support p)
  constructor
  · rintro ⟨D,hd⟩
    obtain ⟨M,hm⟩ := hh.1 ⟨D,by rintro z μ ⟨p,hp,rfl⟩; exact hd z p hp⟩
    exact ⟨M,fun z p hp ↦ hm z _ ⟨p,hp,rfl⟩⟩
  · rintro ⟨M,hm⟩
    obtain ⟨D,hd⟩ := hh.2 ⟨M,by rintro z μ ⟨p,hp,rfl⟩; exact hm z p hp⟩
    exact ⟨D,fun z p hp ↦ hd z _ ⟨p,hp,rfl⟩⟩

/-- Complete, correctly labeled observations suffice almost surely for any
law satisfying that presentation assumption. -/
theorem probabilistic_labeled_detection {α Ω : Type*} [MeasurableSpace Ω]
    (C : Generic.LanguageFamily α) (μ : Measure Ω) (s : Ω → LabeledStream α) (z : ℕ)
    (hp : ∀ᵐ ω ∂μ, IsLabeledEnumeration (s ω) (C z)) (G : Set α) :
    ∀ᵐ ω ∂μ, ∃ T, ∀ t ≥ T, NegativeDetectorCorrectAt negativeExampleDetector G (C z) (s ω) t := by
  filter_upwards [hp] with ω h
  exact negativeExampleDetector_correct C z _ h G

end GenLimit.HallucinationDetection
