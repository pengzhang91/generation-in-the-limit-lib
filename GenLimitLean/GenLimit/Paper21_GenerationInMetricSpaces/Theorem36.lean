import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Overview
import Mathlib.Topology.MetricSpace.Basic

/-!
# Theorem 3.6: transport of the union separation to metric spaces

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1.

The source reduces the theorem to the discrete union-separation result of
Hanneke--Karbasi--Mehrotra--Velegkas.  This file makes that reduction
explicit.  Failure of a finite radius-`r` cover supplies a countable
`r`-separated packing.  The two discrete witness classes from Paper10 are
embedded into that packing.  Their autonomous schedules give the positive
uniform and non-uniform conclusions, while any metric generator for their
union pulls back to a generator on injective presentations of the original
discrete union, contradicting Paper10's lower bound.

The transport is semantic: it does not assume that the packing or its inverse
is computable.
-/

namespace GenLimit.MetricSpaces

open GenLimit.Generic

namespace Theorem36

noncomputable section

/-! ## Images under an injective coding -/

/-- The pointwise image of a language under a coding into an ambient space. -/
def imageLanguage
    (encode : β → α) (L : GenLimit.Generic.Language β) :
    GenLimit.Generic.Language α :=
  encode '' L

/-- The image of every language in a class. -/
def imageClass
    (encode : β → α) (H : LanguageClass β) : LanguageClass α :=
  imageLanguage encode '' H

theorem imageClass_union
    (encode : β → α) (H₁ H₂ : LanguageClass β) :
    imageClass encode (H₁ ∪ H₂) =
      imageClass encode H₁ ∪ imageClass encode H₂ := by
  ext L
  simp only [imageClass, Set.mem_image, Set.mem_union]
  constructor
  · rintro ⟨K, hK | hK, rfl⟩
    · exact Or.inl ⟨K, hK, rfl⟩
    · exact Or.inr ⟨K, hK, rfl⟩
  · rintro (⟨K, hK, rfl⟩ | ⟨K, hK, rfl⟩)
    · exact ⟨K, Or.inl hK, rfl⟩
    · exact ⟨K, Or.inr hK, rfl⟩

/-! ## Elementary metric lemmas used by the transport -/

/-- A finite sample covers itself at every nonnegative radius when the
distance kernel vanishes on the diagonal. -/
theorem finiteSample_self_cover
    {rho : Distance α} (hself : ∀ x, rho x x = 0)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (S : Finset α) :
    (S : Set α) ⊆ closedNeighborhood rho (S : Set α) epsilon := by
  intro x hx eta hepsilonEta
  refine ⟨x, hx, ?_⟩
  rw [hself]
  exact lt_of_le_of_lt hepsilon0 hepsilonEta

/-- If every center is farther than `r` from `y`, then `y` is outside the
closed neighbourhood at every strictly smaller radius. -/
theorem not_mem_closedNeighborhood_of_separated
    {rho : Distance α} {A : Set α} {r epsilon : ℝ} {y : α}
    (hepsilonR : epsilon < r)
    (hfar : ∀ x ∈ A, r < rho x y) :
    y ∉ closedNeighborhood rho A epsilon := by
  intro hy
  let eta : ℝ := (epsilon + r) / 2
  have hepsilonEta : epsilon < eta := by
    dsimp [eta]
    linarith
  have hetaR : eta < r := by
    dsimp [eta]
    linarith
  obtain ⟨x, hxA, hxy⟩ := hy eta hepsilonEta
  have := hfar x hxA
  linarith

/-! ## Positive transport of the autonomous Paper10 witnesses -/

/-- An injective autonomous schedule transports to a metric uniform
generator along a separated coding. -/
theorem uniformlyGeneratableAt_image_of_withoutAdversaryInput
    {rho : Distance α} {r epsilon epsilon' : ℝ}
    (hself : ∀ x, rho x x = 0)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon'R : epsilon' < r)
    (encode : β → α)
    (hencode : Function.Injective encode)
    (hseparated : ∀ {x y}, x ≠ y → r < rho (encode x) (encode y))
    {H : LanguageClass β}
    (hH : GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput H) :
    UniformlyGeneratableAt rho epsilon epsilon' (imageClass encode H) := by
  classical
  obtain ⟨outputs, T, houtputsInjective, houtputs⟩ := hH
  let embeddedOutputs : ℕ → α := fun n => encode (outputs n)
  have hembeddedInjective : Function.Injective embeddedOutputs := by
    intro i j hij
    exact houtputsInjective (hencode hij)
  let G :=
    GenLimit.UnionClosedness.freshGeneratorFromAutonomousOutputs
      embeddedOutputs hembeddedInjective
  refine ⟨G, T, ?_⟩
  rintro L' ⟨L, hLH, rfl⟩ stream hstream t htrigger s hts
  have hTCard : T ≤ (GenLimit.Generic.sample stream t).card :=
    htrigger (GenLimit.Generic.sample stream t)
      (finiteSample_self_cover hself hepsilon0
        (GenLimit.Generic.sample stream t))
  have hTt : T ≤ t :=
    hTCard.trans (GenLimit.Generic.sample_card_le stream t)
  obtain ⟨n, hsn, hout, hfresh⟩ :=
    GenLimit.UnionClosedness.freshGeneratorFromAutonomousOutputs_spec
      embeddedOutputs hembeddedInjective
        (fun i : Fin s => stream i)
  have houtput : GenLimit.Generic.output G stream s = embeddedOutputs n := by
    exact hout
  have hfreshSample :
      embeddedOutputs n ∉ GenLimit.Generic.sample stream s := by
    rw [← houtput]
    simpa only [GenLimit.Generic.output,
      GenLimit.Generic.sequenceSample_prefix] using hfresh
  constructor
  · rw [houtput]
    exact ⟨outputs n,
      houtputs L hLH n ((hTt.trans hts).trans hsn), rfl⟩
  · rw [houtput]
    apply not_mem_closedNeighborhood_of_separated hepsilon'R
    intro x hxSample
    have hxRange : x ∈ Set.range stream := by
      obtain ⟨i, hi, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hxSample
      exact ⟨i, rfl⟩
    obtain ⟨z, hzL, rfl⟩ := hstream hxRange
    apply hseparated
    intro hEq
    apply hfreshSample
    change encode (outputs n) ∈ GenLimit.Generic.sample stream s
    exact hEq ▸ hxSample

/-- The same separated-coding argument with a target-dependent autonomous
tail gives metric non-uniform generation. -/
theorem nonuniformlyGeneratableAt_image_of_withoutAdversaryInput
    {rho : Distance α} {r epsilon epsilon' : ℝ}
    (hself : ∀ x, rho x x = 0)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon'R : epsilon' < r)
    (encode : β → α)
    (hencode : Function.Injective encode)
    (hseparated : ∀ {x y}, x ≠ y → r < rho (encode x) (encode y))
    {H : LanguageClass β}
    (hH : GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput H) :
    NonuniformlyGeneratableAt rho epsilon epsilon' (imageClass encode H) := by
  classical
  obtain ⟨outputs, houtputsInjective, houtputs⟩ := hH
  let embeddedOutputs : ℕ → α := fun n => encode (outputs n)
  have hembeddedInjective : Function.Injective embeddedOutputs := by
    intro i j hij
    exact houtputsInjective (hencode hij)
  let G :=
    GenLimit.UnionClosedness.freshGeneratorFromAutonomousOutputs
      embeddedOutputs hembeddedInjective
  refine ⟨G, ?_⟩
  rintro L' ⟨L, hLH, rfl⟩
  obtain ⟨T, hT⟩ := houtputs L hLH
  refine ⟨T, ?_⟩
  intro stream hstream t htrigger s hts
  have hTCard : T ≤ (GenLimit.Generic.sample stream t).card :=
    htrigger (GenLimit.Generic.sample stream t)
      (finiteSample_self_cover hself hepsilon0
        (GenLimit.Generic.sample stream t))
  have hTt : T ≤ t :=
    hTCard.trans (GenLimit.Generic.sample_card_le stream t)
  obtain ⟨n, hsn, hout, hfresh⟩ :=
    GenLimit.UnionClosedness.freshGeneratorFromAutonomousOutputs_spec
      embeddedOutputs hembeddedInjective
        (fun i : Fin s => stream i)
  have houtput : GenLimit.Generic.output G stream s = embeddedOutputs n := by
    exact hout
  have hfreshSample :
      embeddedOutputs n ∉ GenLimit.Generic.sample stream s := by
    rw [← houtput]
    simpa only [GenLimit.Generic.output,
      GenLimit.Generic.sequenceSample_prefix] using hfresh
  constructor
  · rw [houtput]
    exact ⟨outputs n, hT n ((hTt.trans hts).trans hsn), rfl⟩
  · rw [houtput]
    apply not_mem_closedNeighborhood_of_separated hepsilon'R
    intro x hxSample
    have hxRange : x ∈ Set.range stream := by
      obtain ⟨i, hi, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hxSample
      exact ⟨i, rfl⟩
    obtain ⟨z, hzL, rfl⟩ := hstream hxRange
    apply hseparated
    intro hEq
    apply hfreshSample
    change encode (outputs n) ∈ GenLimit.Generic.sample stream s
    exact hEq ▸ hxSample

/-! ## Pulling a metric union generator back to the discrete witnesses -/

/-- Pull an ambient generator back through an injective coding.  Outputs
outside the coding range are decoded arbitrarily; successful ambient runs
eventually output inside the target image, where `invFun` is a true inverse. -/
def pullGenerator [Nonempty β]
    (encode : β → α) (G : Generator α) : Generator β :=
  fun t xs => Function.invFun encode (G t (fun i => encode (xs i)))

theorem encoded_metricPresentation
    {rho : Distance α} (hself : ∀ x, rho x x = 0)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (encode : β → α)
    {stream : Stream β} {L : GenLimit.Generic.Language β}
    (hpresents : GenLimit.Generic.Presents stream L) :
    MetricPresentation rho epsilon (fun n => encode (stream n))
      (imageLanguage encode L) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    refine ⟨stream n, ?_, rfl⟩
    rw [← hpresents]
    exact ⟨n, rfl⟩
  · rintro _ ⟨x, hxL, rfl⟩ eta hepsilonEta
    have hxRange : x ∈ Set.range stream := by
      rwa [hpresents]
    obtain ⟨n, rfl⟩ := hxRange
    refine ⟨encode (stream n), ⟨n, rfl⟩, ?_⟩
    rw [hself]
    exact lt_of_le_of_lt hepsilon0 hepsilonEta

theorem correctAt_pullGenerator_of_metricCorrectAt
    [Nonempty β]
    {rho : Distance α} (hself : ∀ x, rho x x = 0)
    {epsilon' : ℝ} (hepsilon'0 : 0 ≤ epsilon')
    (encode : β → α) (hencode : Function.Injective encode)
    (G : Generator α) (L : GenLimit.Generic.Language β)
    (stream : Stream β) (t : ℕ)
    (hcorrect :
      MetricCorrectAt rho epsilon' G (imageLanguage encode L)
        (fun n => encode (stream n)) t) :
    GenLimit.Generic.CorrectAt (pullGenerator encode G) L stream t := by
  rcases hcorrect with ⟨htarget, hfresh⟩
  obtain ⟨x, hxL, hxOutput⟩ := htarget
  have hpullOutput :
      GenLimit.Generic.output (pullGenerator encode G) stream t = x := by
    simp only [GenLimit.Generic.output, pullGenerator]
    change Function.invFun encode
      (GenLimit.Generic.output G (fun n => encode (stream n)) t) = x
    rw [← hxOutput]
    exact Function.leftInverse_invFun hencode x
  constructor
  · simpa only [hpullOutput] using hxL
  · rw [hpullOutput]
    intro hxSample
    apply hfresh
    intro eta hepsilon'Eta
    refine ⟨encode x, ?_, ?_⟩
    · obtain ⟨i, hi, hix⟩ :=
        GenLimit.Generic.mem_sample_iff.mp hxSample
      apply GenLimit.Generic.mem_sample_iff.mpr
      exact ⟨i, hi, congrArg encode hix⟩
    · rw [← hxOutput, hself]
      exact lt_of_le_of_lt hepsilon'0 hepsilon'Eta

/-- Any metric generator for an image class yields a discrete generator for
the source class on the injective presentations used by Paper10. -/
theorem generatableOnInjectivePresentations_of_generatableInLimitAt_image
    [Nonempty β]
    {rho : Distance α} (hself : ∀ x, rho x x = 0)
    {epsilon epsilon' : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon'0 : 0 ≤ epsilon')
    (encode : β → α) (hencode : Function.Injective encode)
    {H : LanguageClass β}
    (hmetric : GeneratableInLimitAt rho epsilon epsilon'
      (imageClass encode H)) :
    GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations H := by
  obtain ⟨G, hG⟩ := hmetric
  refine ⟨pullGenerator encode G, ?_⟩
  intro L hLH stream _hstreamInjective hpresents
  have hLImage : imageLanguage encode L ∈ imageClass encode H :=
    ⟨L, hLH, rfl⟩
  obtain ⟨T, hT⟩ :=
    hG (imageLanguage encode L) hLImage
      (fun n => encode (stream n))
      (encoded_metricPresentation hself hepsilon0 encode hpresents)
  exact ⟨T, fun t ht =>
    correctAt_pullGenerator_of_metricCorrectAt
      hself hepsilon'0 encode hencode G L stream t (hT t ht)⟩

/-! ## Extracting a countable separated packing -/

theorem exists_outside_finite_cover
    {rho : Distance α} {r : ℝ}
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α))
    (centers : Finset α) :
    ∃ x : α, x ∉ closedNeighborhood rho (centers : Set α) r := by
  by_contra hnone
  push_neg at hnone
  apply hcover
  exact ⟨centers, fun x _ => hnone x⟩

/-- The finite prefix of the greedily selected packing. -/
def packingPrefix
    [DecidableEq α]
    (rho : Distance α) (r : ℝ)
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α)) :
    ℕ → Finset α
  | 0 => ∅
  | n + 1 =>
      insert
        (Classical.choose
          (exists_outside_finite_cover hcover
            (packingPrefix rho r hcover n)))
        (packingPrefix rho r hcover n)

/-- The new point added at stage `n` of the greedy packing. -/
def packingPoint
    [DecidableEq α]
    (rho : Distance α) (r : ℝ)
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α))
    (n : ℕ) : α :=
  Classical.choose
    (exists_outside_finite_cover hcover (packingPrefix rho r hcover n))

@[simp] theorem packingPrefix_succ
    [DecidableEq α]
    (rho : Distance α) (r : ℝ)
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α)) (n : ℕ) :
    packingPrefix rho r hcover (n + 1) =
      insert (packingPoint rho r hcover n) (packingPrefix rho r hcover n) :=
  rfl

theorem packingPoint_not_mem_closedNeighborhood
    [DecidableEq α]
    (rho : Distance α) (r : ℝ)
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α)) (n : ℕ) :
    packingPoint rho r hcover n ∉
      closedNeighborhood rho (packingPrefix rho r hcover n : Set α) r :=
  Classical.choose_spec
    (exists_outside_finite_cover hcover (packingPrefix rho r hcover n))

theorem packingPoint_mem_prefix
    [DecidableEq α]
    (rho : Distance α) (r : ℝ)
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α))
    {m n : ℕ} (hmn : m < n) :
    packingPoint rho r hcover m ∈ packingPrefix rho r hcover n := by
  classical
  induction n with
  | zero => omega
  | succ n ih =>
      rw [packingPrefix_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hmn | rfl
      · exact Finset.mem_insert_of_mem (ih hmn)
      · exact @Finset.mem_insert_self α _ _ _

theorem packingPoint_separated_of_lt
    [DecidableEq α]
    {rho : Distance α} {r : ℝ}
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α))
    {m n : ℕ} (hmn : m < n) :
    r < rho (packingPoint rho r hcover m)
      (packingPoint rho r hcover n) := by
  classical
  by_contra hnot
  have hle :
      rho (packingPoint rho r hcover m)
        (packingPoint rho r hcover n) ≤ r :=
    le_of_not_gt hnot
  apply packingPoint_not_mem_closedNeighborhood rho r hcover n
  apply inClosedNeighborhood_mono_centers
    (show ({packingPoint rho r hcover m} : Set α) ⊆
      (packingPrefix rho r hcover n : Set α) by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact packingPoint_mem_prefix rho r hcover hmn)
  exact mem_closedNeighborhood_singleton_iff.mpr hle

theorem packingPoint_separated
    [DecidableEq α]
    {rho : Distance α} {r : ℝ}
    (hcomm : ∀ x y, rho x y = rho y x)
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α))
    {m n : ℕ} (hmn : m ≠ n) :
    r < rho (packingPoint rho r hcover m)
      (packingPoint rho r hcover n) := by
  rcases Nat.lt_or_gt_of_ne hmn with hmn | hnm
  · exact packingPoint_separated_of_lt hcover hmn
  · rw [hcomm]
    exact packingPoint_separated_of_lt hcover hnm

theorem packingPoint_injective
    [DecidableEq α]
    {rho : Distance α} {r : ℝ}
    (hcomm : ∀ x y, rho x y = rho y x)
    (hself : ∀ x, rho x x = 0) (hr : 0 < r)
    (hcover : ¬ HasFiniteCover rho r (Set.univ : Set α)) :
    Function.Injective (packingPoint rho r hcover) := by
  intro m n hmn
  by_contra hne
  have hsep := packingPoint_separated hcomm hcover hne
  rw [hmn] at hsep
  rw [hself] at hsep
  linarith

end

end Theorem36

/-! ## Source-facing theorem -/

/-- Theorem 3.6.  In every metric space whose whole domain has infinite
radius-`r` covering number, and at scales at most `r / 2`, there are a
uniformly generatable class and a non-uniformly generatable class whose union
is not generatable in the limit.

The witness classes are the images of Paper10's discrete Theorem 3.2 classes
inside a greedily chosen countable `r`-packing. -/
theorem theorem_3_6
    {alpha : Type*} [MetricSpace alpha]
    {r epsilon epsilon' : ℝ}
    (hr : 0 < r)
    (hepsilon0 : 0 ≤ epsilon) (_hepsilonLe : epsilon ≤ r / 2)
    (hepsilon'0 : 0 ≤ epsilon') (hepsilon'Le : epsilon' ≤ r / 2)
    (hcover :
      ¬ HasFiniteCover (fun x y : alpha => dist x y) r
        (Set.univ : Set alpha)) :
    ∃ H₁ H₂ : LanguageClass alpha,
      UniformlyGeneratableAt (fun x y => dist x y) epsilon epsilon' H₁ ∧
      NonuniformlyGeneratableAt (fun x y => dist x y) epsilon epsilon' H₂ ∧
      ¬ GeneratableInLimitAt (fun x y => dist x y) epsilon epsilon'
        (H₁ ∪ H₂) := by
  classical
  let encode : ℤ → alpha := fun z =>
    Theorem36.packingPoint (fun x y : alpha => dist x y) r hcover
      (Equiv.intEquivNat z)
  have hencodeSeparated :
      ∀ {x y : ℤ}, x ≠ y → r < dist (encode x) (encode y) := by
    intro x y hxy
    apply Theorem36.packingPoint_separated dist_comm hcover
    exact Equiv.intEquivNat.injective.ne hxy
  have hencodeInjective : Function.Injective encode := by
    intro x y hxy
    apply Equiv.intEquivNat.injective
    apply Theorem36.packingPoint_injective dist_comm dist_self hr hcover
    exact hxy
  have hepsilon'R : epsilon' < r := by
    have hrHalf : r / 2 < r := by linarith
    exact hepsilon'Le.trans_lt hrHalf
  let H₁ : LanguageClass alpha :=
    Theorem36.imageClass encode
      GenLimit.UnionClosedness.theorem43FirstClass
  let H₂ : LanguageClass alpha :=
    Theorem36.imageClass encode
      GenLimit.UnionClosedness.theorem43SecondClass
  refine ⟨H₁, H₂, ?_, ?_, ?_⟩
  · apply Theorem36.uniformlyGeneratableAt_image_of_withoutAdversaryInput
      dist_self hepsilon0 hepsilon'R encode hencodeInjective hencodeSeparated
    exact
      GenLimit.UnionClosedness.theorem_3_2_witness.2.2.2.1
  · apply Theorem36.nonuniformlyGeneratableAt_image_of_withoutAdversaryInput
      dist_self hepsilon0 hepsilon'R encode hencodeInjective hencodeSeparated
    exact GenLimit.UnionClosedness.theorem_3_2_witness.2.1
  · intro hmetric
    have hmetricImage :
        GeneratableInLimitAt (fun x y : alpha => dist x y) epsilon epsilon'
          (Theorem36.imageClass encode
            (GenLimit.UnionClosedness.theorem43FirstClass ∪
              GenLimit.UnionClosedness.theorem43SecondClass)) := by
      rw [Theorem36.imageClass_union]
      exact hmetric
    have hpulled :=
      Theorem36.generatableOnInjectivePresentations_of_generatableInLimitAt_image
        dist_self hepsilon0 hepsilon'0 encode hencodeInjective hmetricImage
    exact GenLimit.UnionClosedness.theorem_3_2_witness.2.2.2.2
      (by simpa only [Set.union_comm] using hpulled)

end GenLimit.MetricSpaces
