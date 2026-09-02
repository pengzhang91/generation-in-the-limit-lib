import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper17_InfiniteContamination.VanishingNoise
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Element-based density and finite-contamination transfer

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Theorem 6.15, Corollary 6.16, Claim 6.17, and
Theorem 6.18.

Element density is the ordered density of the range of the entire output
stream.  The first part of this module isolates the analytic endgame of
Algorithm 8: globally distinct outputs that are eventually target-valid and
whose target rank has asymptotic slope at most `2 / ρ` have lower density at
least `ρ / 2`.  This is proved through the already verified change-of-density
lemma rather than reproducing the source's long inverse-prefix calculation.

The final section packages Theorem 6.18's finite-expansion reduction.  Its
ordering-compatibility hypothesis is explicit: `OrderedLanguage` permits
arbitrary enumerations, whereas the paper assumes that all target orders are
induced by one fixed ambient canonical order.
-/

namespace GenLimit.InfiniteContamination

open Filter
open scoped Topology
open GenLimit.KleinbergWei

/-! ## Definition 9: density of the output sequence -/

/-- The element generator's complete output stream on one input run. -/
def elementOutputStream
    (gen : GenLimit.Generic.Generator ℕ)
    (stream : GenLimit.Generic.Stream ℕ) :
    GenLimit.Generic.Stream ℕ :=
  fun t => GenLimit.Generic.output gen stream t

/-- The set of all values ever output on a run. -/
def elementOutputLanguage
    (gen : GenLimit.Generic.Generator ℕ)
    (stream : GenLimit.Generic.Stream ℕ) : Set ℕ :=
  Set.range (elementOutputStream gen stream)

/-- Definition 9's lower element-based density. -/
noncomputable def elementBasedLowerDensity
    (gen : GenLimit.Generic.Generator ℕ)
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ) : ℝ :=
  K.lowerDensity (elementOutputLanguage gen stream)

/-- Definition 9's upper element-based density. -/
noncomputable def elementBasedUpperDensity
    (gen : GenLimit.Generic.Generator ℕ)
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ) : ℝ :=
  K.upperDensity (elementOutputLanguage gen stream)

/-- Avoiding all previous outputs at every round makes the output stream
globally injective. -/
theorem elementOutputStream_injective_of_fresh
    (gen : GenLimit.Generic.Generator ℕ)
    (stream : GenLimit.Generic.Stream ℕ)
    (hfresh : ∀ t,
      GenLimit.Generic.output gen stream t ∉
        generatedBefore gen stream t) :
    Function.Injective (elementOutputStream gen stream) := by
  intro m n hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hfresh n (mem_generatedBefore_iff.mpr
      ⟨m, hlt, hmn⟩)
  · exact hfresh m (mem_generatedBefore_iff.mpr
      ⟨n, hgt, hmn.symm⟩)

/-! ## Output streams with finitely many invalid initial values -/

theorem finiteNoise_of_eventually_mem
    {output : GenLimit.Generic.Stream ℕ} {L : Set ℕ}
    (heventually : ∃ N, ∀ n, N ≤ n → output n ∈ L) :
    FiniteNoise output L := by
  obtain ⟨N, hN⟩ := heventually
  apply (Set.finite_Iio N).subset
  intro n hn
  change output n ∉ L at hn
  change n < N
  by_contra hnot
  exact hn (hN n (Nat.le_of_not_gt hnot))

/-- For an injective output stream, counting displayed values in its own
range and in `K` is the same as counting target-valid output times. -/
theorem empiricalTargetCount_outputRange_inter
    (output : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective output)
    (K : Set ℕ) (n : ℕ) :
    empiricalTargetCount output (Set.range output ∩ K) n =
      trueCount output K n := by
  classical
  letI : DecidableEq ℕ := Classical.decEq ℕ
  letI : DecidablePred (fun x : ℕ => x ∈ Set.range output ∩ K) :=
    Classical.decPred _
  unfold empiricalTargetCount trueCount GenLimit.Generic.sample
  rw [Finset.filter_image]
  simp only [Set.mem_inter_iff, Set.mem_range, exists_apply_eq_apply,
    true_and]
  exact Finset.card_image_of_injective _ hinjective

theorem empiricalTargetRatio_outputRange_inter_eq
    (output : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective output)
    (K : Set ℕ) {n : ℕ} (hn : 0 < n) :
    empiricalTargetRatio output (Set.range output ∩ K) n =
      1 - empiricalNoiseRate output K n := by
  have hcount :=
    empiricalTargetCount_outputRange_inter output hinjective K n
  have hpartition := trueCount_add_noiseCount output K n
  have hpartitionReal :
      (trueCount output K n : ℝ) +
          (noiseCount output K n : ℝ) = n := by
    exact_mod_cast hpartition
  simp only [empiricalTargetRatio, hn.ne', if_false,
    empiricalNoiseRate]
  rw [hcount]
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp [hnReal.ne']
  linarith

/-- An injective stream which is eventually target-valid spends asymptotic
fraction one in the target-valid part of its own range. -/
theorem tendsto_empiricalTargetRatio_outputRange_inter_one
    (output : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective output)
    (K : Set ℕ)
    (heventually : ∃ N, ∀ n, N ≤ n → output n ∈ K) :
    Tendsto
      (empiricalTargetRatio output (Set.range output ∩ K))
      atTop (nhds 1) := by
  have hnoise : VanishingNoise output K :=
    finiteNoise_implies_vanishingNoise
      (finiteNoise_of_eventually_mem heventually)
  have hsub :
      Tendsto (fun n => 1 - empiricalNoiseRate output K n)
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hnoise
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (empiricalTargetRatio_outputRange_inter_eq
    output hinjective K (by omega)).symm

theorem liminf_empiricalTargetRatio_outputRange_inter_eq_one
    (output : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective output)
    (K : Set ℕ)
    (heventually : ∃ N, ∀ n, N ≤ n → output n ∈ K) :
    liminf
        (empiricalTargetRatio output (Set.range output ∩ K))
        atTop = 1 :=
  (tendsto_empiricalTargetRatio_outputRange_inter_one
    output hinjective K heventually).liminf_eq

/-! ## Claim 6.17 and the density endgame -/

/-- A point stream has asymptotic canonical displacement at most `q` when
it is `M`-bounded for every strictly larger constant `M`. -/
def AsymptoticDisplacementAtMost
    (K : OrderedLanguage)
    (output : GenLimit.Generic.Stream ℕ) (q : ℝ) : Prop :=
  ∀ M, q < M → BoundedDisplacement K output K.carrier M

/-- A single displacement bound turns global output distinctness and late
validity into an element-density lower bound. -/
theorem elementLowerDensity_of_boundedDisplacement
    (K : OrderedLanguage)
    (output : GenLimit.Generic.Stream ℕ)
    (M : ℝ) (hM : 0 < M)
    (hinjective : Function.Injective output)
    (heventually :
      ∃ N, ∀ n, N ≤ n → output n ∈ K.carrier)
    (hbounded : BoundedDisplacement K output K.carrier M) :
    1 / M ≤ K.lowerDensity (Set.range output) := by
  let validRange := Set.range output ∩ K.carrier
  have hchange :=
    lemma_7_5_lowerDensity K output validRange
      Set.inter_subset_right M hM hbounded
  have hliminf :
      liminf (empiricalTargetRatio output validRange) atTop = 1 := by
    exact liminf_empiricalTargetRatio_outputRange_inter_eq_one
      output hinjective K.carrier heventually
  have hvalid : 1 / M ≤ K.lowerDensity validRange := by
    rw [hliminf] at hchange
    simpa using hchange
  exact hvalid.trans
    (K.lowerDensity_mono Set.inter_subset_left)

/-- The limiting form of Claim 6.17: asymptotic displacement `q` gives
element lower density at least `1/q`. -/
theorem elementLowerDensity_of_asymptoticDisplacement
    (K : OrderedLanguage)
    (output : GenLimit.Generic.Stream ℕ)
    (q : ℝ) (hq : 0 < q)
    (hinjective : Function.Injective output)
    (heventually :
      ∃ N, ∀ n, N ≤ n → output n ∈ K.carrier)
    (hdisplacement : AsymptoticDisplacementAtMost K output q) :
    1 / q ≤ K.lowerDensity (Set.range output) := by
  let M : ℕ → ℝ := fun n => q + 1 / (n + 1 : ℕ)
  have hMpos : ∀ n, 0 < M n := by
    intro n
    dsimp [M]
    positivity
  have hqM : ∀ n, q < M n := by
    intro n
    dsimp [M]
    exact lt_add_of_pos_right q (by positivity)
  have hbound :
      ∀ n, 1 / M n ≤ K.lowerDensity (Set.range output) := by
    intro n
    exact elementLowerDensity_of_boundedDisplacement
      K output (M n) (hMpos n) hinjective heventually
      (hdisplacement (M n) (hqM n))
  have hMtendsto : Tendsto M atTop (nhds q) := by
    simpa [M] using
      tendsto_const_nhds.add
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hinv : Tendsto (fun n => 1 / M n) atTop (nhds (1 / q)) := by
    simpa [one_div] using hMtendsto.inv₀ hq.ne'
  exact le_of_tendsto' hinv hbound

/-- Theorem 6.15's exact analytic endpoint once Algorithm 8 has established
Claim 6.17's asymptotic rank bound. -/
theorem theorem_6_15_density_endgame
    (K : OrderedLanguage)
    (output : GenLimit.Generic.Stream ℕ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hinjective : Function.Injective output)
    (heventually :
      ∃ N, ∀ n, N ≤ n → output n ∈ K.carrier)
    (hclaim :
      AsymptoticDisplacementAtMost K output (2 / ρ)) :
    ρ / 2 ≤ K.lowerDensity (Set.range output) := by
  have hq : 0 < 2 / ρ := div_pos (by norm_num) hρ
  have h := elementLowerDensity_of_asymptoticDisplacement
    K output (2 / ρ) hq hinjective heventually hclaim
  convert h using 1
  field_simp [hρ.ne']

/-! ## Theorem 6.18: finite-expansion reduction -/

/-- Lower and upper element-density guarantees on a fixed run. -/
def ElementDensityGuaranteeOn
    (gen : GenLimit.Generic.Generator ℕ)
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (ρlow ρup : ℝ) : Prop :=
  ρlow ≤ elementBasedLowerDensity gen K stream ∧
    ρup ≤ elementBasedUpperDensity gen K stream

/-- Theorem 6.18's reduction for explicit finite-expansion and ordering
interfaces.  `hmeasure` records the paper's ambient-canonical-order fact:
the finite expansion and its base language give the same density to every
output set. -/
theorem theorem_6_18_finiteContamination_transfer
    (O : GenLimit.OracleFamily)
    (orders expansionOrders : ℕ → OrderedLanguage)
    (_hcarrier : ∀ i, (orders i).carrier = O.language i)
    (_hexpansionCarrier : ∀ j,
      (expansionOrders j).carrier =
        (finiteExpansionOracleFamily O).language j)
    (hmeasure : ∀ j A,
      (expansionOrders j).lowerDensity A =
          (finiteExpansionMeasure orders j).lowerDensity A ∧
        (expansionOrders j).upperDensity A =
          (finiteExpansionMeasure orders j).upperDensity A)
    (gen : GenLimit.Generic.Generator ℕ)
    (ρlow ρup : ℝ)
    (hvanilla : ∀ j stream,
      GenLimit.Generic.Presents stream
          ((finiteExpansionOracleFamily O).language j) →
        GeneratesElementInLimitOn gen
            ((finiteExpansionOracleFamily O).language j) stream ∧
          ElementDensityGuaranteeOn
            gen (expansionOrders j) stream ρlow ρup) :
    ∀ z stream,
      FiniteNoiseFiniteOmissionEnumeration stream (O.language z) →
        GeneratesElementInLimitOn gen (O.language z) stream ∧
          ElementDensityGuaranteeOn
            gen (orders z) stream ρlow ρup := by
  intro z stream hcontam
  obtain ⟨j, hjBase, hjPresents⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  have hrun := hvanilla j stream hjPresents
  refine ⟨lemma_4_3_element_finiteExpansion_transfer
    hcontam ?_, ?_⟩
  · rw [hjPresents]
    exact hrun.1
  · rcases hrun.2 with ⟨hlow, hup⟩
    change
      ρlow ≤ (orders z).lowerDensity
          (elementOutputLanguage gen stream) ∧
        ρup ≤ (orders z).upperDensity
          (elementOutputLanguage gen stream)
    change ρlow ≤ (expansionOrders j).lowerDensity
      (elementOutputLanguage gen stream) at hlow
    change ρup ≤ (expansionOrders j).upperDensity
      (elementOutputLanguage gen stream) at hup
    have hm := hmeasure j (elementOutputLanguage gen stream)
    constructor
    · rw [hm.1, finiteExpansionMeasure, hjBase] at hlow
      exact hlow
    · rw [hm.2, finiteExpansionMeasure, hjBase] at hup
      exact hup

end GenLimit.InfiniteContamination
