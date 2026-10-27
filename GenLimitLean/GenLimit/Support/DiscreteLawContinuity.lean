import GenLimit.Support.DiscreteIID
import GenLimit.Support.FullSupportDistribution
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Continuity of finite-sample discrete experiments

Push a fixed full-support PMF on natural numbers forward along a sequence.
The expected value of any bounded finite-sample loss is continuous in that
sequence's product topology. The proof is a summable, uniformly dominated
series of functions depending on finitely many coordinates.
-/

namespace GenLimit.DiscreteIID

noncomputable section

open scoped Topology

/-- Geometrically weighted empirical law of an infinite sequence. -/
def sequenceLaw (s : ℕ → ℕ) : PMF ℕ := positiveGeometric.map s

theorem sequenceLaw_support (s : ℕ → ℕ) : (sequenceLaw s).support = Set.range s := by
  rw [sequenceLaw, PMF.support_map]
  ext x
  constructor
  · rintro ⟨k, _, h⟩; exact ⟨k, h⟩
  · rintro ⟨k, h⟩; exact ⟨k, positiveGeometric_support k, h⟩

theorem continuous_finite_coordinates (ks : List ℕ) (f : List ℕ → ℝ) :
    Continuous (fun s : ℕ → ℕ => f (ks.map s)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  let N := ks.foldr max 0 + 1
  have hN (k : ℕ) (hk : k ∈ ks) : k < N := by
    have h : k ≤ ks.foldr max 0 := by
      induction ks with
      | nil => simp at hk
      | cons a ks ih =>
        rcases List.mem_cons.mp hk with rfl | hk
        · exact le_max_left _ _
        · exact (ih hk).trans (le_max_right _ _)
    exact Nat.lt_succ_of_le h
  have heq : ∀ᶠ t in 𝓝 s, f (ks.map t) = f (ks.map s) := by
    filter_upwards [(PiNat.isOpen_cylinder (fun _ => ℕ) s N).mem_nhds
      (PiNat.self_mem_cylinder s N)] with t ht
    congr 1
    apply List.map_congr_left
    intro k hk
    exact PiNat.mem_cylinder_iff.mp ht k (hN k hk)
  apply continuousAt_const.congr
  filter_upwards [heq] with t ht using ht.symm

theorem continuous_sequence_experiment (n : ℕ) (q : List ℕ → PMF ℕ) (E : Set ℕ) :
    Continuous (fun s : ℕ → ℕ => probability ((samples (sequenceLaw s) n).bind q) E) := by
  have heq (s : ℕ → ℕ) : probability ((samples (sequenceLaw s) n).bind q) E =
      ∑' ks, (samples positiveGeometric n ks).toReal * probability (q (ks.map s)) E := by
    rw [sequenceLaw, samples_map, PMF.bind_map, probability_bind_eq_tsum]
    rfl
  simp_rw [heq]
  apply continuous_tsum
  · intro ks
    exact continuous_const.mul (continuous_finite_coordinates ks (fun xs => probability (q xs) E))
  · exact ENNReal.summable_toReal (PMF.tsum_coe_ne_top (samples positiveGeometric n))
  · intro ks s
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (probability_nonneg _ _))]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (probability_le_one _ _)

/-- The usual Baire space of natural-number sequences. -/
theorem baire_natSequences : BaireSpace (ℕ → ℕ) := by
  letI := PiNat.metricSpaceNatNat
  infer_instance

/-- Surjective sequences form a dense G-delta subset of Baire space. -/
theorem surjective_sequences_dense_gdelta :
    IsGδ {s : ℕ → ℕ | Function.Surjective s} ∧
      Dense {s : ℕ → ℕ | Function.Surjective s} := by
  letI := baire_natSequences
  let H (j : ℕ) : Set (ℕ → ℕ) := {s | ∃ k, s k = j}
  have hopen (j : ℕ) : IsOpen (H j) := by
    have heq : H j = ⋃ k : ℕ, {s : ℕ → ℕ | s k = j} := by ext s; simp [H]
    rw [heq]
    apply isOpen_iUnion
    intro k
    exact IsOpen.preimage (show Continuous (fun s : ℕ → ℕ => s k) from continuous_apply k)
      (isOpen_discrete ({j} : Set ℕ))
  have hdense (j : ℕ) : Dense (H j) := by
    apply dense_iff_inter_open.mpr
    intro U hU hne
    obtain ⟨s, hs⟩ := hne
    obtain ⟨V, ⟨t, n, rfl⟩, hsV, hVU⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hs hU
    refine ⟨Function.update t n j, hVU (PiNat.update_mem_cylinder t n j), n, ?_⟩
    simp
  have heq : {s : ℕ → ℕ | Function.Surjective s} = ⋂ j : ℕ, H j := by
    ext s; simp [H, Function.Surjective]
  rw [heq]
  exact ⟨IsGδ.iInter_of_isOpen hopen, dense_iInter_of_isOpen hopen hdense⟩

end
end GenLimit.DiscreteIID
