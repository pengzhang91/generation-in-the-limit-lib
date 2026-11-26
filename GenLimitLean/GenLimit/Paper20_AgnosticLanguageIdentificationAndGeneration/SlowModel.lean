import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.MinimalLower
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.FiniteExperiments
import GenLimit.Paper02_LearningTheory.PACModel
import Mathlib.Combinatorics.Colex
import Mathlib.Probability.Distributions.Uniform

/-! # The fixed finite-label family and distributions for Theorem 2.3 -/
namespace GenLimit.AgnosticLanguage.Slow
open DiscreteIID LiRamanTewari Filter
open scoped Classical Topology
noncomputable section

abbrev Word := ℕ × Option Bool

/-- Each hypothesis specifies one binary label at finitely many coordinates.
The unused third label supplies infinitely many padding words. -/
def family (i : ℕ) : Set Word :=
  {z | z.2 = none ∨ z.1 < i.unpair.1 ∧ z.2 = some (decide (z.1 ∈ Finset.equivBitIndices i.unpair.2))}

theorem infinite_languages (i : ℕ) : (family i).Infinite :=
  (Set.infinite_range_of_injective (f := fun x : ℕ ↦ ((x,none) : Word))
    (fun _ _ h ↦ congrArg Prod.fst h)).mono (by rintro _ ⟨x,rfl⟩; exact Or.inl rfl)

def tag (s : ℕ → ℕ) (x : ℕ) : Word := (x,some (decide (s x ≠ 0)))

theorem unique_label (i x : ℕ) : ¬ ((x,some false) ∈ family i ∧ (x,some true) ∈ family i) := by
  simp [family]
  tauto

def uniformBlock (k n : ℕ) : PMF ℕ :=
  (PMF.uniformOfFintype (Fin (4*n+1))).map (fun j ↦ Nat.pair k j.val)

def marginal (N : ℕ → ℕ) := positiveGeometric.bind (fun k ↦ uniformBlock k (N k))
def weight (k : ℕ) := (positiveGeometric k).toReal

theorem weight_pos (k : ℕ) : 0 < weight k :=
  ENNReal.toReal_pos (positiveGeometric_support k) (positiveGeometric.apply_ne_top k)

private theorem marker_mem (N : ℕ → ℕ) (k : ℕ) : Nat.pair k 0 ∈ (marginal N).support := by
  change _ ∈ (positiveGeometric.bind _).support
  rw [PMF.mem_support_bind_iff]
  refine ⟨k,positiveGeometric_support k,?_⟩
  unfold uniformBlock
  rw [PMF.mem_support_map_iff]
  exact ⟨⟨0,by omega⟩,PMF.mem_support_uniformOfFintype _,rfl⟩

theorem zero_infimum (μ : PMF ℕ) (s : ℕ → ℕ) : optimalRisk family (μ.map (tag s)) = 0 := by
  apply le_antisymm _ (optimalRisk_nonneg ..)
  by_contra! h
  obtain ⟨T,hT⟩ := pmf_tight μ _ h
  let F := T.filter fun x ↦ s x ≠ 0
  let i := Nat.pair (T.sup id+1) (Finset.equivBitIndices.symm F)
  have hin (x) (hx : x ∈ T) : tag s x ∈ family i := by
    apply Or.inr
    simp only [i,Nat.unpair_pair,Equiv.apply_symm_apply,tag]
    refine ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hx),?_⟩
    simp [F,hx]
  have hh := optimalRisk_le family (μ.map (tag s)) i
  rw [risk,probability_map_preimage] at hh
  have hm : tag s ⁻¹' (family i)ᶜ ⊆ (T : Set ℕ)ᶜ := fun x hx hxt ↦ hx (hin x hxt)
  have hc := (probability_mono μ hm)
  rw [probability_compl] at hc
  linarith

theorem no_optimum (N s : ℕ → ℕ) : ¬ ∃ i, Optimal family ((marginal N).map (tag s)) i := by
  rintro ⟨i,hi⟩
  have hz : risk ((marginal N).map (tag s)) (family i) = 0 := hi.trans (zero_infimum ..)
  let x := Nat.pair i.unpair.1 0
  have hm : tag s x ∈ ((marginal N).map (tag s)).support := by
    rw [PMF.mem_support_map_iff]; exact ⟨x,marker_mem N i.unpair.1,rfl⟩
  have hin := (risk_eq_zero_iff ..).mp hz hm
  have hlt : x < i.unpair.1 := (hin.resolve_left (by simp [tag])).1
  exact (Nat.not_lt_of_ge (Nat.left_le_pair _ _)) hlt

def misses (i : ℕ) (s : ℕ → ℕ) (x : ℕ) : Bool := decide (tag s x ∉ family i)

def trial (ν : PMF ℕ) (s : ℕ → ℕ) (o : PMF ℕ) : PMF Bool :=
  o.bind fun i ↦ ν.map (misses i s)

def experiment (A : Identifier Word) (μ ν : PMF ℕ) (n : ℕ) (s : ℕ → ℕ) : ℝ :=
  probability ((samples μ n).bind fun xs ↦ trial ν s (A (xs.map (tag s)))) {true}

theorem trial_each (ν : PMF ℕ) (s : ℕ → ℕ) (i : ℕ) :
    probability (ν.map (misses i s)) {true} = probability ν {x | tag s x ∉ family i} := by
  rw [probability_map_preimage]; congr 1; ext x; simp [misses]

theorem experiment_eq (A : Identifier Word) (μ ν : PMF ℕ) (n : ℕ) (s : ℕ → ℕ) :
    experiment A μ ν n s = ∑' i, (((samples (μ.map (tag s)) n).bind A) i).toReal *
      probability ν {x | tag s x ∉ family i} := by
  unfold experiment trial
  rw [←PMF.bind_bind,probability_bind_eq_tsum,samples_map,PMF.bind_map]
  simp_rw [trial_each]; rfl

theorem block_lower (A : Identifier Word) (N s : ℕ → ℕ) (n k : ℕ) :
    weight k * experiment A (marginal N) (uniformBlock k (N k)) n s ≤
      idErr family A ((marginal N).map (tag s)) n := by
  rw [idErr,zero_infimum,experiment_eq,←tsum_mul_left]
  simp only [sub_zero]
  let o := (samples ((marginal N).map (tag s)) n).bind A
  have hsum := weighted_summable o (v := fun i ↦ probability (uniformBlock k (N k)) {x | tag s x ∉ family i})
    (fun _ ↦ ⟨probability_nonneg ..,probability_le_one ..⟩)
  apply Summable.tsum_le_tsum _ (hsum.mul_left _) (weighted_summable o (v := fun i ↦ risk ((marginal N).map (tag s)) (family i)) fun _ ↦ ⟨probability_nonneg ..,probability_le_one ..⟩)
  intro i
  have bound : weight k * probability (uniformBlock k (N k)) {x | tag s x ∉ family i} ≤ risk ((marginal N).map (tag s)) (family i) := by
    rw [risk,probability_map_preimage]
    exact probability_bind_ge positiveGeometric (fun t ↦ uniformBlock t (N t)) _ k
  exact (mul_left_comm _ _ _).le.trans (mul_le_mul_of_nonneg_left bound ENNReal.toReal_nonneg)

end
end GenLimit.AgnosticLanguage.Slow
