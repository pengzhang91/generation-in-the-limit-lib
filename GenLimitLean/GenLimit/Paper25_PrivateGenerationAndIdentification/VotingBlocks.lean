import GenLimit.Paper14_ListLanguageIdentification.Statistical
import GenLimit.Paper25_PrivateGenerationAndIdentification.StochasticNecessity
import Mathlib.Data.Nat.Pairing
import Mathlib.Analysis.SpecificLimits.Normed

/-! Sample-and-aggregate blocks for stochastic identification. At epoch k,
there are k+1 voters, each reading k+1 distinct public input positions. -/
namespace GenLimit.PrivateLimit.Voting

open MeasureTheory Filter Set ListIdentification
open scoped Classical ENNReal Topology
noncomputable section

def slot (k i j : ℕ) := Nat.pair k (Nat.pair i j)

def ballot (s : ℕ → ℕ) (k i : ℕ) := (List.range (k+1)).map fun j => s (slot k i j)

def canon (C : LanguageFamily) (z : ℕ) : ℕ := Nat.find (show ∃ j, C j = C z from ⟨z,rfl⟩)

theorem canon_spec (C : LanguageFamily) (z : ℕ) : C (canon C z) = C z :=
  Nat.find_spec (show ∃ j, C j = C z from ⟨z,rfl⟩)

private theorem canon_congr (C : LanguageFamily) {i j : ℕ} (h : C i = C j) :
    canon C i = canon C j := by
  apply le_antisymm
  · exact Nat.find_min' _ ((canon_spec C j).trans h.symm)
  · exact Nat.find_min' _ ((canon_spec C i).trans h)

def vote (C : LanguageFamily) (xs : List ℕ) := canon C (relativeIdentifier C univ xs)

theorem witness (C : LanguageFamily) (hc : Angluin.ConditionTwo C) (z : ℕ) :
    ∃ W : Finset ℕ, (W : Set ℕ) ⊆ C z ∧ ∀ xs : List ℕ,
      (∀ x ∈ xs, x ∈ C z) → (∀ x ∈ W, x ∈ xs) → vote C xs = canon C z := by
  have cond : RelativeConditionTwo C univ := by
    intro i _
    obtain ⟨T,sub,lock⟩ := hc i
    exact ⟨T,sub,fun j _ => lock j⟩
  obtain ⟨W,hW,hw⟩ := Statistical.layer_witness C cond (Set.mem_univ z)
  exact ⟨W,hW,fun xs hin seen => canon_congr C (hw xs hin seen)⟩

/-- A linear number of events, each with geometrically small probability,
has a summable union bound. -/
theorem summable_linear_geometric {r : ℝ} (hr : 0 ≤ r) (lt : r < 1) :
    Summable (fun k : ℕ => (k+1:ℝ)*r^k) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (show ‖r‖ < 1 by rwa [Real.norm_eq_abs,abs_of_nonneg hr])
  simpa [add_mul] using (by simpa using h : Summable (fun k : ℕ => (k:ℝ)*r^k)).add
    (summable_geometric_of_lt_one hr lt)

theorem eventually_avoid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (B : ℕ → Set Ω) {v : ℕ → ℝ} (hv : Summable v)
    (bound : ∀ᶠ k in atTop, μ.real (B k) ≤ v k) :
    ∀ᵐ x ∂μ, ∀ᶠ k in atTop, x ∉ B k := by
  have hsum : Summable (fun k => μ.real (B k)) :=
    hv.of_norm_bounded_eventually_nat (by simpa only [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg] using bound)
  apply ae_eventually_notMem
  simpa only [Measure.real_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top

private theorem missing (p : PMF ℕ) (x k i : ℕ) :
    (Measure.infinitePi fun _ : ℕ => p.toMeasure).real {s | x ∉ ballot s k i} =
      ((p.toMeasure).real {x}ᶜ)^(k+1) := by
  let I := (Finset.range (k+1)).image (slot k i)
  have inj : Function.Injective (slot k i) := fun _ _ h =>
    (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2).2
  have eq : {s | x ∉ ballot s k i} = (↑I : Set ℕ).pi (fun _ => ({x} : Set ℕ)ᶜ) := by
    ext s
    simp [ballot,I,Set.mem_pi,eq_comm]
    exact ⟨fun h _ j hj eq => eq ▸ h j hj,fun h j hj => h _ j hj rfl⟩
  rw [Measure.real_def,eq,Measure.infinitePi_pi _ (fun _ _ => (measurableSet_singleton x).compl)]
  simp [I,Finset.card_image_of_injective _ inj,Measure.real_def]

theorem eventually_ballots (C : LanguageFamily) (hc : Angluin.ConditionTwo C)
    (z : ℕ) (p : PMF ℕ) (hp : p.support = C z) :
    ∀ᵐ s ∂Measure.infinitePi (fun _ : ℕ => p.toMeasure),
      ∀ᶠ k : ℕ in atTop, ∀ i ≤ k, vote C (ballot s k i) = canon C z := by
  let μ := Measure.infinitePi fun _ : ℕ => p.toMeasure
  obtain ⟨W,hW,hw⟩ := witness C hc z
  have one (x : ℕ) (hx : x ∈ W) : ∀ᵐ s ∂μ, ∀ᶠ k : ℕ in atTop, ∀ i ≤ k, x ∈ ballot s k i := by
    let r := (p.toMeasure).real {x}ᶜ
    have mem : x ∈ p.support := hp.symm ▸ hW hx
    have pos : 0 < (p x).toReal := ENNReal.toReal_pos mem (p.apply_ne_top _)
    have hr : 0 ≤ r := measureReal_nonneg
    have lt : r < 1 := by
      dsimp [r]; rw [measureReal_compl (measurableSet_singleton _),measureReal_univ_eq_one,
        Measure.real_def,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]; linarith
    let B (k : ℕ) := ⋃ i ∈ Finset.range (k+1), {s | x ∉ ballot s k i}
    have bd (k : ℕ) : μ.real (B k) ≤ (k+1:ℝ)*r^k := by
      apply (measureReal_biUnion_finset_le (μ := μ) _ _).trans
      simp only [μ,missing,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr lt.le (Nat.le_succ k)) (by positivity)
    filter_upwards [eventually_avoid μ B (summable_linear_geometric hr lt) (Eventually.of_forall bd)] with s hs
    filter_upwards [hs] with k hk i hi
    exact Classical.not_not.mp (fun h => hk (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),h⟩⟩))
  have all := (ae_all_iff.mpr fun x : ↥W => one x x.property)
  filter_upwards [all,HallucinationDetection.iid_presents_support p] with s hs hsupp
  have together := (eventually_all (ι := ↥W)).mpr hs
  filter_upwards [together] with k hk i hi
  apply hw
  · intro x hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    rw [←hp,←hsupp]; exact mem_range_self _
  · exact fun x hx => hk ⟨x,hx⟩ i hi

end
end GenLimit.PrivateLimit.Voting
