import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LocalLemma
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform

/-! Independent fair signs, the two-sided tail estimate, and the trace
dependency graph in the proof of Theorem 5.9. -/
namespace GenLimit.KleinbergWei.Banach.RandomSigns
open MeasureTheory ProbabilityTheory Set Finset
open scoped Classical
noncomputable section
variable {V I : Type*}

abbrev coin := (PMF.uniformOfFintype Bool).toMeasure
abbrev law (V : Type*) := Measure.infinitePi (fun _ : V => coin)
def sign (b : Bool) : ℝ := if b then 1 else -1
def bad (T : Finset V) (limit : ℝ) : Set (V → Bool) :=
  {c | limit < |∑ v ∈ T, sign (c v)|}

private theorem tail (T : Finset V) (limit : ℝ) (positive : 0 ≤ limit) :
    (law V).real (bad T limit) ≤ 2*Real.exp (-limit^2/(2*T.card)) := by
  have oneSide (g : Bool → ℝ) (zero : ∫ b, g b ∂coin = 0)
      (bounded : ∀ b, g b ∈ Set.Icc (-1) 1) :
      (law V).real {c | limit ≤ ∑ v ∈ T, g (c v)} ≤ Real.exp (-limit^2/(2*T.card)) := by
    have meas : Measurable g := Measurable.of_discrete
    have ind := iIndepFun_infinitePi (μ := fun _ : V => coin) (X := fun _ => g) (fun _ => meas)
    have sub (v : V) : HasSubgaussianMGF (fun c : V → Bool => g (c v)) 1 (law V) := by
      have hm := (meas.comp (measurable_pi_apply v)).aemeasurable (μ := law V)
      have ez : ∫ c : V → Bool, g (c v) ∂law V = 0 := by
        rw [←zero,←(measurePreserving_eval_infinitePi (fun _ : V => coin) v).map_eq]
        exact (integral_map (measurable_pi_apply v).aemeasurable meas.aestronglyMeasurable).symm
      have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm
        (Filter.Eventually.of_forall fun c => bounded (c v)) ez
      norm_num at h
      exact h
    simpa using HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun ind
      (fun v (_ : v ∈ T) => sub v) positive
  have mean : ∫ b, sign b ∂coin = 0 := by norm_num [PMF.integral_eq_sum,sign]
  have plus := oneSide sign mean (fun b => by cases b <;> norm_num [sign])
  have minus := oneSide (fun b => -sign b) (by rw [integral_neg,mean,neg_zero]) (fun b => by cases b <;> norm_num [sign])
  let A : Set (V → Bool) := {c | limit ≤ ∑ v ∈ T, sign (c v)}
  let B : Set (V → Bool) := {c | limit ≤ ∑ v ∈ T, -sign (c v)}
  have sub : bad T limit ⊆ A ∪ B := by
    intro c hc
    change limit < |∑ v ∈ T, sign (c v)| at hc
    change limit ≤ _ ∨ limit ≤ _
    rw [Finset.sum_neg_distrib]
    cases lt_abs.mp hc with
    | inl h => exact Or.inl h.le
    | inr h => exact Or.inr (by linarith)
  exact ((measureReal_mono (μ := law V) sub).trans (measureReal_union_le A B)).trans
    (by change (law V).real A + (law V).real B ≤ _; linarith)

/-- Events tested on disjoint sets of coordinates are independent, even
when each test is an arbitrary predicate on all the signs in its trace. -/
private theorem independent (S T : Finset V) (dis : Disjoint S T)
    (P : Set (S → Bool)) (Q : Set (T → Bool)) :
    IndepSet (S.restrict ⁻¹' P) (T.restrict ⁻¹' Q) (law V) := by
  have ind := iIndepFun_infinitePi (μ := fun _ : V => coin) (X := fun _ => id) (fun _ => measurable_id)
  have pairs := ind.indepFun_finset S T dis (fun v => measurable_pi_apply v)
  exact (indepFun_iff_indepSet_preimage (Finset.measurable_restrict S) (Finset.measurable_restrict T)).mp
    pairs P Q (.of_discrete) (.of_discrete)

theorem finite_coloring [DecidableEq V] [Fintype I] (trace : I → Finset V) (limit x : I → ℝ)
    (nonneg : ∀ i, 0 ≤ limit i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (fit : ∀ i, 2*Real.exp (-(limit i)^2/(2*(trace i).card)) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => ¬Disjoint (trace i) (trace j)), (1-x j)) :
    ∃ c : V → Bool, ∀ i, |∑ v ∈ trace i, sign (c v)| ≤ limit i := by
  classical
  let E i := bad (trace i) (limit i)
  let N i := Finset.univ.filter (fun j => ¬Disjoint (trace i) (trace j))
  let P (i : I) : Set (trace i → Bool) := {c | limit i < |∑ v, sign (c v)|}
  have test (i : I) : E i = (trace i).restrict ⁻¹' P i := by
    ext c
    change (limit i < |∑ v ∈ trace i, sign (c v)| ↔ limit i < |∑ v ∈ (trace i).attach, sign (c v.val)|)
    rw [Finset.sum_attach (trace i) (fun v => sign (c v))]
  have meas i : MeasurableSet (E i) := test i ▸ (Finset.measurable_restrict _ (MeasurableSet.of_discrete))
  have dep i (S : Finset I) (_ : i ∉ S) (dis : Disjoint S (N i)) :
      IndepSet (E i) (LocalLemma.avoids E S) (law V) := by
    let U := S.biUnion trace
    have apart : Disjoint (trace i) U := by
      apply Finset.disjoint_left.mpr
      intro v hv mem
      obtain ⟨j,hj,inJ⟩ := Finset.mem_biUnion.mp mem
      exact Finset.disjoint_left.mp dis hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun h =>
        Finset.disjoint_left.mp h hv inJ⟩)
    let Q : Set (U → Bool) := {c | ∀ j, ∀ hj : j ∈ S,
      (fun v : trace j => c ⟨v.val,Finset.mem_biUnion.mpr ⟨j,hj,v.property⟩⟩) ∉ P j}
    have eq : LocalLemma.avoids E S = U.restrict ⁻¹' Q := by
      ext c
      simp only [LocalLemma.avoids,Set.mem_setOf_eq,test,Set.mem_preimage,Q]
      rfl
    rw [test i,eq]
    exact independent _ _ apart _ _
  obtain ⟨pos,lb⟩ := LocalLemma.asymmetric (law V) E meas N dep x hx
    (fun i => (tail _ _ (nonneg i)).trans (fit i)) Finset.univ
  have hn : (law V) (LocalLemma.avoids E Finset.univ) ≠ 0 := fun eq =>
    (pos.trans_le lb).ne' (by simp [measureReal_def,eq])
  obtain ⟨c,hc⟩ := MeasureTheory.nonempty_of_measure_ne_zero hn
  exact ⟨c,fun i => le_of_not_gt (hc i (Finset.mem_univ i))⟩

end
end GenLimit.KleinbergWei.Banach.RandomSigns
