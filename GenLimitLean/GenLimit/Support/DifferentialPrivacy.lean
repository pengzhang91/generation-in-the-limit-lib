import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Event-based differential privacy for replacement of one input coordinate.
The same adjacency applies to a finite database and to an infinite stream. -/

namespace GenLimit.Privacy

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Inputs agree except possibly at a single chosen coordinate. -/
def Neighbors {ι X : Type*} (u v : ι → X) : Prop := ∃ j, ∀ i, i ≠ j → u i = v i

/-- Event inequality for an output law. Setting δ to zero gives pure privacy. -/
def DifferentiallyPrivate {ι X Y : Type*} [MeasurableSpace Y]
    (ε : ℝ) (δ : ℝ≥0∞) (law : (ι → X) → Measure Y) : Prop :=
  ∀ u v, Neighbors u v → ∀ E, MeasurableSet E →
    law u E ≤ ENNReal.ofReal (Real.exp ε) * law v E + δ

/-- A finite group of replacements costs at most one exponential factor per replacement. -/
theorem group_privacy {ι X Y : Type*} [MeasurableSpace Y] {ε : ℝ}
    {law : (ι → X) → Measure Y} (hp : DifferentiallyPrivate ε 0 law)
    (edits : Finset ι) {u v : ι → X} (same : ∀ i ∉ edits, u i = v i)
    {E : Set Y} (hE : MeasurableSet E) :
    law u E ≤ ENNReal.ofReal (Real.exp ε) ^ edits.card * law v E := by
  classical
  induction edits using Finset.induction_on generalizing u with
  | empty =>
    have h : u = v := funext fun i => same i (by simp)
    simp [h]
  | @insert j js hj ih =>
    let w := Function.update u j (v j)
    have adj : Neighbors u w := ⟨j, fun i h => (Function.update_of_ne h _ _).symm⟩
    have agree : ∀ i ∉ js, w i = v i := by
      intro i hi
      by_cases h : i = j
      · subst i; simp [w]
      · change Function.update u j (v j) i = _
        rw [Function.update_of_ne h]
        exact same i (by simp [hi,h])
    have one := hp u w adj E hE
    simp only [add_zero] at one
    rw [Finset.card_insert_of_notMem hj,pow_succ',mul_assoc]
    exact one.trans (mul_le_mul_left' (ih agree) _)

/-- A causal randomized continual release specifies the joint output law.
Every event on its first n outputs depends only on the first n inputs. -/
structure ContinualRelease (X Y : Type*) [MeasurableSpace Y] where
  law : (ℕ → X) → Measure (ℕ → Y)
  probability : ∀ s, IsProbabilityMeasure (law s)
  causal : ∀ n (u v : ℕ → X), (∀ i < n, u i = v i) →
    ∀ E : Set (Fin n → Y), MeasurableSet E →
      law u ((fun y i => y (i : Fin n)) ⁻¹' E) = law v ((fun y i => y (i : Fin n)) ⁻¹' E)

namespace ContinualRelease

variable {X Y : Type*} [MeasurableSpace Y] (M : ContinualRelease X Y)

theorem marginal_congr (t : ℕ) {u v : ℕ → X} (h : ∀ i ≤ t, u i = v i)
    {B : Set Y} (hb : MeasurableSet B) :
    M.law u {y | y t ∈ B} = M.law v {y | y t ∈ B} :=
  M.causal (t+1) u v (fun i hi => h i (Nat.le_of_lt_succ hi))
    ((fun y => y ⟨t,Nat.lt_succ_self t⟩) ⁻¹' B) ((measurable_pi_apply _) hb)

theorem tail_measurable {B : Set Y} (hb : MeasurableSet B) (n : ℕ) :
    MeasurableSet {y : ℕ → Y | ∀ t ≥ n, y t ∈ B} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ => (measurable_pi_apply t) hb

/-- Finite edits preserve probability-one eventual membership under pure
continual privacy, including on streams that do not enumerate a target. -/
theorem transfer_eventually {ε : ℝ} (hp : DifferentiallyPrivate ε 0 M.law)
    {u v : ℕ → X} (edits : Finset ℕ) (same : ∀ i ∉ edits, u i = v i)
    {B : Set Y} (hb : MeasurableSet B) (ha : ∀ᵐ y ∂M.law v, ∃ n, ∀ t ≥ n, y t ∈ B) :
    ∀ᵐ y ∂M.law u, ∃ n, ∀ t ≥ n, y t ∈ B := by
  rw [ae_iff] at ha ⊢
  have hm : MeasurableSet {y : ℕ → Y | ∃ n, ∀ t ≥ n, y t ∈ B} := by
    rw [Set.setOf_exists]; exact MeasurableSet.iUnion (tail_measurable hb)
  change M.law v {y : ℕ → Y | ∃ n, ∀ t ≥ n, y t ∈ B}ᶜ = 0 at ha
  exact nonpos_iff_eq_zero.mp ((group_privacy hp edits same hm.compl).trans_eq (by rw [ha,mul_zero]))

/-- Almost-sure eventual membership forces every sufficiently late marginal
to place strictly more than half its mass in the indicated set. -/
theorem eventual_majority (s : ℕ → X) {B : Set Y} (hb : MeasurableSet B)
    (ha : ∀ᵐ y ∂M.law s, ∃ n, ∀ t ≥ n, y t ∈ B) :
    ∃ n, ∀ t ≥ n, 1 / 2 < (M.law s).real {y | y t ∈ B} := by
  letI := M.probability s
  let E := fun n : ℕ => {y : ℕ → Y | ∀ t ≥ n, y t ∈ B}
  have mono : Monotone E := fun _ _ h _ hy t ht => hy t (h.trans ht)
  have ae : ∀ᵐ y ∂M.law s, y ∈ ⋃ n, E n := by simpa [E] using ha
  have mass : (M.law s).real (⋃ n, E n) = 1 := by
    rw [measureReal_def,(mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (tail_measurable hb))).mp ae,ENNReal.toReal_one]
  have tends : Tendsto (fun n => (M.law s).real (E n)) atTop (𝓝 1) := by
    rw [← mass]
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop mono)
  obtain ⟨n,hn⟩ := eventually_atTop.mp (tends.eventually (Ioi_mem_nhds (by norm_num : (1:ℝ)/2 < 1)))
  exact ⟨n,fun t ht => (hn t ht).trans_le (measureReal_mono (fun _ hy => hy t le_rfl))⟩

end ContinualRelease
end GenLimit.Privacy
