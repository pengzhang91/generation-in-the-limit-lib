import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-! The asymmetric finite Lovász local lemma used in the proof of 5.9.
The induction only uses independence from simultaneous avoidance of
nonneighbors. Its product estimate is valid without conditioning on an
event of unknown positive probability. -/
namespace GenLimit.KleinbergWei.Banach.LocalLemma
open Finset MeasureTheory Set ProbabilityTheory
open scoped BigOperators
variable {ι Ω : Type*} [DecidableEq ι]

/-- Telescope one-event bounds over all members of a disjoint finite set. -/
private theorem extend (Z : Finset ι → ℝ) (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (n : ℕ) (step : ∀ S : Finset ι, S.card < n → ∀ j ∉ S, Z S * w j ≤ Z (insert j S))
    (T U : Finset ι) (dis : Disjoint T U) (size : (T ∪ U).card ≤ n) :
    Z T * ∏ j ∈ U, w j ≤ Z (T ∪ U) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert j U fresh ih =>
    have dj : j ∉ T := fun h => Finset.disjoint_left.mp dis h (Finset.mem_insert_self ..)
    have notin : j ∉ T ∪ U := by simp [dj,fresh]
    rw [Finset.union_insert,Finset.card_insert_of_notMem notin] at size
    rw [Finset.union_insert,Finset.prod_insert fresh]
    have sub : Disjoint T U := dis.mono_right (Finset.subset_insert ..)
    calc
      _ = (Z T * ∏ i ∈ U, w i) * w j := by ring
      _ ≤ Z (T ∪ U) * w j := mul_le_mul_of_nonneg_right (ih sub (by omega)) (hw j)
      _ ≤ _ := step _ (by omega) j notin

private theorem avoidance_bound (Z : Finset ι → ℝ) (nonneg : ∀ S, 0 ≤ Z S)
    (unit : Z ∅ = 1) (neighbors : ι → Finset ι) (p x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (loss : ∀ S i, i ∉ S → Z S - Z (insert i S) ≤ p i * Z (S \ neighbors i))
    (small : ∀ i, p i ≤ x i * ∏ j ∈ neighbors i, (1-x j)) (S : Finset ι) :
    (∏ j ∈ S, (1-x j)) ≤ Z S := by
  let w j := 1-x j
  have pos j : 0 ≤ w j := sub_nonneg.mpr (hx j).2.le
  have dec (U V : Finset ι) (sub : U ⊆ V) : (∏ j ∈ V, w j) ≤ ∏ j ∈ U, w j := by
    rw [←Finset.prod_sdiff sub]
    apply mul_le_of_le_one_left (Finset.prod_nonneg fun j _ => pos j)
    exact Finset.prod_le_one (fun j _ => pos j) (fun j _ => by dsimp [w]; linarith [(hx j).1])
  have step (n : ℕ) (A : Finset ι) (hn : A.card = n) (i : ι) (hi : i ∉ A) :
      Z A * w i ≤ Z (insert i A) := by
    induction n using Nat.strong_induction_on generalizing A i with
    | h n ih =>
      let T := A \ neighbors i
      let U := A ∩ neighbors i
      have eq : T ∪ U = A := Finset.sdiff_union_inter ..
      have dis : Disjoint T U := Finset.disjoint_left.mpr fun j hT hU =>
        (Finset.mem_sdiff.mp hT).2 (Finset.mem_inter.mp hU).2
      have prod := extend Z w pos n (fun S ht j hj => ih S.card ht S rfl j hj)
        T U dis (by rw [eq,hn])
      rw [eq] at prod
      have bound : p i ≤ x i * ∏ j ∈ U, w j :=
        (small i).trans (mul_le_mul_of_nonneg_left (dec U _ Finset.inter_subset_right) (hx i).1)
      have marginal := loss A i hi
      change _ ≤ p i * Z T at marginal
      have h₁ := mul_le_mul_of_nonneg_right bound (nonneg T)
      have h₂ := mul_le_mul_of_nonneg_left prod (hx i).1
      dsimp only [w] at *
      nlinarith only [marginal,h₁,h₂]
  simpa [unit,w] using extend Z w pos (S.card) (fun A _ j hj => step _ A rfl j hj)
    ∅ S (by simp) (by simp)

def avoids (E : ι → Set Ω) (S : Finset ι) : Set Ω := {ω | ∀ i ∈ S, ω ∉ E i}

/-- Appendix Theorem 7.4, stated on a probability space. A dependency
graph supplies independence from avoidance of every finite set of
nonneighbors. -/
theorem asymmetric [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ι → Set Ω) (meas : ∀ i, MeasurableSet (E i)) (neighbors : ι → Finset ι)
    (indep : ∀ i (S : Finset ι), i ∉ S → Disjoint S (neighbors i) →
      IndepSet (E i) (avoids E S) μ)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (small : ∀ i, μ.real (E i) ≤ x i * ∏ j ∈ neighbors i, (1-x j)) (S : Finset ι) :
    0 < (∏ j ∈ S, (1-x j)) ∧ (∏ j ∈ S, (1-x j)) ≤ μ.real (avoids E S) := by
  have empty : avoids E ∅ = univ := by ext; simp [avoids]
  have ins (A : Finset ι) i : avoids E (insert i A) = avoids E A \ (E i ∩ avoids E A) := by
    ext; simp [avoids]; tauto
  have measurable (A : Finset ι) : MeasurableSet (avoids E A) := by
    induction A using Finset.induction_on with
    | empty => rw [empty]; exact MeasurableSet.univ
    | insert i A _ ih => rw [ins]; exact ih.diff ((meas i).inter ih)
  refine ⟨Finset.prod_pos fun i _ => sub_pos.mpr (hx i).2,
    avoidance_bound (fun A => μ.real (avoids E A)) (fun _ => measureReal_nonneg)
      (by simp [empty]) neighbors (fun i => μ.real (E i)) x hx ?_ small S⟩
  intro A i fresh
  let T := A \ neighbors i
  have ind := indep i T (fun h => fresh (Finset.mem_sdiff.mp h).1)
    (Finset.disjoint_left.mpr fun _ hm hn => (Finset.mem_sdiff.mp hm).2 hn)
  have prob := ind.measure_inter_eq_mul
  have realprob := congrArg ENNReal.toReal prob
  rw [ENNReal.toReal_mul] at realprob
  have sub : E i ∩ avoids E A ⊆ E i ∩ avoids E T :=
    fun ω h => ⟨h.1,fun j hj => h.2 j (Finset.mem_sdiff.mp hj).1⟩
  change μ.real (avoids E A) - μ.real (avoids E (insert i A)) ≤ μ.real (E i) * μ.real (avoids E T)
  rw [ins,measureReal_diff Set.inter_subset_right ((meas i).inter (measurable A))]
  simpa only [sub_sub_cancel] using
    (measureReal_mono (μ := μ) sub).trans_eq realprob

end GenLimit.KleinbergWei.Banach.LocalLemma
