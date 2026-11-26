import GenLimit.Paper25_PrivateGenerationAndIdentification.ContinualComposition
import Mathlib.Data.Nat.Find

/-! A causal release repeats the last completed epoch, using independent
epoch draws conditional on the input stream. -/
namespace GenLimit.PrivateLimit

open Privacy MeasureTheory Set Filter
open scoped Classical ENNReal
noncomputable section

namespace Epoch

def latest (finish : ℕ → ℕ) (t : ℕ) := Nat.findGreatest (fun k => finish k ≤ t) t

theorem available (finish : ℕ → ℕ) (hz : finish 0 = 0) (t : ℕ) : finish (latest finish t) ≤ t :=
  Nat.findGreatest_spec (P := fun k => finish k ≤ t) (Nat.zero_le t) (by dsimp; rw [hz]; omega)

theorem eventually_latest (finish : ℕ → ℕ) (k : ℕ) : ∀ᶠ t in atTop, k ≤ latest finish t := by
  filter_upwards [eventually_ge_atTop (max k (finish k))] with t ht
  exact Nat.le_findGreatest ((le_max_left ..).trans ht) ((le_max_right ..).trans ht)

def playback (finish : ℕ → ℕ) (y : ℕ → ℕ) (t : ℕ) := y (latest finish t)

theorem measurable_playback (finish : ℕ → ℕ) : Measurable (playback finish) :=
  measurable_pi_lambda _ (fun t => measurable_pi_apply (latest finish t))

def productLaw (q : (ℕ → ℕ) → ℕ → PMF ℕ) (s : ℕ → ℕ) :=
  Measure.infinitePi fun k => (q s k).toMeasure

instance (q : (ℕ → ℕ) → ℕ → PMF ℕ) (s : ℕ → ℕ) : IsProbabilityMeasure (productLaw q s) := by
  unfold productLaw; infer_instance

def release (finish : ℕ → ℕ) (hz : finish 0 = 0) (q : (ℕ → ℕ) → ℕ → PMF ℕ)
    (depends : ∀ u v k, (∀ j ≤ finish k, u j = v j) → q u k = q v k) : ContinualRelease ℕ ℕ where
  law s := (productLaw q s).map (playback finish)
  probability _ := Measure.isProbabilityMeasure_map (measurable_playback finish).aemeasurable
  causal n u v agree E hm := by
    let I := Finset.univ.image fun i : Fin n => latest finish i.val
    let index (i : Fin n) : I := ⟨latest finish i.val,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    let B := (fun g : I → ℕ => fun i : Fin n => g (index i)) ⁻¹' E
    have hB : MeasurableSet B := (measurable_pi_lambda _ (fun i => measurable_pi_apply (index i))) hm
    have event (s : ℕ → ℕ) :
        ((productLaw q s).map (playback finish)) ((fun y i => y (i : Fin n)) ⁻¹' E) =
          (Measure.pi (fun j : I => (q s j.val).toMeasure)) B := by
      rw [Measure.map_apply (measurable_playback finish)
        ((measurable_pi_lambda _ (fun i : Fin n => measurable_pi_apply i.val)) hm)]
      change (Measure.infinitePi fun k => (q s k).toMeasure) (cylinder I B) = _
      exact Measure.infinitePi_cylinder (fun k => (q s k).toMeasure) (s := I) (S := B) hB
    rw [event,event]
    have same (j : I) : q u j.val = q v j.val := by
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp j.property
      apply depends
      intro a ha
      exact agree a ((ha.trans (hi ▸ available finish hz i.val)).trans_lt i.isLt)
    simp_rw [same]

theorem release_private (finish : ℕ → ℕ) (hz : finish 0 = 0) (q : (ℕ → ℕ) → ℕ → PMF ℕ)
    (depends : ∀ u v k, (∀ j ≤ finish k, u j = v j) → q u k = q v k) {ε : ℝ}
    (dp : DifferentiallyPrivate ε 0 (productLaw q)) :
    DifferentiallyPrivate ε 0 (release finish hz q depends).law :=
  private_transcript_map dp (measurable_playback finish)

theorem release_stabilizes (finish : ℕ → ℕ) (hz : finish 0 = 0) (q : (ℕ → ℕ) → ℕ → PMF ℕ)
    (depends : ∀ u v k, (∀ j ≤ finish k, u j = v j) → q u k = q v k) (s : ℕ → ℕ) (z : ℕ)
    (stable : ∀ᵐ y ∂productLaw q s, ∀ᶠ k in atTop, y k = z) :
    ∀ᵐ y ∂(release finish hz q depends).law s, ∃ T, ∀ t ≥ T, y t = z := by
  change ∀ᵐ y ∂(productLaw q s).map (playback finish), _
  apply (ae_map_iff (measurable_playback finish).aemeasurable ?_).mpr
  · filter_upwards [stable] with y hy
    obtain ⟨k,hk⟩ := eventually_atTop.mp hy
    exact eventually_atTop.mp ((eventually_latest finish k).mono (fun t ht => hk _ ht))
  · simp only [setOf_exists,setOf_forall]
    refine MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ => ?_
    change MeasurableSet ((fun y : ℕ → ℕ => y t) ⁻¹' {z})
    exact (measurable_pi_apply t) (measurableSet_singleton z)

end Epoch
end
end GenLimit.PrivateLimit
