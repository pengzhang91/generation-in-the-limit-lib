import GenLimit.NoRegretLanguageGeneration.CapacityBounds
import Mathlib.Tactic.Ring

namespace PredictionToGeneration
open scoped ENNReal

noncomputable def signedFactor (η : ℝ≥0∞) : Bool → Bool → ℝ≥0∞
  | false, true => 1 + η
  | true, false => 1 - η
  | _, _ => 1

theorem capacity_four_le (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (n : Nat) (z x : X) :
    capacity H w n ≤
      capacity (restrict (restrict H z false) x false) w n +
      capacity (restrict (restrict H z false) x true) w n +
      (capacity (restrict (restrict H z true) x false) w n +
      capacity (restrict (restrict H z true) x true) w n) :=
  (capacity_partition_le H w n z).trans (add_le_add
    (capacity_partition_le (restrict H z false) w n x)
    (capacity_partition_le (restrict H z true) w n x))

/-- The signed update lemma, including the endpoint parameters zero and one. -/
theorem capacity_agnostic_update (H : HypothesisClass X) (w : Hypothesis X → ℝ≥0∞)
    (n : Nat) (z x : X) (η : ℝ≥0∞) (hη : η ≤ 1)
    (hmax : capacity (restrict H x true) w (n+1) ≤ capacity (restrict H z true) w (n+1)) :
    capacity H (fun h => signedFactor η (h z) (h x) * w h) n ≤ capacity H w (n+2) := by
  let C := fun a b => capacity (restrict (restrict H z a) x b) w n
  let P := capacity H w (n+2)
  have hcoeff (a b : Bool) :
      capacity (restrict (restrict H z a) x b) (fun h => signedFactor η (h z) (h x) * w h) n =
        signedFactor η a b * C a b := by
    rw [← capacity_homogeneous]
    apply capacity_congr (fun _ => Iff.rfl)
    intro h hh
    rw [hh.1.2, hh.2]
  have hu : capacity H (fun h => signedFactor η (h z) (h x) * w h) n ≤
      C false false + (1+η)*C false true + ((1-η)*C true false + C true true) := by
    have ht := capacity_four_le H (fun h => signedFactor η (h z) (h x) * w h) n z x
    rw [hcoeff false false, hcoeff false true, hcoeff true false, hcoeff true true] at ht
    simpa only [signedFactor, one_mul] using ht
  have hbase : C false false + C false true + (C true false + C true true) ≤ P :=
    (add_le_add (capacity_split_le (restrict H z false) w n x)
      (capacity_split_le (restrict H z true) w n x)).trans (capacity_split_le H w (n+1) z)
  have hright : C false true + C true true ≤ capacity (restrict H z true) w (n+1) := by
    have ht := capacity_split_le (restrict H x true) w n z
    rw [capacity_restrict_comm H w n x z true false,
      capacity_restrict_comm H w n x z true true] at ht
    exact ht.trans hmax
  have hdouble : C false false + C false true + (C false true + C true true) ≤ P :=
    (add_le_add (capacity_split_le (restrict H z false) w n x) hright).trans
      (capacity_split_le H w (n+1) z)
  have he : (1 - η) + η = 1 := tsub_add_cancel_of_le hη
  apply hu.trans
  calc
    _ = ((1-η)+η)*C false false + (((1-η)+η)+η)*C false true +
        ((1-η)*C true false + ((1-η)+η)*C true true) := by rw [he]; simp
    _ = (1-η)*(C false false + C false true + (C true false + C true true)) +
        η*(C false false + C false true + (C false true + C true true)) := by ring
    _ ≤ (1-η)*P + η*P := add_le_add (mul_le_mul_left' hbase _) (mul_le_mul_left' hdouble _)
    _ = P := by rw [← add_mul, he, one_mul]

end PredictionToGeneration

