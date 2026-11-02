import GenLimit.Paper21_GenerationInMetricSpaces.HilbertGeometry
import GenLimit.Paper21_GenerationInMetricSpaces.ThresholdTransfer
import GenLimit.Support.StreamPrefix
import Mathlib.Data.Set.Card

/-!
# A two-hypothesis obstruction at reversed novelty scales

Example B.3 of arXiv:2602.07710v2. The proof uses the finite-threshold
transfer of Lemma C.1 and the orthogonal covering estimate directly.
-/

namespace GenLimit.MetricSpaces.ExampleB3

open GenLimit.Generic GenLimit.Support HilbertAxisReservoir

noncomputable section

def offset (b : Bool) : ℕ := if b then 2 else 1

def small (a : ℝ) (k : ℕ) : Hilbert2 := axisPoint a (3 * (k + 1))

def remote (r : ℝ) (b : Bool) : Set Hilbert2 :=
  Set.range (fun k : ℕ => axisPoint (2 * r) (3 * (k + 1) + offset b))

def common (a : ℝ) : Set Hilbert2 := {0} ∪ Set.range (small a)

def target (a r : ℝ) (b : Bool) : Set Hilbert2 := common a ∪ remote r b

def family (a r : ℝ) : LanguageClass Hilbert2 := Set.range (target a r)

theorem remote_disjoint {r : ℝ} (hr : 0 < r) {b c : Bool} (hbc : b ≠ c) :
    Disjoint (remote r b) (remote r c) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨i, rfl⟩ ⟨j, hj⟩
  have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero
    (by positivity : (2 * r : ℝ) ≠ 0) hj).2
  cases b <;> cases c <;> simp_all [offset] <;> omega

theorem family_uus {a r : ℝ} (hr : 0 < r) :
    UniformlyUnboundedSupportAt dist r (family a r) := by
  apply uus_of_infinite_isolated_orthogonal
    (R := 2 * r) (δ := 2 * r) hr.le (by linarith) (by linarith)
  rintro L ⟨b, rfl⟩
  refine ⟨remote r b, ?_, Set.subset_union_right, ?_, ?_, ?_⟩
  · apply axis_range_infinite (by positivity : (2 * r : ℝ) ≠ 0)
    intro i j hij
    dsimp only at hij
    omega
  · exact axis_range_norm (by positivity) _
  · exact axis_range_orthogonal _ _
  · rintro x ⟨k, rfl⟩ y ((hy | ⟨j, rfl⟩) | ⟨j, rfl⟩) hnear
    · have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      subst y
      simp [abs_of_pos (by positivity : 0 < 2 * r)] at hnear
    · have hcoord : 3 * (j + 1) ≠ 3 * (k + 1) + offset b := by
        cases b <;> simp [offset] <;> omega
      have hfar := abs_amplitude_le_dist_axisPoint_of_ne a (2 * r) hcoord
      rw [abs_of_pos (by positivity : 0 < 2 * r)] at hfar
      exact (not_lt_of_ge hfar hnear).elim
    · by_cases hjk : j = k
      · subst j; rfl
      · have hcoord : 3 * (j + 1) + offset b ≠ 3 * (k + 1) + offset b := by omega
        have hfar := abs_amplitude_le_dist_axisPoint_of_ne (2 * r) (2 * r) hcoord
        rw [abs_of_pos (by positivity : 0 < 2 * r)] at hfar
        exact (not_lt_of_ge hfar hnear).elim

theorem not_nonuniform {r a ε ε' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεa : ε < a) (haε' : a < ε') :
    ¬ NonuniformlyGeneratableAt dist ε ε' (family a r) := by
  classical
  rintro ⟨G, hG⟩
  let T : Fin 2 → Set Hilbert2 := fun i => remote r (decide (i.val ≠ 0))
  have hEmpty : (⋂ i, T i) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h0 := Set.mem_iInter.mp hx ⟨0, by decide⟩
    have h1 := Set.mem_iInter.mp hx ⟨1, by decide⟩
    exact Set.disjoint_left.mp (remote_disjoint hr (by decide : false ≠ true))
      (by simpa [T] using h0) (by simpa [T] using h1)
  have hTargets : ∀ S, S ∈ ({common a} : LanguageClass Hilbert2) → ∀ i, S ∪ T i ∈ family a r := by
    intro S hS i
    have hEq : S = common a := Set.mem_singleton_iff.mp hS
    subst S
    exact ⟨decide (i.val ≠ 0), rfl⟩
  obtain ⟨d, hd⟩ := lemma_C_1_threshold_transfer (by decide : 0 < 2) T hEmpty hTargets hG
    (common a) (by simp)
  let stream := prependStream [0] (small a)
  have hstream : StreamIn stream (common a) := by
    change Set.range stream ⊆ common a
    rw [range_prependStream]
    simp [common]
  have ha : 0 < a := hε.trans hεa
  have hA : (Set.range (small a)).Infinite := by
    apply axis_range_infinite ha.ne' _
    intro i j hij
    dsimp only at hij
    omega
  have hArange : Set.range (small a) ⊆ Set.range stream := by
    rintro x ⟨i, rfl⟩
    exact ⟨1 + i, prependStream_add [0] (small a) i⟩
  obtain ⟨t, ht⟩ := prefix_covering_unbounded_of_infinite_orthogonal
    hA hArange ha hε.le hεa (axis_range_norm ha.le _)
    (axis_range_orthogonal _ _) d
  let s := max t 1
  have hcorrect := hd stream hstream t ht s (Nat.le_max_left _ _)
  have hzero : (0 : Hilbert2) ∈ sample stream s := by
    apply mem_sample_iff.mpr
    exact ⟨0, lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_right _ _), rfl⟩
  apply hcorrect.2
  apply inClosedNeighborhood_mono_centers (show ({0} : Set Hilbert2) ⊆
      (sample stream s : Set Hilbert2) from fun x hx => by simpa using Set.mem_singleton_iff.mp hx ▸ hzero)
  rw [mem_closedNeighborhood_singleton_iff]
  rcases hcorrect.1 with h0 | ⟨i, hi⟩
  · have : output G stream s = 0 := Set.mem_singleton_iff.mp h0
    rw [this, dist_self]
    linarith
  · rw [← hi, dist_zero_left]
    simp only [small, norm_axisPoint, abs_of_pos ha]
    exact haε'.le

theorem targets_distinct {a r : ℝ} (hr : 0 < r) : target a r false ≠ target a r true := by
  intro heq
  have hx : axisPoint (2 * r) 4 ∈ target a r false := Or.inr ⟨0, rfl⟩
  rw [heq] at hx
  rcases hx with (hzero | ⟨j, hj⟩) | hremote
  · have hnorm := congrArg norm (Set.mem_singleton_iff.mp hzero)
    simp only [norm_axisPoint, norm_zero, abs_of_pos (by positivity : 0 < 2 * r)] at hnorm
    linarith
  · change axisPoint a (3 * (j + 1)) = axisPoint (2 * r) 4 at hj
    have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero
      (by positivity : (2 * r : ℝ) ≠ 0) hj.symm).2
    omega
  · exact Set.disjoint_left.mp (remote_disjoint hr (by decide : false ≠ true))
      (show axisPoint (2 * r) 4 ∈ remote r false from ⟨0, rfl⟩) hremote

theorem family_eq_pair (a r : ℝ) : family a r = {target a r false, target a r true} := by
  ext L
  simp only [family, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, rfl⟩
    cases b <;> simp
  · rintro (h | h)
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩

end

end GenLimit.MetricSpaces.ExampleB3

namespace GenLimit.MetricSpaces

/-- Example B.3: at reversed novelty scales a two-hypothesis r-UUS class
in genuine real Hilbert space need not be non-uniformly generatable. -/
theorem example_B_3 {r ε ε' : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (hεε' : ε < ε') (_hε'r : ε' ≤ r) :
    ∃ H : GenLimit.Generic.LanguageClass HilbertAxisReservoir.Hilbert2,
      H.ncard = 2 ∧ UniformlyUnboundedSupportAt dist r H ∧
      ¬ NonuniformlyGeneratableAt dist ε ε' H := by
  let a := (ε + ε') / 2
  refine ⟨ExampleB3.family a r, ?_, ExampleB3.family_uus hr,
    ExampleB3.not_nonuniform hr hε ?_ ?_⟩
  · rw [ExampleB3.family_eq_pair]
    exact Set.ncard_pair (ExampleB3.targets_distinct hr)
  · dsimp [a]; linarith
  · dsimp [a]; linarith

end GenLimit.MetricSpaces
