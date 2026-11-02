import GenLimit.Paper21_GenerationInMetricSpaces.CoveringGeometry
import GenLimit.Paper21_GenerationInMetricSpaces.UniformSufficiency
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.MetricSpace.Basic

/-!
# Failure of finite-union closure on the real line

Theorem 3.5 of Li--Raman--Tewari, arXiv:2602.07710v2.
Each class shares an unbounded arithmetic progression. A diagonal sequence
chooses one point between each pair of progression points, avoiding all
outputs on its earlier prefixes. It presents two fixed targets whose common
part is that sequence. Simultaneous eventual correctness is impossible.
-/

namespace GenLimit.MetricSpaces.FiniteUnion

open GenLimit.Generic

noncomputable section

def anchor (r offset : ℝ) (n : ℕ) : ℝ := 3 * r * ((n : ℝ) + 1) + offset

def Admissible (r ε : ℝ) (s : Stream ℝ) : Prop :=
  ∀ n, anchor r 0 n < s n ∧ s n < anchor r ε n

def targetClass (r ε offset : ℝ) : LanguageClass ℝ :=
  {L | ∃ s : Stream ℝ, Admissible r ε s ∧
    L = Set.range (anchor r offset) ∪ Set.range s}

theorem anchor_unbounded (r offset : ℝ) (hr : 0 < r) (b : ℝ) :
    ∃ n, b < anchor r offset n := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - offset) / (3 * r))
  have hmul := (div_lt_iff₀ (by positivity : 0 < 3 * r)).mp hn
  refine ⟨n, ?_⟩
  dsimp [anchor]
  nlinarith

theorem not_finiteCover_of_unboundedAbove
    {A : Set ℝ} (hA : ∀ b : ℝ, ∃ x ∈ A, b < x) (R : ℝ) :
    ¬ HasFiniteCover dist R A := by
  classical
  rintro ⟨centers, hcover⟩
  obtain ⟨x, hx, hlarge⟩ := hA ((∑ c ∈ centers, |c|) + R + 1)
  obtain ⟨c, hc, hcx⟩ := mem_closedNeighborhood_finset_iff.mp (hcover hx)
  have hcBound : c ≤ ∑ z ∈ centers, |z| :=
    (le_abs_self c).trans (Finset.single_le_sum (fun z _ => abs_nonneg z) hc)
  have hdiff : x - c ≤ |c - x| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  rw [Real.dist_eq] at hcx
  linarith

theorem anchor_not_finiteCover (r offset : ℝ) (hr : 0 < r) (R : ℝ) :
    ¬ HasFiniteCover dist R (Set.range (anchor r offset)) := by
  apply not_finiteCover_of_unboundedAbove
  intro b
  obtain ⟨n, hn⟩ := anchor_unbounded r offset hr b
  exact ⟨anchor r offset n, ⟨n, rfl⟩, hn⟩

theorem targetClass_uus (r ε offset : ℝ) (hr : 0 < r) :
    UniformlyUnboundedSupportAt dist r (targetClass r ε offset) := by
  apply uus_of_no_finite_cover_triple dist_self dist_comm dist_triangle hr.le
  rintro L ⟨s, _, rfl⟩ hcover
  exact anchor_not_finiteCover r offset hr (3 * r)
    (hcover.mono_set Set.subset_union_left)

theorem targetClass_uniform (r ε ε' offset : ℝ) (hr : 0 < r) (hε : 0 ≤ ε) :
    UniformlyGeneratableAt dist ε ε' (targetClass r ε offset) := by
  apply finite_scaleClosureDimension_implies_uniform dist_self hε
  refine ⟨0, ?_⟩
  rintro d _ ⟨S, _, _, hcover⟩
  apply anchor_not_finiteCover r offset hr ε'
  apply hcover.toFiniteCover.mono_set
  intro x hx L hL
  obtain ⟨s, _, rfl⟩ := hL.1
  exact Or.inl hx

theorem anchors_disjoint {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r) :
    Disjoint (Set.range (anchor r 0)) (Set.range (anchor r ε)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨n, rfl⟩ ⟨m, hm⟩
  by_cases hnm : n ≤ m
  · have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hmul := mul_le_mul_of_nonneg_left hcast (by positivity : 0 ≤ 3 * r)
    dsimp [anchor] at hm
    nlinarith
  · have hcast : (m : ℝ) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hnm)
    have hmul := mul_le_mul_of_nonneg_left hcast (by positivity : 0 ≤ 3 * r)
    dsimp [anchor] at hm
    nlinarith

/-- The output on any prefix of an already fixed history. -/
def pastOutput (G : Generator ℝ) (n : ℕ) (xs : Fin n → ℝ) (t : Fin (n + 1)) : ℝ :=
  G t (fun i => xs ⟨i, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩)

theorem exists_next_point (r ε : ℝ) (hε : 0 < ε)
    (G : Generator ℝ) (n : ℕ) (xs : Fin n → ℝ) :
    ∃ x, (anchor r 0 n < x ∧ x < anchor r ε n) ∧
      ∀ t : Fin (n + 1), x ≠ pastOutput G n xs t := by
  classical
  have hinterval : anchor r 0 n < anchor r ε n := by
    dsimp [anchor]
    linarith
  obtain ⟨x, hx, havoid⟩ := (Set.Ioo_infinite hinterval).exists_notMem_finset
    (Finset.univ.image (pastOutput G n xs))
  refine ⟨x, hx, ?_⟩
  intro t heq
  apply havoid
  exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, heq.symm⟩

def nextPoint (r ε : ℝ) (hε : 0 < ε)
    (G : Generator ℝ) (n : ℕ) (xs : Fin n → ℝ) : ℝ :=
  Classical.choose (exists_next_point r ε hε G n xs)

theorem nextPoint_spec (r ε : ℝ) (hε : 0 < ε)
    (G : Generator ℝ) (n : ℕ) (xs : Fin n → ℝ) :
    (anchor r 0 n < nextPoint r ε hε G n xs ∧
      nextPoint r ε hε G n xs < anchor r ε n) ∧
    ∀ t : Fin (n + 1), nextPoint r ε hε G n xs ≠ pastOutput G n xs t :=
  Classical.choose_spec (exists_next_point r ε hε G n xs)

def diagonal (r ε : ℝ) (hε : 0 < ε) (G : Generator ℝ) (n : ℕ) : ℝ :=
  Nat.strongRecOn n fun n previous =>
    nextPoint r ε hε G n (fun i => previous i i.isLt)

theorem diagonal_eq (r ε : ℝ) (hε : 0 < ε) (G : Generator ℝ) (n : ℕ) :
    diagonal r ε hε G n = nextPoint r ε hε G n (fun i => diagonal r ε hε G i) := by
  unfold diagonal
  rw [Nat.strongRecOn_eq]

theorem diagonal_admissible (r ε : ℝ) (hε : 0 < ε) (G : Generator ℝ) :
    Admissible r ε (diagonal r ε hε G) := by
  intro n
  rw [diagonal_eq r ε hε G n]
  exact (nextPoint_spec r ε hε G n _).1

theorem diagonal_avoids_future (r ε : ℝ) (hε : 0 < ε) (G : Generator ℝ)
    {t n : ℕ} (htn : t ≤ n) :
    diagonal r ε hε G n ≠ output G (diagonal r ε hε G) t := by
  rw [diagonal_eq r ε hε G n]
  exact (nextPoint_spec r ε hε G n _).2 ⟨t, Nat.lt_succ_of_le htn⟩

theorem presentation_with_anchor {r ε offset : ℝ} {s : Stream ℝ}
    (hε : 0 ≤ ε) (hclose : ∀ n, dist (s n) (anchor r offset n) ≤ ε) :
    MetricPresentation dist ε s (Set.range (anchor r offset) ∪ Set.range s) := by
  constructor
  · exact Set.subset_union_right
  · rintro x (⟨n, rfl⟩ | ⟨n, rfl⟩) η hη
    · exact ⟨s n, ⟨n, rfl⟩, (hclose n).trans_lt hη⟩
    · exact ⟨s n, ⟨n, rfl⟩, by rw [dist_self]; linarith⟩

theorem admissible_presentations {r ε : ℝ} (hε : 0 < ε) {s : Stream ℝ}
    (hs : Admissible r ε s) :
    MetricPresentation dist ε s (Set.range (anchor r 0) ∪ Set.range s) ∧
    MetricPresentation dist ε s (Set.range (anchor r ε) ∪ Set.range s) := by
  constructor
  · apply presentation_with_anchor hε.le
    intro n
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (hs n).1)]
    have := (hs n).2
    dsimp [anchor] at *
    linarith
  · apply presentation_with_anchor hε.le
    intro n
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (hs n).2)]
    have := (hs n).1
    dsimp [anchor] at *
    linarith

theorem union_not_generatable {r ε ε' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r) (hε' : 0 ≤ ε') :
    ¬ GeneratableInLimitAt dist ε ε'
      (targetClass r ε 0 ∪ targetClass r ε ε) := by
  rintro ⟨G, hG⟩
  let s := diagonal r ε hε G
  have hs : Admissible r ε s := diagonal_admissible r ε hε G
  obtain ⟨hpA, hpB⟩ := admissible_presentations hε hs
  obtain ⟨TA, hA⟩ := hG _ (Or.inl ⟨s, hs, rfl⟩) s hpA
  obtain ⟨TB, hB⟩ := hG _ (Or.inr ⟨s, hs, rfl⟩) s hpB
  let t := max TA TB
  have hcorrectA := hA t (Nat.le_max_left _ _)
  have hcorrectB := hB t (Nat.le_max_right _ _)
  have hout : output G s t ∈ Set.range s := by
    rcases hcorrectA.1 with hA | hS
    · rcases hcorrectB.1 with hB | hS
      · exact (Set.disjoint_left.mp (anchors_disjoint hr hε hεr) hA hB).elim
      · exact hS
    · exact hS
  obtain ⟨n, hn⟩ := hout
  by_cases hnt : n < t
  · apply hcorrectA.2
    apply mem_closedNeighborhood_finset_iff.mpr
    refine ⟨s n, value_mem_sample hnt, ?_⟩
    rw [← hn, dist_self]
    exact hε'
  · exact diagonal_avoids_future r ε hε G (Nat.le_of_not_gt hnt) hn

end

end GenLimit.MetricSpaces.FiniteUnion

namespace GenLimit.MetricSpaces

/-- Theorem 3.5, arXiv v2: even on the real line, a union of two uniformly
generatable UUS classes can fail to be generatable in the limit. -/
theorem theorem_3_5_failure_of_finite_union
    {r ε ε' : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε' : 0 < ε')
    (hεr : ε ≤ r) (_hε'r : ε' ≤ r) :
    ∃ H₁ H₂ : GenLimit.Generic.LanguageClass ℝ,
      UniformlyUnboundedSupportAt dist r H₁ ∧
      UniformlyUnboundedSupportAt dist r H₂ ∧
      UniformlyGeneratableAt dist ε ε' H₁ ∧
      UniformlyGeneratableAt dist ε ε' H₂ ∧
      ¬ GeneratableInLimitAt dist ε ε' (H₁ ∪ H₂) :=
  ⟨FiniteUnion.targetClass r ε 0, FiniteUnion.targetClass r ε ε,
    FiniteUnion.targetClass_uus r ε 0 hr, FiniteUnion.targetClass_uus r ε ε hr,
    FiniteUnion.targetClass_uniform r ε ε' 0 hr hε.le,
    FiniteUnion.targetClass_uniform r ε ε' ε hr hε.le,
    FiniteUnion.union_not_generatable hr hε hεr hε'.le⟩

end GenLimit.MetricSpaces
