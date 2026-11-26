import GenLimit.Paper30_TimeSensitiveLanguageGeneration.RandomizedRuns
import GenLimit.Core.GenericGeneration

/-! # A uniform-rate obstruction to P30 Theorem 3

All target languages contain zero and otherwise occupy disjoint infinite
columns. Two exact presentations can agree on zero for the first t rounds.
Their outputs agree up to t. Each fresh distinct output is a hallucination
for at least one target. Integration preserves this lower bound.
-/
namespace GenLimit.TimeSensitive
open MeasureTheory Filter
open scoped Topology

def sharedRoot (z : ℕ) : Generic.Language ℕ := insert 0 (Set.range fun j => Nat.pair z j + 1)

private def delayRoot (z t n : ℕ) : ℕ :=
  if n ≤ t then 0 else Nat.pair z (n - (t+1)) + 1

theorem sharedRoot_infinite (z : ℕ) : (sharedRoot z).Infinite := by
  apply (Set.infinite_range_of_injective (f := fun j => Nat.pair z j + 1) ?_).mono
    (Set.subset_insert _ _)
  intro i j h
  exact (Nat.pair_eq_pair.mp (Nat.add_right_cancel h)).2

private theorem common_point {i j x : ℕ} (ne : i ≠ j)
    (hx : x ∈ sharedRoot i) (hy : x ∈ sharedRoot j) : x = 0 := by
  rcases hx with rfl | ⟨a,rfl⟩
  · rfl
  rcases hy with h | ⟨b,h⟩
  · exact h
  · exact (ne (Nat.pair_eq_pair.mp (Nat.add_right_cancel h)).1.symm).elim

theorem sharedRoot_injective : Function.Injective sharedRoot := by
  intro i j h
  by_contra ne
  have mem : Nat.pair i 0 + 1 ∈ sharedRoot i := Or.inr ⟨0,rfl⟩
  have := common_point ne mem (h ▸ mem)
  omega

private theorem delayRoot_presents (z t : ℕ) : Generic.Presents (delayRoot z t) (sharedRoot z) := by
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    unfold delayRoot
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨_,rfl⟩
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨0, by simp [delayRoot]⟩
    · exact ⟨t+1+j, by simp [delayRoot, show ¬t+1+j ≤ t by omega]⟩

private theorem pair_loss {Ω : Type*} [MeasurableSpace Ω] (A : RandomizedGenerator Ω)
    (t : ℕ) (ht : 0 < t) (ω : Ω) :
    1 ≤ A.loss (delayRoot 0 t) (sharedRoot 0) t ω +
      A.loss (delayRoot 1 t) (sharedRoot 1) t ω := by
  classical
  let s := A.run (delayRoot 0 t) ω
  let P := sequencePrefix s t
  have eq : sequencePrefix (A.run (delayRoot 1 t) ω) t = P := by
    ext x
    simp only [P, mem_sequencePrefix_iff]
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    rw [A.run_congr (n := t) (s := delayRoot 1 t) (r := delayRoot 0 t)
      (fun a ha => by simp [delayRoot, ha.le]) ω hj]
  have nozero : 0 ∉ P := by
    intro hz
    obtain ⟨n, _, h⟩ := (mem_sequencePrefix_iff s 0 t).mp hz
    have hf := A.fresh n (fun i => delayRoot 0 t i.val) ω (0 : Fin (n+1))
    exact hf (by simpa [s, RandomizedGenerator.run, delayRoot] using h)
  have card : P.card = t := sequencePrefix_card_eq s (A.distinct _ ω) t
  have sub : P ⊆ (P.filter fun x => x ∉ sharedRoot 0) ∪ (P.filter fun x => x ∉ sharedRoot 1) := by
    intro x hx
    by_cases h : x ∈ sharedRoot 0
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, fun h1 =>
        nozero (common_point (by decide : 0 ≠ 1) h h1 ▸ hx)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,h⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
  rw [card] at bound
  unfold RandomizedGenerator.loss hallucinationCount
  rw [eq, ← add_div, le_div_iff₀ (show (0:ℝ) < t by exact_mod_cast ht), one_mul]
  exact_mod_cast bound

/-- For each positive horizon, some target and exact enumeration have expected
hallucination rate at least one half. The same fixed countably infinite class
works for every randomized generator, irrespective of the deadline. -/
theorem uniform_rate_obstruction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedGenerator Ω) (t : ℕ) (ht : 0 < t) :
    ∃ z s, Generic.Presents s (sharedRoot z) ∧ 1/2 ≤ A.expectedRate μ s (sharedRoot z) t := by
  have h := integral_mono (μ := μ) (integrable_const (1:ℝ))
    ((A.integrable_loss μ (delayRoot 0 t) (sharedRoot 0) t).add
      (A.integrable_loss μ (delayRoot 1 t) (sharedRoot 1) t)) (pair_loss A t ht)
  simp only [Pi.add_apply] at h
  rw [integral_const, measureReal_univ_eq_one, one_smul, integral_add (A.integrable_loss ..) (A.integrable_loss ..)] at h
  change 1 ≤ A.expectedRate μ _ _ _ + A.expectedRate μ _ _ _ at h
  by_cases h0 : 1/2 ≤ A.expectedRate μ (delayRoot 0 t) (sharedRoot 0) t
  · exact ⟨0, _, delayRoot_presents 0 t, h0⟩
  · exact ⟨1, _, delayRoot_presents 1 t, by linarith⟩

/-- The uniform hallucination clause of Theorem 3 contradicts every vanishing
bound H, including each feasible rate in the theorem. -/
theorem no_uniform_vanishing_rate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedGenerator Ω)
    {H : ℕ → ℝ} (vanishes : Tendsto H atTop (𝓝 0)) :
    ¬∀ᶠ t in atTop, ∀ z s, Generic.Presents s (sharedRoot z) →
      A.expectedRate μ s (sharedRoot z) t ≤ H t := by
  intro uniform
  have small := vanishes.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨t, ht, bound, low⟩ := ((eventually_gt_atTop 0).and (uniform.and small)).exists
  obtain ⟨z,s,hp,bad⟩ := uniform_rate_obstruction μ A t ht
  exact low.not_ge (bad.trans (bound z s hp))

end GenLimit.TimeSensitive
