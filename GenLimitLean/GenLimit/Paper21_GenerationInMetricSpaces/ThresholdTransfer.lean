import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Transfer of non-uniform thresholds

Lemma C.1 of arXiv:2602.07710v2. The maximum of finitely many target
thresholds works on their common part. The proof does not require UUS or
coverage for that common part, as emphasized in the revised appendix.
-/

namespace GenLimit.MetricSpaces

open GenLimit.Generic

/-- The common-part transfer preserves a shared uniform threshold. -/
theorem uniform_threshold_transfer
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ}
    {H family : LanguageClass α} {q d : ℕ} (hq : 0 < q)
    (T : Fin q → Language α) (hempty : (⋂ i, T i) = ∅)
    (hTargets : ∀ S, S ∈ family → ∀ i, S ∪ T i ∈ H)
    {G : Generator α} (hG : IsUniformGeneratorAt ρ ε ε' G H d) :
    IsUniformGeneratorAt ρ ε ε' G family d := by
  intro S hS stream hstream t ht s hts
  have hcorrect : ∀ i, MetricCorrectAt ρ ε' G (S ∪ T i) stream s :=
    fun i => hG _ (hTargets S hS i) stream (hstream.trans Set.subset_union_left) t ht s hts
  refine ⟨?_, (hcorrect ⟨0, hq⟩).2⟩
  by_contra hnot
  have hall : output G stream s ∈ ⋂ i, T i :=
    Set.mem_iInter.mpr (fun i => (hcorrect i).1.resolve_left hnot)
  rw [hempty] at hall
  exact hall

/-- Lemma C.1. For a finite nonempty family of auxiliary sets with empty
intersection, a non-uniform generator on every `S ∪ T i` has a threshold
that forces all later outputs to lie in `S` and to be novel.

The source's UUS and nonempty-support assumptions are unnecessary for this
conditional transfer statement. -/
theorem lemma_C_1_threshold_transfer
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ}
    {H family : LanguageClass α} {q : ℕ} (hq : 0 < q)
    (T : Fin q → Language α) (hempty : (⋂ i, T i) = ∅)
    (hTargets : ∀ S, S ∈ family → ∀ i, S ∪ T i ∈ H)
    {G : Generator α} (hG : IsNonuniformGeneratorAt ρ ε ε' G H) :
    ∀ S, S ∈ family → ∃ d : ℕ,
      ∀ stream : Stream α, StreamIn stream S →
      ∀ t, CoveringNumberAtLeast ρ ε (sample stream t : Set α) d →
      ∀ s, t ≤ s → MetricCorrectAt ρ ε' G S stream s := by
  classical
  intro S hS
  have hThresholds := fun i => hG (S ∪ T i) (hTargets S hS i)
  choose d hd using hThresholds
  refine ⟨Finset.univ.sup d, ?_⟩
  intro stream hstream t ht s hts
  have hcorrect : ∀ i, MetricCorrectAt ρ ε' G (S ∪ T i) stream s := by
    intro i
    apply hd i stream (hstream.trans Set.subset_union_left) t _ s hts
    intro centers hcover
    exact (Finset.le_sup (f := d) (Finset.mem_univ i)).trans (ht centers hcover)
  refine ⟨?_, (hcorrect ⟨0, hq⟩).2⟩
  by_contra hnot
  have hall : output G stream s ∈ ⋂ i, T i := by
    apply Set.mem_iInter.mpr
    intro i
    exact (hcorrect i).1.resolve_left hnot
  rw [hempty] at hall
  exact hall

end GenLimit.MetricSpaces
