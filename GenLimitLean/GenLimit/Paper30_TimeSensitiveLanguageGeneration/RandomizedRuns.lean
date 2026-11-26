import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyRun
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.DensityReduction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Nat.Pairing

/-! # Causal random-tape runs and the source's expected hallucination rate -/
namespace GenLimit.TimeSensitive

open MeasureTheory

theorem sequencePrefix_card_eq (s : ℕ → α) (hs : Function.Injective s) (t : ℕ) :
    (sequencePrefix s t).card = t := by
  classical
  unfold sequencePrefix
  rw [Finset.card_image_of_injective _ hs, Finset.card_range]

structure RandomizedGenerator (Ω : Type*) [MeasurableSpace Ω] where
  choose : ∀ t : ℕ, (Fin (t+1) → ℕ) → Ω → ℕ
  measurable_choose : ∀ t xs, Measurable (choose t xs)
  fresh : ∀ t xs ω i, choose t xs ω ≠ xs i
  distinct : ∀ (s : ℕ → ℕ) ω, Function.Injective (fun t => choose t (fun i => s i.val) ω)

namespace RandomizedGenerator
variable {Ω : Type*} [MeasurableSpace Ω] (A : RandomizedGenerator Ω)

def run (s : ℕ → ℕ) (ω : Ω) (t : ℕ) : ℕ :=
  A.choose t (fun i => s i.val) ω

theorem run_congr {s r : ℕ → ℕ} {n : ℕ} (agree : ∀ j < n, s j = r j)
    (ω : Ω) {j : ℕ} (hj : j < n) : A.run s ω j = A.run r ω j := by
  unfold run
  congr 1
  funext i
  exact agree _ (by have := i.isLt; omega)

noncomputable def loss (s : ℕ → ℕ) (K : Set ℕ) (t : ℕ) (ω : Ω) : ℝ :=
  (hallucinationCount (A.run s ω) K t : ℝ) / t

theorem loss_nonneg (s : ℕ → ℕ) (K : Set ℕ) (t : ℕ) (ω : Ω) :
    0 ≤ A.loss s K t ω := by unfold loss; positivity

theorem loss_le_one (s : ℕ → ℕ) (K : Set ℕ) (t : ℕ) (ω : Ω) :
    A.loss s K t ω ≤ 1 := by
  classical
  unfold loss
  by_cases h : t = 0
  · simp [h]
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)]
    have card := sequencePrefix_card_le (A.run s ω) t
    have hcount : hallucinationCount (A.run s ω) K t ≤ t :=
      (Finset.card_filter_le _ _).trans card
    exact_mod_cast hcount

theorem measurable_loss (s : ℕ → ℕ) (K : Set ℕ) (t : ℕ) :
    Measurable (A.loss s K t) := by
  classical
  let stat (x : Fin t → ℕ) : ℝ :=
    (((Finset.univ.image x).filter fun y => y ∉ K).card : ℝ) / t
  have eq (ω : Ω) : A.loss s K t ω = stat (fun i => A.run s ω i.val) := by
    have same : sequencePrefix (A.run s ω) t =
        Finset.univ.image (fun i : Fin t => A.run s ω i.val) := by
      ext y
      simp only [sequencePrefix, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
      exact ⟨fun ⟨j,hj,hy⟩ => ⟨⟨j,hj⟩,hy⟩, fun ⟨i,hi⟩ => ⟨i,i.isLt,hi⟩⟩
    simp only [loss, hallucinationCount, stat, same]
  rw [funext eq]
  exact (measurable_of_countable stat).comp (measurable_pi_lambda _ fun i => A.measurable_choose _ _)

theorem integrable_loss (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℕ → ℕ) (K : Set ℕ) (t : ℕ) : Integrable (A.loss s K t) μ :=
  Integrable.of_bound (A.measurable_loss s K t).aestronglyMeasurable 1
    (.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (A.loss_nonneg ..)]; exact A.loss_le_one ..)

noncomputable def expectedRate (μ : Measure Ω) (s : ℕ → ℕ) (K : Set ℕ) (t : ℕ) : ℝ :=
  ∫ ω, A.loss s K t ω ∂μ

end RandomizedGenerator
end GenLimit.TimeSensitive
