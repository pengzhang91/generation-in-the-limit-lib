import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! A finite minimum with a distinguished entry, including an empty index set. -/
namespace GenLimit.PriceOfPrivacy.FiniteMinimum

open scoped Classical
noncomputable section

def lower (r : ℝ) (S : Finset ι) (f : ι → ℝ) : ℝ :=
  (insert r (S.image f)).min' (by simp)

theorem lower_anchor (r : ℝ) (S : Finset ι) (f : ι → ℝ) : lower r S f ≤ r :=
  Finset.min'_le _ _ (Finset.mem_insert_self ..)

theorem lower_entry {S : Finset ι} (r : ℝ) (f : ι → ℝ) {i : ι} (hi : i ∈ S) :
    lower r S f ≤ f i := Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hi))

theorem le_lower {b r : ℝ} {S : Finset ι} {f : ι → ℝ} (anchor : b ≤ r)
    (all : ∀ i ∈ S, b ≤ f i) : b ≤ lower r S f := by
  apply Finset.le_min'
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact anchor
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact all i hi

theorem lower_shift {r t d : ℝ} {S : Finset ι} {f g : ι → ℝ}
    (anchor : r-t ≤ d) (all : ∀ i ∈ S, f i-g i ≤ d) :
    lower r S f - lower t S g ≤ d := by
  have h : lower r S f - d ≤ lower t S g := le_lower
    (by linarith [lower_anchor r S f]) (fun i hi => by linarith [lower_entry r f hi,all i hi])
  linarith

end
end GenLimit.PriceOfPrivacy.FiniteMinimum
