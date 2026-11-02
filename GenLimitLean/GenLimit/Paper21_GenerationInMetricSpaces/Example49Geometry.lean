import GenLimit.Paper21_GenerationInMetricSpaces.ReservoirGeneration
import GenLimit.Paper21_GenerationInMetricSpaces.BlockDiagonal
import GenLimit.Paper21_GenerationInMetricSpaces.RealLineThresholdNegative

/-!
# Example 4.9: the source class and four disjoint coordinate families

The indices satisfy `2 ≤ k`. All towers use positive exponents. Keeping
the four residue classes modulo four separate permits equal scale values.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example49

open GenLimit.Generic

noncomputable section

def indices : Set ℕ := {k | 2 ≤ k}

def U (r : ℝ) (k : ℕ) : Hilbert2 := axisPoint (2 * r) (4 * k)
def A (ε : ℝ) (k : ℕ) : Hilbert2 := axisPoint ε (4 * k + 1)
def B (ε : ℝ) (k : ℕ) : Hilbert2 := axisPoint ε (4 * k + 2)
def G (ε : ℝ) (k : ℕ) : Hilbert2 := axisPoint ε (4 * k + 3)

def optimal (r ε' : ℝ) (I : Set ℕ) : Set Hilbert2 :=
  {x | ∃ k ∈ I, x = U r k} ∪ {x | ∃ k ∈ I, ∃ n : ℕ, x = G ε' (k ^ (n + 1))}

def target (r ε₁ ε₂ ε' : ℝ) (I₁ I₂ J : Set ℕ) : Set Hilbert2 :=
  {0} ∪ (optimal r ε' I₁ ∪ ({x | ∃ k ∈ I₂, x = A ε₁ k} ∪ {x | ∃ k ∈ J, x = B ε₂ k}))

def family (r ε₁ ε₂ ε' : ℝ) : LanguageClass Hilbert2 :=
  {L | ∃ I₁ I₂ J : Set ℕ, I₁.Infinite ∧ I₂.Infinite ∧ J.Finite ∧
    I₁ ⊆ indices ∧ I₂ ⊆ indices ∧ J ⊆ indices ∧ L = target r ε₁ ε₂ ε' I₁ I₂ J}

theorem target_axisSupported (r ε₁ ε₂ ε' : ℝ) (I₁ I₂ J : Set ℕ) :
    AxisSupported (target r ε₁ ε₂ ε' I₁ I₂ J) := by
  intro x hx
  rcases hx with hzero | ((hU | hG) | (hA | hB))
  · exact ⟨0, 0, by simpa using hzero⟩
  · obtain ⟨k, _, rfl⟩ := hU
    exact ⟨2 * r, 4 * k, rfl⟩
  · obtain ⟨k, _, n, rfl⟩ := hG
    exact ⟨ε', 4 * k ^ (n + 1) + 3, rfl⟩
  · obtain ⟨k, _, rfl⟩ := hA
    exact ⟨ε₁, 4 * k + 1, rfl⟩
  · obtain ⟨k, _, rfl⟩ := hB
    exact ⟨ε₂, 4 * k + 2, rfl⟩

theorem coordinate_dist_lower (c d : ℝ) {i j : ℕ} (hij : i ≠ j) :
    |c| ≤ dist (axisPoint d j) (axisPoint c i) := by
  simpa only [hilbertDistance] using abs_amplitude_le_dist_axisPoint_of_ne d c hij.symm

theorem u_isolated {r ε₁ ε₂ ε' : ℝ} (hr : 0 < r) {I₁ I₂ J : Set ℕ}
    {k : ℕ} {x : Hilbert2} (hx : x ∈ target r ε₁ ε₂ ε' I₁ I₂ J)
    (hclose : dist x (U r k) < 2 * r) : x = U r k := by
  rcases hx with hzero | ((hU | hG) | (hA | hB))
  · have hx0 : x = 0 := Set.mem_singleton_iff.mp hzero
    rw [hx0] at hclose
    exfalso
    simp [U, abs_of_pos (by positivity : 0 < 2 * r)] at hclose
  · obtain ⟨j, _, rfl⟩ := hU
    by_cases hj : j = k
    · simp [hj]
    · have hfar := coordinate_dist_lower (2 * r) (2 * r) (by omega : 4 * k ≠ 4 * j)
      rw [abs_of_pos (by positivity : 0 < 2 * r)] at hfar
      exact (not_lt_of_ge hfar hclose).elim
  · obtain ⟨j, _, n, rfl⟩ := hG
    have hfar := coordinate_dist_lower (2 * r) ε'
      (by omega : 4 * k ≠ 4 * j ^ (n + 1) + 3)
    rw [abs_of_pos (by positivity : 0 < 2 * r)] at hfar
    exact (not_lt_of_ge hfar hclose).elim
  · obtain ⟨j, _, rfl⟩ := hA
    have hfar := coordinate_dist_lower (2 * r) ε₁ (by omega : 4 * k ≠ 4 * j + 1)
    rw [abs_of_pos (by positivity : 0 < 2 * r)] at hfar
    exact (not_lt_of_ge hfar hclose).elim
  · obtain ⟨j, _, rfl⟩ := hB
    have hfar := coordinate_dist_lower (2 * r) ε₂ (by omega : 4 * k ≠ 4 * j + 2)
    rw [abs_of_pos (by positivity : 0 < 2 * r)] at hfar
    exact (not_lt_of_ge hfar hclose).elim

theorem family_uus {r ε₁ ε₂ ε' : ℝ} (hr : 0 < r) :
    UniformlyUnboundedSupportAt dist r (family r ε₁ ε₂ ε') := by
  apply uus_of_infinite_isolated_orthogonal hr.le
    (by linarith : r < 2 * r) (by linarith : r < 2 * r)
  rintro L ⟨I₁, I₂, J, hI₁, _, _, _, _, _, rfl⟩
  let C : Set Hilbert2 := (U r) '' I₁
  have hC : C.Infinite := hI₁.image (by
    intro i _ j _ hij
    have hc := (axisPoint_eq_axisPoint_of_left_ne_zero
      (by positivity : (2 * r : ℝ) ≠ 0) hij).2
    omega)
  refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨k, hk, rfl⟩
    exact Or.inr (Or.inl (Or.inl ⟨k, hk, rfl⟩))
  · rintro x ⟨k, hk, rfl⟩
    simp [U, abs_of_pos (by positivity : 0 < 2 * r)]
  · rintro x ⟨k, hk, rfl⟩ y ⟨j, hj, rfl⟩ hne
    exact inner_axisPoint_of_ne _ _ (fun hc => hne (congrArg (axisPoint (2 * r)) hc))
  · rintro x ⟨k, hk, rfl⟩ y hy hclose
    exact u_isolated hr hy hclose

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.Example49
