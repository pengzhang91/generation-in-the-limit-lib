import GenLimit.Paper21_GenerationInMetricSpaces.WeightedHilbert
import GenLimit.Paper21_GenerationInMetricSpaces.ReservoirGeneration

/-!
# Example 4.11: dyadic layers and doubling orbits

Layer zero represents the source's first layer and has amplitude `4r`.
Each layer contains the full doubling orbits of an infinite set of positive
odd-part indices. The same class is UUS for both Hilbert metrics.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example411

open GenLimit.Generic WeightedHilbert

noncomputable section

def amplitude (r : ℝ) (m : ℕ) : ℝ := 4 * r * (1 / 2 : ℝ) ^ m

@[simp] theorem amplitude_zero (r : ℝ) : amplitude r 0 = 4 * r := by simp [amplitude]

theorem amplitude_pos {r : ℝ} (hr : 0 < r) (m : ℕ) : 0 < amplitude r m := by
  unfold amplitude
  positivity

theorem amplitude_succ (r : ℝ) (m : ℕ) : amplitude r (m + 1) = amplitude r m / 2 := by
  simp only [amplitude, pow_succ]
  ring

theorem amplitude_strictAnti {r : ℝ} (hr : 0 < r) : StrictAnti (amplitude r) := by
  intro m n hmn
  exact mul_lt_mul_of_pos_left
    (pow_right_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hmn)
    (by positivity)

theorem amplitude_injective {r : ℝ} (hr : 0 < r) : Function.Injective (amplitude r) :=
  (amplitude_strictAnti hr).injective

def orbit (k n : ℕ) : ℕ := 2 ^ n * (2 * k + 1)

theorem orbit_pos (k n : ℕ) : 0 < orbit k n := by unfold orbit; positivity

theorem orbit_injective (k : ℕ) : Function.Injective (orbit k) := by
  intro m n hmn
  have hpow : (2 : ℕ) ^ m = 2 ^ n := by
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * k + 1) hmn
  exact Nat.pow_right_injective (by decide) hpow

theorem orbit_root {k l n m : ℕ} (h : orbit k n = orbit l m) : k = l := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa [orbit] using h
    | succ m =>
      have hm := congrArg (fun q : ℕ => q % 2) h
      simp [orbit, pow_succ, Nat.mul_mod] at hm
  | succ n ih =>
    cases m with
    | zero =>
      have hm := congrArg (fun q : ℕ => q % 2) h
      simp [orbit, pow_succ, Nat.mul_mod] at hm
    | succ m =>
      apply ih (m := m)
      change 2 ^ n * (2 * k + 1) = 2 ^ m * (2 * l + 1)
      simp only [orbit, pow_succ] at h
      nlinarith

def layer (r : ℝ) (m : ℕ) (I : Set ℕ) : Set Hilbert2 :=
  {x | ∃ k ∈ I, ∃ n, x = axisPoint (amplitude r m) (orbit k n)}

def target (r : ℝ) (I : ℕ → Set ℕ) : Set Hilbert2 :=
  {0} ∪ {x | ∃ m, x ∈ layer r m (I m)}

def family (r : ℝ) : LanguageClass Hilbert2 :=
  {L | ∃ I : ℕ → Set ℕ, (∀ m, (I m).Infinite ∧ ∀ k ∈ I m, 0 < k) ∧ L = target r I}

theorem target_axisSupported (r : ℝ) (I : ℕ → Set ℕ) : AxisSupported (target r I) := by
  rintro x (hx | ⟨m, k, hk, n, rfl⟩)
  · exact ⟨0, 0, by simpa using hx⟩
  · exact ⟨amplitude r m, orbit k n, rfl⟩

theorem no_cover_of_fixed_orthogonal {A L : Set Hilbert2} {R γ : ℝ}
    (f : Hilbert2 → Hilbert2) (hfix : ∀ x ∈ A, f x = x)
    (hA : A.Infinite) (hAL : A ⊆ L) (hR : 0 < R) (hγ : 0 ≤ γ) (hγR : γ < R)
    (hnorm : ∀ x ∈ A, ‖x‖ = R)
    (horth : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → inner ℝ x y = 0) :
    ¬ HasFiniteCover (fun x y => dist (f x) (f y)) γ L := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨S, hSA, hSlarge⟩ := infinite_orthogonal_has_large_finite_sample
    hA hR hγ hγR hnorm horth ((C.image f).card + 1)
  have hcover : (S : Set Hilbert2) ⊆ closedNeighborhood dist (C.image f : Set Hilbert2) γ := by
    intro x hx η hη
    obtain ⟨y, hy, hclose⟩ := hC (hAL (hSA hx)) η hη
    exact ⟨f y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, by simpa only [hfix x (hSA hx)] using hclose⟩
  have hbad := hSlarge (C.image f) hcover
  omega

theorem first_layer_witness {r : ℝ} (hr : 0 < r) {L : Set Hilbert2} (hL : L ∈ family r) :
    ∃ A : Set Hilbert2, A.Infinite ∧ A ⊆ L ∧
      (∀ x ∈ A, ‖x‖ = 4 * r) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → inner ℝ x y = 0) ∧
      (∀ x ∈ A, weightedMap x = x) := by
  obtain ⟨I, hI, rfl⟩ := hL
  let A : Set Hilbert2 := (fun k => axisPoint (4 * r) (2 * k + 1)) '' I 0
  have hA : A.Infinite := (hI 0).1.image (by
    intro i _ j _ hij
    have hc := (axisPoint_eq_axisPoint_of_left_ne_zero (by positivity : (4 * r : ℝ) ≠ 0) hij).2
    omega)
  refine ⟨A, hA, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨k, hk, rfl⟩
    exact Or.inr ⟨0, k, hk, 0, by simp [orbit]⟩
  · rintro x ⟨k, hk, rfl⟩
    simp [abs_of_pos (by positivity : 0 < 4 * r)]
  · rintro x ⟨k, hk, rfl⟩ y ⟨j, hj, rfl⟩ hne
    exact inner_axisPoint_of_ne _ _ (fun hc => hne (congrArg (axisPoint (4 * r)) hc))
  · rintro x ⟨k, hk, rfl⟩
    simp [weight, show (2 * k + 1) % 2 = 1 by omega]

theorem family_uus {r : ℝ} (hr : 0 < r) : UniformlyUnboundedSupportAt dist r (family r) := by
  apply uus_of_no_finite_cover_triple dist_self dist_comm dist_triangle hr.le
  intro L hL
  obtain ⟨A, hA, hAL, hnorm, horth, hfix⟩ := first_layer_witness hr hL
  exact no_cover_of_fixed_orthogonal id (fun _ _ => rfl) hA hAL
    (by positivity) (by positivity) (by linarith) hnorm horth

theorem family_weighted_uus {r : ℝ} (hr : 0 < r) :
    UniformlyUnboundedSupportAt weightedDistance r (family r) := by
  apply uus_of_no_finite_cover_triple (fun x => dist_self (weightedMap x))
    (fun x y => dist_comm (weightedMap x) (weightedMap y))
    (fun x y z => dist_triangle (weightedMap x) (weightedMap y) (weightedMap z)) hr.le
  intro L hL
  obtain ⟨A, hA, hAL, hnorm, horth, hfix⟩ := first_layer_witness hr hL
  exact no_cover_of_fixed_orthogonal weightedMap hfix hA hAL
    (by positivity) (by positivity) (by linarith) hnorm horth

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.Example411
