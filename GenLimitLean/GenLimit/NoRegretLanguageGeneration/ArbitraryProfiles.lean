import GenLimit.NoRegretLanguageGeneration.ArbitraryProfilesReserve
import GenLimit.NoRegretLanguageGeneration.AsymptoticBridge

namespace PredictionToGeneration.ArbitraryProfiles
open Classical
open Blocks

def size (n : Nat) : Nat := 4 ^ (n + 1)
def capacity (f : Nat → Nat) (n : Nat) : Nat := f (size n)
noncomputable def H (f : Nat → Nat) := Blocks.Class size (capacity f)

theorem size_positive (n : Nat) : 0 < size n := Nat.pow_pos (by decide)

theorem size_mono {i j : Nat} (hij : i ≤ j) : size i ≤ size j := by
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem size_unbounded (t : Nat) : ∃ n, t ≤ size n := by
  refine ⟨t, ?_⟩
  have ht : t + 1 < 4 ^ (t + 1) := Nat.lt_pow_self (by decide)
  dsimp [size]
  omega

noncomputable def coveringBlock (t : Nat) : Nat := Nat.find (size_unbounded t)

theorem coveringBlock_spec (t : Nat) : t ≤ size (coveringBlock t) := Nat.find_spec (size_unbounded t)

theorem below_coveringBlock (t n : Nat) (hn : n < coveringBlock t) : size n < t := by
  have hh := Nat.find_min (size_unbounded t) hn
  omega

noncomputable def prefixPoints (n : Nat) : Finset (Space size) :=
  (Finset.range n).biUnion (points size)

theorem mem_prefixPoints (n : Nat) (x : Space size) :
    x ∈ prefixPoints n ↔ block x < n := by
  simp [prefixPoints]

theorem prefixPoints_card (n : Nat) : (prefixPoints n).card ≤ 2 * 4 ^ n := by
  induction n with
  | zero => simp [prefixPoints]
  | succ n ih =>
    have he : prefixPoints (n + 1) = prefixPoints n ∪ points size n := by
      ext x
      simp only [mem_prefixPoints, Finset.mem_union, mem_points]
      omega
    rw [he]
    have hu := Finset.card_union_le (prefixPoints n) (points size n)
    rw [card_points] at hu
    dsimp [size] at hu
    rw [Nat.pow_succ] at hu ⊢
    omega

theorem small_prefix_card (t : Nat) : (prefixPoints (coveringBlock t)).card ≤ 2 * t := by
  by_cases hz : coveringBlock t = 0
  · simp [hz, prefixPoints]
  · have hh := below_coveringBlock t (coveringBlock t - 1) (by omega)
    have he : coveringBlock t - 1 + 1 = coveringBlock t := by omega
    dsimp [size] at hh
    rw [he] at hh
    have hc := prefixPoints_card (coveringBlock t)
    omega

theorem upper (f : Nat → Nat) (hmono : Monotone f) (T : Nat) (hT : 4 ≤ T) :
    MF (H f) T ≤ f (8 * T) := by
  let n := coveringBlock (2 * T)
  have hs : 2 * T ≤ size n := coveringBlock_spec _
  have hn : n ≠ 0 := by
    intro he
    simp [he, size] at hs
    omega
  have hp := below_coveringBlock (2 * T) (n - 1) (by dsimp [n]; omega)
  have he : n - 1 + 1 = n := by omega
  dsimp [size] at hp
  rw [he] at hp
  have hsize : size n ≤ 8 * T := by
    simp only [size, Nat.pow_succ]
    omega
  exact Nat.le_trans (Blocks.mf_upper size (capacity f) size_positive n T hs) (hmono hsize)

theorem lower (f : Nat → Nat) (hmono : Monotone f)
    (hbound : ∀ t, 1 ≤ t → f t ≤ t) (T : Nat) (hT : 4 ≤ T) :
    f (T / 4) ≤ MF (H f) T := by
  let u := T / 4
  let small := prefixPoints (coveringBlock u)
  apply Blocks.mf_lower size (capacity f) size_positive (f u) T small
  · intro z hz
    apply (mem_prefixPoints _ z).mpr
    by_contra hn
    have hc := coveringBlock_spec u
    have hs := size_mono (show coveringBlock u ≤ block z by omega)
    have hf := hmono (show u ≤ size (block z) by omega)
    dsimp [capacity] at hz
    omega
  · have hc := small_prefix_card u
    have hf := hbound u (by dsimp [u]; omega)
    change f u + (prefixPoints (coveringBlock u)).card ≤ T
    dsimp [u] at hc hf ⊢
    omega

/-- The explicit countable cofinite block class realizes every admissible
profile between the manuscript's fixed rescalings. -/
theorem arbitrary_profile (f : Nat → Nat) (hmono : Monotone f)
    (hbound : ∀ t, 1 ≤ t → 1 ≤ f t ∧ f t ≤ t) :
    Countable {h // H f h} ∧ UUS (H f) ∧
      ∀ T, 4 ≤ T → f (T / 4) ≤ MF (H f) T ∧ MF (H f) T ≤ f (8 * T) := by
  refine ⟨Blocks.countable_class size (capacity f), Blocks.uus size (capacity f) size_positive, ?_⟩
  intro T hT
  exact ⟨lower f hmono (fun t ht => (hbound t ht).2) T hT, upper f hmono T hT⟩

end PredictionToGeneration.ArbitraryProfiles

namespace PredictionToGeneration.ArbitraryProfiles

/-- Sublinearity of an admissible profile yields an actual no-regret generator
for the explicitly constructed class. -/
theorem no_regret (f : Nat → Nat) (hmono : Monotone f) (hf : NatSublinear f) :
    RealizableNoRegret (H f) := by
  apply (realizable_no_regret_iff_sublinear (H f) (Blocks.uus size (capacity f) size_positive)
    (Blocks.nonempty_class size (capacity f))).mpr
  intro k
  obtain ⟨N, hN⟩ := hf (8 * k)
  refine ⟨max 4 N, ?_⟩
  intro t ht
  have hu := upper f hmono t (by omega)
  have hc := Nat.mul_le_mul_left k hu
  have hs := hN (8 * t) (by omega)
  rw [Nat.mul_assoc] at hs
  omega

/-- Stability at factor eight suffices for the manuscript's Theta conclusion;
stability under every constant rescaling implies this special case. -/
theorem theta_of_rescaling (f : Nat → Nat) (hmono : Monotone f)
    (hbound : ∀ t, 1 ≤ t → f t ≤ t)
    (hstable : ∃ C N : Nat, ∀ t, N ≤ t → f (8 * t) ≤ C * f t) :
    (fun t : Nat => (MF (H f) t : ℝ)) =Θ[Filter.atTop] (fun t : Nat => (f t : ℝ)) := by
  obtain ⟨C, N, hC⟩ := hstable
  constructor
  · apply Asymptotics.IsBigO.of_bound (C : ℝ)
    apply Filter.eventually_atTop.mpr
    refine ⟨max 4 N, ?_⟩
    intro t ht
    have hu := upper f hmono t (by omega)
    have hc := hC t (by omega)
    simp only [Real.norm_natCast]
    exact_mod_cast Nat.le_trans hu hc
  · apply Asymptotics.IsBigO.of_bound (C : ℝ)
    apply Filter.eventually_atTop.mpr
    refine ⟨max 4 (4 * N), ?_⟩
    intro t ht
    have hlo := lower f hmono hbound t (by omega)
    have hmono' := hmono (show t ≤ 8 * (t / 4) by omega)
    have hc := hC (t / 4) (by omega)
    have hm := Nat.mul_le_mul_left C hlo
    simp only [Real.norm_natCast]
    exact_mod_cast Nat.le_trans hmono' (Nat.le_trans hc hm)

end PredictionToGeneration.ArbitraryProfiles
