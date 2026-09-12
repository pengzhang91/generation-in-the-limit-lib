import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.NormNum

/-!
# Example 4.5: the tractable real-line threshold direction

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1, Example 4.5 and
Appendix C.2.

For every positive odd prime `p`, the source uses

`Aₚ = {pⁿ : n ≥ 1} ∪ {pⁿ - 1 : n ≥ 1}`

and allows an arbitrary subset of the positive even integers to be added to
`Aₚ`.  This file proves the source's positive direction: the resulting class
is `1`-UUS and is `(ε, 1)`-generatable in the limit whenever `0 < ε < 1`.

The generator is deliberately noncomputable, as are the paper-facing
generators elsewhere in this development.  Once an odd integer marker has
appeared, it chooses a sufficiently remote positive power of that marker.
Because every target point is an integer, an adversarial cover at radius
strictly below one must actually enumerate the target.

The negative `(1,1)` direction is not claimed here.  The source proves it
through the infinite-row diagonal Lemma C.3; formalizing that lemma is a
separate, substantially larger construction.
-/

namespace GenLimit.MetricSpaces
namespace RealLineThreshold

open scoped BigOperators

/-- The ordinary distance on the real line. -/
def realDistance (x y : ℝ) : ℝ :=
  |x - y|

/-- The source's set `Aₚ`, with its positive exponent convention explicit. -/
def primePairSupport (p : ℕ) : Set ℝ :=
  {x | ∃ n : ℕ,
    x = ((p ^ (n + 1) : ℕ) : ℝ) ∨
      x = (((p ^ (n + 1) - 1 : ℕ) : ℕ) : ℝ)}

/-- The positive even integers, embedded in the real line. -/
def positiveEvenIntegers : Set ℝ :=
  {x | ∃ n : ℕ, x = ((2 * (n + 1) : ℕ) : ℝ)}

/-- The explicit hypothesis class from Example 4.5. -/
def languageClass : GenLimit.Generic.LanguageClass ℝ :=
  {L | ∃ p : ℕ, p.Prime ∧ Odd p ∧
    ∃ B : Set ℝ, B ⊆ positiveEvenIntegers ∧
      L = primePairSupport p ∪ B}

theorem power_mem_primePairSupport (p n : ℕ) :
    ((p ^ (n + 1) : ℕ) : ℝ) ∈ primePairSupport p :=
  ⟨n, Or.inl rfl⟩

theorem primePairSupport_consists_of_natCasts
    {p : ℕ} {x : ℝ} (hx : x ∈ primePairSupport p) :
    ∃ m : ℕ, x = (m : ℝ) := by
  obtain ⟨n, hn | hn⟩ := hx
  · exact ⟨p ^ (n + 1), hn⟩
  · exact ⟨p ^ (n + 1) - 1, hn⟩

theorem positiveEvenIntegers_consists_of_natCasts
    {x : ℝ} (hx : x ∈ positiveEvenIntegers) :
    ∃ m : ℕ, x = (m : ℝ) := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨2 * (n + 1), rfl⟩

theorem language_consists_of_natCasts
    {p : ℕ} {B L : Set ℝ}
    (hB : B ⊆ positiveEvenIntegers)
    (hL : L = primePairSupport p ∪ B)
    {x : ℝ} (hx : x ∈ L) :
    ∃ m : ℕ, x = (m : ℝ) := by
  rw [hL] at hx
  rcases hx with hx | hx
  · exact primePairSupport_consists_of_natCasts hx
  · exact positiveEvenIntegers_consists_of_natCasts (hB hx)

/-- Distinct natural numbers embedded in `ℝ` are at least one apart. -/
theorem natCast_eq_of_abs_sub_lt_one
    {m n : ℕ} (h : |(m : ℝ) - (n : ℝ)| < 1) :
    m = n := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hmn | hnm
  · have hstep : (m : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hmn)
    have habs : 1 ≤ |(m : ℝ) - (n : ℝ)| := by
      rw [abs_of_nonpos]
      · linarith
      · linarith
    linarith
  · have hstep : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnm)
    have habs : 1 ≤ |(m : ℝ) - (n : ℝ)| := by
      rw [abs_of_nonneg]
      · linarith
      · linarith
    linarith

/-- On an integer-supported target, every metric presentation below radius
one is an exact presentation. -/
theorem metricPresentation_is_exact_of_natCasts
    {ε : ℝ} (hε : ε < 1)
    {stream : GenLimit.Generic.Stream ℝ}
    {L : GenLimit.Generic.Language ℝ}
    (hnat : ∀ x ∈ L, ∃ m : ℕ, x = (m : ℝ))
    (hpres : MetricPresentation realDistance ε stream L) :
    GenLimit.Generic.Presents stream L := by
  apply Set.Subset.antisymm hpres.1
  intro y hyL
  obtain ⟨m, rfl⟩ := hnat y hyL
  have hεmid : ε < (ε + 1) / 2 := by linarith
  have hmid1 : (ε + 1) / 2 < 1 := by linarith
  obtain ⟨z, ⟨i, rfl⟩, hdist⟩ :=
    hpres.2 hyL ((ε + 1) / 2) hεmid
  have hstreamL : stream i ∈ L :=
    hpres.1 ⟨i, rfl⟩
  obtain ⟨n, hn⟩ := hnat (stream i) hstreamL
  have hclose : |(n : ℝ) - (m : ℝ)| < 1 := by
    rw [← hn]
    exact lt_trans hdist hmid1
  have hnm : n = m := natCast_eq_of_abs_sub_lt_one hclose
  exact ⟨i, by rw [hn, hnm]⟩

/-- An odd natural number larger than one, viewed as a real history marker. -/
def IsOddIntegerMarker (x : ℝ) : Prop :=
  ∃ m : ℕ, Odd m ∧ 1 < m ∧ x = (m : ℝ)

/-- Choose an odd marker already present in a finite history, or use `3`
before such a marker appears. -/
noncomputable def historyMarker
    {t : ℕ} (xs : Fin t → ℝ) : ℝ := by
  classical
  exact
    if h : ∃ i : Fin t, IsOddIntegerMarker (xs i) then
      xs (Classical.choose h)
    else
      3

theorem historyMarker_spec
    {t : ℕ} (xs : Fin t → ℝ) :
    IsOddIntegerMarker (historyMarker xs) := by
  classical
  by_cases h : ∃ i : Fin t, IsOddIntegerMarker (xs i)
  · rw [historyMarker, dif_pos h]
    exact Classical.choose_spec h
  · rw [historyMarker, dif_neg h]
    exact ⟨3, ⟨1, by norm_num⟩, by norm_num, by norm_num⟩

theorem one_lt_historyMarker
    {t : ℕ} (xs : Fin t → ℝ) :
    1 < historyMarker xs := by
  obtain ⟨m, -, hm, hcast⟩ := historyMarker_spec xs
  rw [hcast]
  exact_mod_cast hm

theorem historyMarker_mem_history
    {t : ℕ} {xs : Fin t → ℝ}
    (h : ∃ i : Fin t, IsOddIntegerMarker (xs i)) :
    ∃ i : Fin t, historyMarker xs = xs i := by
  classical
  rw [historyMarker, dif_pos h]
  exact ⟨Classical.choose h, rfl⟩

private theorem abs_entry_le_sum
    {t : ℕ} (xs : Fin t → ℝ) (i : Fin t) :
    |xs i| ≤ ∑ j : Fin t, |xs j| := by
  classical
  exact Finset.single_le_sum
    (fun j _ ↦ abs_nonneg (xs j))
    (Finset.mem_univ i)

/-- Positive powers of a real number greater than one eventually lie more
than distance two from every entry of a finite history. -/
theorem exists_far_power
    (x : ℝ) (hx : 1 < x)
    {t : ℕ} (xs : Fin t → ℝ) :
    ∃ n : ℕ,
      3 < x ^ n ∧
      ∀ i : Fin t, 2 < |xs i - x ^ n| := by
  let S : ℝ := ∑ i : Fin t, |xs i|
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _ ↦ abs_nonneg (xs i))
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (S + 3) hx
  refine ⟨n, by linarith, ?_⟩
  intro i
  have hi : |xs i| ≤ S := by
    simpa [S] using abs_entry_le_sum xs i
  have hxle : xs i ≤ |xs i| := le_abs_self (xs i)
  have hdiff : 2 < x ^ n - xs i := by
    linarith
  have habs : x ^ n - xs i ≤ |xs i - x ^ n| := by
    rw [abs_sub_comm]
    exact le_abs_self (x ^ n - xs i)
  linarith

noncomputable def farExponent
    (x : ℝ) (hx : 1 < x)
    {t : ℕ} (xs : Fin t → ℝ) : ℕ :=
  Classical.choose (exists_far_power x hx xs)

noncomputable def farPower
    (x : ℝ) (hx : 1 < x)
    {t : ℕ} (xs : Fin t → ℝ) : ℝ :=
  x ^ farExponent x hx xs

theorem farPower_large
    (x : ℝ) (hx : 1 < x)
    {t : ℕ} (xs : Fin t → ℝ) :
    3 < farPower x hx xs :=
  (Classical.choose_spec (exists_far_power x hx xs)).1

theorem farPower_far
    (x : ℝ) (hx : 1 < x)
    {t : ℕ} (xs : Fin t → ℝ) (i : Fin t) :
    2 < |xs i - farPower x hx xs| :=
  (Classical.choose_spec (exists_far_power x hx xs)).2 i

theorem farExponent_pos
    (x : ℝ) (hx : 1 < x)
    {t : ℕ} (xs : Fin t → ℝ) :
    0 < farExponent x hx xs := by
  by_contra h
  have hz : farExponent x hx xs = 0 := Nat.eq_zero_of_not_pos h
  have hlarge := farPower_large x hx xs
  simp [farPower, hz] at hlarge

/-- The finite-history generator for the positive half of Example 4.5. -/
noncomputable def generator : GenLimit.Generic.Generator ℝ :=
  fun _ xs ↦
    farPower (historyMarker xs) (one_lt_historyMarker xs) xs

theorem generator_is_novel
    (stream : GenLimit.Generic.Stream ℝ) (t : ℕ) :
    GenLimit.Generic.output generator stream t ∉
      closedNeighborhood realDistance
        (GenLimit.Generic.sample stream t : Set ℝ) 1 := by
  intro hclose
  obtain ⟨z, hz, hdist⟩ := hclose 2 (by norm_num)
  obtain ⟨i, hi, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hz
  let j : Fin t := ⟨i, hi⟩
  have hfar :=
    farPower_far
      (historyMarker (fun k : Fin t ↦ stream k))
      (one_lt_historyMarker (fun k : Fin t ↦ stream k))
      (fun k : Fin t ↦ stream k) j
  have hdist' :
      |stream i - GenLimit.Generic.output generator stream t| < 2 := by
    simpa [realDistance] using hdist
  have hfar' :
      2 < |stream i - GenLimit.Generic.output generator stream t| := by
    simpa [generator, GenLimit.Generic.output, j] using hfar
  linarith

theorem oddMarker_mem_target_is_primePower
    {p : ℕ} (hpodd : Odd p)
    {B : Set ℝ} (hB : B ⊆ positiveEvenIntegers)
    {x : ℝ}
    (hx : x ∈ primePairSupport p ∪ B)
    (hmarker : IsOddIntegerMarker x) :
    ∃ n : ℕ, x = ((p ^ (n + 1) : ℕ) : ℝ) := by
  obtain ⟨m, hmodd, -, hxm⟩ := hmarker
  rcases hx with hx | hx
  · obtain ⟨n, hn | hn⟩ := hx
    · exact ⟨n, hn⟩
    · exfalso
      have hcast :
          (m : ℝ) = ((p ^ (n + 1) - 1 : ℕ) : ℝ) :=
        hxm.symm.trans hn
      have hm :
          m = p ^ (n + 1) - 1 := by
        exact_mod_cast hcast
      have hpPowOdd : Odd (p ^ (n + 1)) := hpodd.pow
      have heven : Even (p ^ (n + 1) - 1) :=
        hpPowOdd.tsub_odd odd_one
      have hmeven : Even m := by simpa [hm] using heven
      exact (Nat.not_even_iff_odd.mpr hmodd) hmeven
  · exfalso
    obtain ⟨n, hn⟩ := hB hx
    have hcast :
        (m : ℝ) = ((2 * (n + 1) : ℕ) : ℝ) :=
      hxm.symm.trans hn
    have hm : m = 2 * (n + 1) := by
      exact_mod_cast hcast
    have hmeven : Even m := by
      rw [hm]
      exact even_two_mul (n + 1)
    exact (Nat.not_even_iff_odd.mpr hmodd) hmeven

theorem positive_power_of_target_marker_mem
    {p : ℕ} (hpodd : Odd p)
    {B : Set ℝ} (hB : B ⊆ positiveEvenIntegers)
    {x : ℝ}
    (hx : x ∈ primePairSupport p ∪ B)
    (hmarker : IsOddIntegerMarker x)
    {N : ℕ} (hN : 0 < N) :
    x ^ N ∈ primePairSupport p ∪ B := by
  obtain ⟨k, hxpow⟩ :=
    oddMarker_mem_target_is_primePower hpodd hB hx hmarker
  left
  cases N with
  | zero => simp at hN
  | succ N =>
      refine ⟨(k + 1) * (N + 1) - 1, Or.inl ?_⟩
      have hpos : 0 < (k + 1) * (N + 1) := Nat.mul_pos (by omega) (by omega)
      have hsucc :
          ((k + 1) * (N + 1) - 1) + 1 =
            (k + 1) * (N + 1) := by omega
      rw [hxpow, hsucc]
      have hnat :
          (p ^ (k + 1)) ^ (N + 1) =
            p ^ ((k + 1) * (N + 1)) := by
        rw [pow_mul]
      exact_mod_cast hnat

private theorem exists_far_power_finset
    (x : ℝ) (hx : 1 < x) (centers : Finset ℝ) :
    ∃ n : ℕ,
      3 < x ^ n ∧
      ∀ c ∈ centers, 2 < |c - x ^ n| := by
  let S : ℝ := ∑ c ∈ centers, |c|
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun c _ ↦ abs_nonneg c)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (S + 3) hx
  refine ⟨n, by linarith, ?_⟩
  intro c hc
  have hcS : |c| ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun y hy ↦ abs_nonneg y)
      hc
  have hcle : c ≤ |c| := le_abs_self c
  have hdiff : 2 < x ^ n - c := by
    linarith
  have habs : x ^ n - c ≤ |c - x ^ n| := by
    rw [abs_sub_comm]
    exact le_abs_self (x ^ n - c)
  linarith

/-- Example 4.5's explicit class has uniformly unbounded support at radius
one. -/
theorem example_4_5_uus :
    UniformlyUnboundedSupportAt realDistance 1 languageClass := by
  intro L hL hfinite
  obtain ⟨p, hp, hpodd, B, hB, rfl⟩ := hL
  obtain ⟨centers, hcover⟩ := hfinite
  have hpgt : 1 < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp.two_le)
  obtain ⟨n, hnlarge, hnfar⟩ :=
    exists_far_power_finset (p : ℝ) hpgt centers
  cases n with
  | zero => norm_num at hnlarge
  | succ n =>
      have hy :
          ((p : ℝ) ^ (n + 1)) ∈ primePairSupport p ∪ B := by
        left
        simpa using power_mem_primePairSupport p n
      have hycover := hcover hy
      obtain ⟨c, hc, hdist⟩ := hycover 2 (by norm_num)
      have hfar := hnfar c hc
      simp only [realDistance] at hdist
      linarith

/-- The positive, tractable half of source Example 4.5: below adversary
radius one, the explicit real-line class is generatable with novelty radius
one. -/
theorem example_4_5_positive
    {ε : ℝ} (_hεpos : 0 < ε) (hεlt : ε < 1) :
    GeneratableInLimitAt realDistance ε 1 languageClass := by
  refine ⟨generator, ?_⟩
  intro L hL stream hpres
  obtain ⟨p, hp, hpodd, B, hB, hL⟩ := hL
  have hexact :
      GenLimit.Generic.Presents stream L :=
    metricPresentation_is_exact_of_natCasts hεlt
      (fun x hx ↦ language_consists_of_natCasts hB hL hx)
      hpres
  have hpL : (p : ℝ) ∈ L := by
    rw [hL]
    left
    simpa using power_mem_primePairSupport p 0
  obtain ⟨s, hs⟩ : (p : ℝ) ∈ Set.range stream := by
    rw [hexact]
    exact hpL
  refine ⟨s + 1, ?_⟩
  intro t ht
  have hst : s < t := lt_of_lt_of_le (Nat.lt_succ_self s) ht
  let xs : Fin t → ℝ := fun i ↦ stream i
  have hpgt : 1 < p :=
    lt_of_lt_of_le Nat.one_lt_two hp.two_le
  have hpmarker : IsOddIntegerMarker (stream s) := by
    refine ⟨p, hpodd, hpgt, ?_⟩
    exact hs
  have hhas : ∃ i : Fin t, IsOddIntegerMarker (xs i) :=
    ⟨⟨s, hst⟩, hpmarker⟩
  have hselectedMarker : IsOddIntegerMarker (historyMarker xs) :=
    historyMarker_spec xs
  obtain ⟨i, hi⟩ := historyMarker_mem_history hhas
  have hiL : xs i ∈ L := by
    exact hpres.1 ⟨i, rfl⟩
  have hmarkerL : historyMarker xs ∈ L := by
    rw [hi]
    exact hiL
  constructor
  · rw [hL] at hmarkerL ⊢
    simpa [generator, GenLimit.Generic.output, xs] using
      positive_power_of_target_marker_mem hpodd hB hmarkerL
        hselectedMarker
        (farExponent_pos (historyMarker xs)
          (one_lt_historyMarker xs) xs)
  · exact generator_is_novel stream t

/-- Source-facing package for the completed half of Example 4.5. -/
theorem example_4_5_positive_package
    {ε : ℝ} (hεpos : 0 < ε) (hεlt : ε < 1) :
    UniformlyUnboundedSupportAt realDistance 1 languageClass ∧
      GeneratableInLimitAt realDistance ε 1 languageClass :=
  ⟨example_4_5_uus, example_4_5_positive hεpos hεlt⟩

end RealLineThreshold
end GenLimit.MetricSpaces
