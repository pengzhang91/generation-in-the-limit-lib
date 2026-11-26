import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Which eligibility thresholds can the scale accounting in Appendix A
of Kleinberg and Wei, arXiv:2611.14887v1, support? Here h is the logarithm
of the spatial side length. The local cutoff costs at least a h, as in (44).
We test (G1) and (G2) independently of the choice of game potential. -/
namespace GenLimit.KleinbergWei.Banach.ScaleThresholds
open Finset Real
noncomputable section

/-- The local retention cutoff α pays a linear cost in the current logarithmic
side length. Eligibility γ is capped at the preceding scale times L. The sum
of discarded fractions is bounded at every finite depth, including level zero. -/
def AdmitsBudget (L : ℕ → ℝ) (budget : ℝ) : Prop :=
  ∃ (h : ℕ → ℕ) (α γ : ℕ → ℝ) (a c : ℝ), StrictMono h ∧ (∀ j, 0 < h j) ∧
    0 < a ∧ 0 < c ∧ (∀ j, a * h j ≤ α j) ∧ (∀ j, 0 < γ j) ∧ γ 0 ≤ c ∧
    (∀ j, γ (j+1) ≤ c * (h j * L (h j))) ∧
    ∀ n, ∑ j ∈ range n, α j / γ j ≤ budget

private def term (L : ℕ → ℝ) (n : ℕ) := 1 / (n * L n)

private theorem term_nonneg {L : ℕ → ℝ} (pos : ∀ n, 0 < L n) (n : ℕ) : 0 ≤ term L n :=
  div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg n) (pos n).le)

private theorem term_antitone {L : ℕ → ℝ} (mono : Monotone L) (pos : ∀ n, 0 < L n)
    {m n : ℕ} (hm : 0 < m) (le : m ≤ n) : term L n ≤ term L m := by
  have hp : 0 < (m:ℝ) * L m := mul_pos (Nat.cast_pos.mpr hm) (pos m)
  exact one_div_le_one_div_of_le hp
    (mul_le_mul (Nat.cast_le.mpr le) (mono le) (pos m).le (Nat.cast_nonneg n))

private theorem condensed {L : ℕ → ℝ} (mono : Monotone L) (pos : ∀ n, 0 < L n) :
    (Summable fun k : ℕ => 1 / L (2^k)) ↔ Summable (term L) := by
  convert summable_condensed_iff_of_nonneg (term_nonneg pos)
    (fun _ _ hm le => term_antitone mono pos hm le) using 2
  funext k
  simp [term,one_div,mul_inv_rev,mul_comm,← mul_assoc]

/-- The cutoff restrictions are imposed only through the last level n. -/
structure FiniteBudget (L : ℕ → ℝ) (a c budget : ℝ) (h : ℕ → ℕ) (α γ : ℕ → ℝ)
    (n : ℕ) : Prop where
  lower : ∀ i ≤ n, a * h i ≤ α i
  positive : ∀ i ≤ n, 0 < γ i
  initial : γ 0 ≤ c
  upper : ∀ i < n, γ (i+1) ≤ c * (h i * L (h i))
  total : ∑ i ∈ range (n+1), α i/γ i ≤ budget

private theorem partial_bound {L : ℕ → ℝ} (mono : Monotone L) (pos : ∀ n, 0 < L n)
    {h α γ n a c budget} (inc : Monotone h) (hpos : ∀ j, 0 < h j)
    (ap : 0 < a) (cp : 0 < c) (H : FiniteBudget L a c budget h α γ n) :
    (∑ k ∈ range (h n), term L k) ≤ (∑ k ∈ range (h 0), term L k) + (c/a)*budget := by
  have an (i) (hi : i ≤ n) : 0 ≤ α i := (mul_nonneg ap.le (Nat.cast_nonneg _)).trans (H.lower i hi)
  have step (i) (hi : i < n) : (h (i+1) - h i) • term L (h i) ≤ (c/a) * (α (i+1) / γ (i+1)) := by
    let v : ℝ := h i * L (h i)
    have vp : 0 < v := mul_pos (Nat.cast_pos.mpr (hpos i)) (pos _)
    have compare := div_le_div₀ (an (i+1) hi) (H.lower (i+1) hi) (H.positive (i+1) hi) (H.upper i hi)
    calc
      (h (i+1) - h i) • term L (h i) ≤ (h (i+1):ℝ) / v := by
        rw [nsmul_eq_mul,term,mul_one_div]
        exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) vp.le
      _ = (c/a) * ((a * h (i+1)) / (c*v)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left compare (div_pos cp ap).le
  have shifted := H.total
  rw [sum_range_succ'] at shifted
  have tail : ∑ i ∈ range n, α (i+1)/γ (i+1) ≤ budget := by
    linarith [div_nonneg (an 0 (Nat.zero_le _)) (H.positive 0 (Nat.zero_le _)).le]
  apply (le_sum_schlomilch (fun _ _ hm le => term_antitone mono pos hm le) hpos inc n).trans
  apply add_le_add_left
  calc
    ∑ i ∈ range n, (h (i+1) - h i) • term L (h i)
      ≤ ∑ i ∈ range n, (c/a) * (α (i+1)/γ (i+1)) := sum_le_sum fun i hi => step i (mem_range.mp hi)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left tail (div_pos cp ap).le

private theorem summable_of_budget {L : ℕ → ℝ} (mono : Monotone L) (pos : ∀ n, 0 < L n)
    {budget : ℝ} (H : AdmitsBudget L budget) : Summable (term L) := by
  obtain ⟨h,α,γ,a,c,strict,hpos,ap,cp,lower,gpos,first,upper,cap⟩ := H
  apply summable_of_sum_range_le (c := (∑ k ∈ range (h 0), term L k) + (c/a)*budget) (term_nonneg pos)
  intro n
  exact (sum_le_sum_of_subset_of_nonneg (range_mono (strict.id_le n)) (fun k _ _ => term_nonneg pos k)).trans
    (partial_bound mono pos strict.monotone hpos ap cp
      (show FiniteBudget L a c budget h α γ n from
        ⟨fun i _ => lower i,fun i _ => gpos i,first,fun i _ => upper i,cap (n+1)⟩))

/-- Even schedules chosen separately for different finite boards have bounded
top scale when the series diverges and a, c and the budget are fixed. The
depth and the initial scale are allowed to vary. -/
theorem finite_height_bound {L : ℕ → ℝ} (mono : Monotone L) (pos : ∀ n, 0 < L n)
    (diverges : ¬ Summable fun k : ℕ => 1/L (2^k))
    {a c : ℝ} (ap : 0 < a) (cp : 0 < c) (budget : ℝ) :
    ∃ B : ℕ, ∀ (h : ℕ → ℕ) (α γ : ℕ → ℝ) (n : ℕ), Monotone h → (∀ j, 0 < h j) →
      FiniteBudget L a c budget h α γ n → h n < B := by
  let start := ⌈(c/a)*budget⌉₊
  let cap := (∑ k ∈ range start, term L k) + (c/a)*budget
  obtain ⟨B,exceeds⟩ : ∃ B, cap < ∑ k ∈ range B, term L k := by
    by_contra! bounded
    exact diverges ((condensed mono pos).mpr (summable_of_sum_range_le (term_nonneg pos) bounded))
  refine ⟨B,fun h α γ n inc hpos H => ?_⟩
  have an (i) (hi : i ≤ n) : 0 ≤ α i := (mul_nonneg ap.le (Nat.cast_nonneg _)).trans (H.lower i hi)
  have first : α 0 / γ 0 ≤ budget :=
    (single_le_sum (fun i (hi : i ∈ range (n+1)) =>
      div_nonneg (an i (Nat.le_of_lt_succ (mem_range.mp hi)))
        (H.positive i (Nat.le_of_lt_succ (mem_range.mp hi))).le)
      (mem_range.mpr (Nat.zero_lt_succ n))).trans H.total
  have a0 := div_le_div₀ (an 0 (Nat.zero_le _)) (H.lower 0 (Nat.zero_le _))
    (H.positive 0 (Nat.zero_le _)) H.initial
  have initial : (h 0:ℝ) ≤ (c/a)*budget := by
    have h := (div_le_iff₀ cp).mp (a0.trans first)
    rw [div_mul_eq_mul_div,le_div_iff₀ ap]; linarith
  have base : h 0 ≤ start := Nat.cast_le.mp (initial.trans (Nat.le_ceil _))
  have bound := (partial_bound mono pos inc hpos ap cp H).trans (add_le_add_right
    (sum_le_sum_of_subset_of_nonneg (range_mono base) (fun k _ _ => term_nonneg pos k)) _)
  by_contra! past
  exact (not_lt_of_ge ((sum_le_sum_of_subset_of_nonneg (range_mono past)
    (fun k _ _ => term_nonneg pos k)).trans bound)) exceeds

private theorem budget_of_condensed {L : ℕ → ℝ} (pos : ∀ n, 0 < L n)
    {budget : ℝ} (bp : 0 < budget) (H : Summable fun k : ℕ => 1/L (2^k)) :
    AdmitsBudget L budget := by
  let S := ∑' k : ℕ, 1 / L (2^k)
  have sn : 0 ≤ S := tsum_nonneg fun k => (one_div_pos.mpr (pos _)).le
  let c := (1 + 2*S) / budget
  have cp : 0 < c := div_pos (by linarith) bp
  let γ : ℕ → ℝ
    | 0 => c
    | k+1 => c * ((2:ℝ)^k * L (2^k))
  refine ⟨(2^·),(fun j => (2:ℝ)^j),γ,1,c,pow_right_strictMono₀ (by decide),
    fun _ => pow_pos (by decide) _,zero_lt_one,cp,by simp,?_,le_rfl,by simp [γ],?_⟩
  · intro j; cases j with
    | zero => exact cp
    | succ k => exact mul_pos cp (mul_pos (by positivity) (pos _))
  · intro n; cases n with
    | zero => simpa using bp.le
    | succ n =>
      rw [sum_range_succ']
      have eq (i : ℕ) : (2:ℝ)^(i+1) / γ (i+1) = (2/c)*(1/L (2^i)) := by
        simp only [γ,pow_succ]
        field_simp
      simp_rw [eq]
      rw [← mul_sum]
      have bound := H.sum_le_tsum (range n) (fun k _ => (one_div_pos.mpr (pos _)).le)
      calc
        (2/c) * (∑ i ∈ range n, 1/L (2^i)) + 2^0/γ 0 ≤ (2/c)*S + 1/c := by
          simpa only [pow_zero,γ] using add_le_add_right
            (mul_le_mul_of_nonneg_left bound (by positivity : 0 ≤ 2/c)) (1/c)
        _ = budget := by
          have cc : c * budget = 1+2*S := by simp [c,ne_of_gt bp]
          field_simp
          linarith

/-- An exact test for the two threshold conditions with linear retention cost.
Arbitrarily choosing widely separated dyadic scales gives no additional
summable profiles beyond what the logarithmic scales h_j = 2^j already allow. -/
theorem admitsBudget_iff {L : ℕ → ℝ} (mono : Monotone L) (pos : ∀ n, 0 < L n)
    {budget : ℝ} (bp : 0 < budget) :
    AdmitsBudget L budget ↔ Summable (fun k : ℕ => 1/L (2^k)) :=
  ⟨fun H => (condensed mono pos).mpr (summable_of_budget mono pos H),budget_of_condensed pos bp⟩

/-- For a power of the iterated logarithm as the extra volume factor, the
threshold accounting is possible precisely above exponent one. This addresses
only (G1), (G2) and the given linear lower bound on the retention cutoff. -/
theorem iterated_log_budget_iff (p : ℝ) (hp : 0 ≤ p) {budget : ℝ} (bp : 0 < budget) :
    AdmitsBudget (fun h => (1 + (Nat.log 2 h:ℝ))^p) budget ↔ 1 < p := by
  rw [admitsBudget_iff (budget := budget) (by
    intro m n le
    exact Real.rpow_le_rpow (by positivity) (by gcongr) hp)
    (fun n => Real.rpow_pos_of_pos (by positivity) _) bp]
  simp only [Nat.log_pow (by decide : 1 < 2)]
  convert Real.summable_one_div_nat_add_rpow 1 p using 2
  funext n
  rw [abs_of_nonneg (by positivity)]
  ring_nf

end
end GenLimit.KleinbergWei.Banach.ScaleThresholds
