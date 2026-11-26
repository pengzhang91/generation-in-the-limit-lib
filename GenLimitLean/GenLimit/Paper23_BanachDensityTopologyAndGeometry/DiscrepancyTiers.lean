import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! The tier convention in Theorem 5.9 of arXiv:2604.02385v2. -/

namespace GenLimit.KleinbergWei.Banach

/-- In the one-dimensional full integer lattice with exponent α = 1/2,
some nondegenerate interval exceeds the upper endpoint of every printed
tier. The result works with the paper's baseline constant for any ε. -/
theorem exists_interval_without_printed_tier (c : ℝ) (hc : 0 ≤ c) :
    ∃ L : ℕ, 0 < L ∧ ∀ j : ℕ,
      ¬ ((Finset.Icc (0 : ℤ) (L : ℤ)).card : ℝ) <
        (2 * c * Real.sqrt L) / (2 : ℝ)^j := by
  obtain ⟨n,hn⟩ := exists_nat_gt (2*c)
  have pos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  refine ⟨n^2, pow_pos (by exact_mod_cast pos) _, ?_⟩
  intro j
  have card : (Finset.Icc (0 : ℤ) ((n^2 : ℕ) : ℤ)).card = n^2+1 := by
    rw [Int.card_Icc]
    simpa only [sub_zero, ← Int.natCast_succ] using Int.toNat_natCast (n^2+1)
  rw [card, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Real.sqrt_sq (by positivity)]
  have div := div_le_self (show 0 ≤ 2*c*n by positivity)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j))
  exact not_lt_of_ge (div.trans (by nlinarith [mul_lt_mul_of_pos_right hn pos]))

/-- With a top tier that contains every dense rectangle, every positive
point count has a well-defined least tier. Here a = c₀ L^α. The original
upper cutoff still holds in every strictly positive tier. -/
theorem exists_least_sparsity_tier {a m : ℝ} (hm : 0 < m) :
    ∃ j : ℕ, a ≤ m * 2^j ∧ (∀ i < j, m * 2^i < a) ∧
      (0 < j → m * 2^j < 2*a) := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (a/m) (by norm_num : (1:ℝ) < 2)
  have existsTier : ∃ i : ℕ, a ≤ m * 2^i := ⟨n, by
    simpa [mul_comm] using ((div_lt_iff₀ hm).mp hn).le⟩
  classical
  let j := Nat.find existsTier
  have lower (i) (hi : i < j) : m * 2^i < a := lt_of_not_ge (Nat.find_min existsTier hi)
  refine ⟨j,Nat.find_spec existsTier,lower,?_⟩
  intro hj
  obtain ⟨p,hp⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have before := lower p (by omega)
  rw [hp,pow_succ]
  linarith

/-- In dimension one and exponent two, an admissible ε gives c₀ = 8.
At size two and tier two the paper bounds the number of traces through
zero by one. The closed unit intervals on its two sides have two distinct
traces. Both satisfy the original positive-tier inequalities. -/
theorem unit_traces_exceed_capacity :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ 2*Real.pi^2/(3*ε^2)=8 ∧
      ∃ T : Finset (Finset ℤ), 1 < T.card ∧
        (∀ R ∈ T, ∃ a : ℤ, R=Finset.Icc a (a+1) ∧ (0 : ℤ) ∈ R ∧ R.card=2) ∧
        (8:ℝ)/2^2 * 1^2 ≤ 2 ∧ (2:ℝ) < 8/2^(2-1 : ℕ) * 1^2 ∧
        (8:ℝ)⁻¹ * 2^2 * 2 = 1 := by
  let ε := Real.pi / Real.sqrt 12
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 12)
  have pos : 0 < Real.sqrt 12 := by positivity
  refine ⟨ε,div_pos Real.pi_pos pos,(div_lt_one pos).mpr ?_,?_,?_⟩
  · have approx := Real.pi_lt_d2
    nlinarith
  · dsimp only [ε]; field_simp; nlinarith [Real.pi_pos]
  · let F : Finset (Finset ℤ) := {Finset.Icc (-1) 0,Finset.Icc 0 1}
    refine ⟨F,by decide,?_,by norm_num,by norm_num,by norm_num⟩
    intro R hR
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at hR
    rcases hR with rfl | rfl
    · exact ⟨-1,rfl,by decide,by decide⟩
    · exact ⟨0,rfl,by decide,by decide⟩

end GenLimit.KleinbergWei.Banach
