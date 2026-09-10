import GenLimit.Paper30_TimeSensitiveLanguageGeneration.DeadlineDiagonal
import Mathlib.Data.Nat.Sqrt

/-!
# Appendix-D feasible-profile diagonal

This file continues the deterministic construction in Appendix D of
Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2.

There are two separate diagonalizations in the source proof:

* a slow index map `g = o(i)` along which a superlinear element-wise
  deadline remains superlinear; and
* for every positive integer denominator, an envelope `q_m = o(n)` for
  generalized-inverse values whose hallucination budgets lie below `n`.

The source simply asserts the existence of `g`.  We give a concrete
construction.  At index `n` take the integer geometric midpoint
`sqrt (n * D n)`, and let `g` be its generalized inverse.  Integer-scaled
estimates prove both required asymptotics without changing codomains.

The source later infers `D (s n) > t` from
`s n > D⁻¹(t)`.  This is not valid for an arbitrary nondecreasing deadline:
it needs strict growth after the inverse index.  The paper's stated feasible
profile includes discrete convexity and superlinearity, which supply
eventual strict growth.  We expose exactly the weaker premise actually used
below as `Deadline.EventuallyStrict`.
-/

namespace GenLimit.TimeSensitive

open Filter

/-! ## A concrete slow witness for a superlinear deadline -/

/-- Integer-scaled form of `D(n) / n → ∞`. -/
def Deadline.NatSuperlinear (D : Deadline) : Prop :=
  ∀ q, 0 < q → ∃ N, ∀ n, N ≤ n → q * n ≤ D n

/-- Integer-scaled form of `D(g(i)) / i → ∞`. -/
def NatSuperlinearAlong (D : Deadline) (g : ℕ → ℕ) : Prop :=
  ∀ q, 0 < q → ∃ N, ∀ i, N ≤ i → q * i ≤ D (g i)

/-- The integer geometric midpoint between the input index and its
deadline value. -/
def deadlineMidpointScale (D : Deadline) (n : ℕ) : ℕ :=
  Nat.sqrt (n * D n)

theorem deadlineMidpointScale_mono
    (D : Deadline) :
    Monotone (deadlineMidpointScale D) := by
  intro m n hmn
  apply Nat.sqrt_le_sqrt
  exact Nat.mul_le_mul hmn (D.monotone' hmn)

theorem Deadline.NatSuperlinear.isUnbounded
    (D : Deadline)
    (hD : D.NatSuperlinear) :
    D.IsUnbounded := by
  intro t
  obtain ⟨N, hN⟩ := hD 1 Nat.zero_lt_one
  let n := max N t
  refine ⟨n, (le_max_right N t).trans ?_⟩
  have hn : n ≤ D n := by
    simpa using hN n (le_max_left N t)
  exact hn

theorem deadlineMidpointScale_isUnbounded
    (D : Deadline)
    (hD : D.NatSuperlinear) :
    ∀ i, ∃ n, i ≤ deadlineMidpointScale D n := by
  intro i
  obtain ⟨N, hN⟩ := hD 1 Nat.zero_lt_one
  let n := max N i
  refine ⟨n, ?_⟩
  apply (le_max_right N i).trans
  apply Nat.le_sqrt.mpr
  have hn : n ≤ D n := by
    simpa using hN n (le_max_left N i)
  exact Nat.mul_le_mul_left n hn

/-- Concrete slow index map used for the source's asserted function `g`.

It is the least `n` whose geometric midpoint has reached `i`. -/
noncomputable def slowDeadlineWitness
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (i : ℕ) : ℕ :=
  Nat.find (deadlineMidpointScale_isUnbounded D hD i)

theorem slowDeadlineWitness_spec
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (i : ℕ) :
    i ≤ deadlineMidpointScale D (slowDeadlineWitness D hD i) :=
  Nat.find_spec (deadlineMidpointScale_isUnbounded D hD i)

theorem slowDeadlineWitness_min
    (D : Deadline)
    (hD : D.NatSuperlinear)
    {i n : ℕ}
    (hn : i ≤ deadlineMidpointScale D n) :
    slowDeadlineWitness D hD i ≤ n :=
  Nat.find_min' (deadlineMidpointScale_isUnbounded D hD i) hn

theorem slowDeadlineWitness_mono
    (D : Deadline)
    (hD : D.NatSuperlinear) :
    Monotone (slowDeadlineWitness D hD) := by
  intro i j hij
  apply slowDeadlineWitness_min D hD
  exact hij.trans (slowDeadlineWitness_spec D hD j)

theorem slowDeadlineWitness_tendsto_atTop
    (D : Deadline)
    (hD : D.NatSuperlinear) :
    Tendsto (slowDeadlineWitness D hD) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards
    [eventually_ge_atTop (deadlineMidpointScale D b + 1)] with i hi
  by_contra hnot
  have hlt : slowDeadlineWitness D hD i < b :=
    Nat.lt_of_not_ge hnot
  have hmid :
      deadlineMidpointScale D (slowDeadlineWitness D hD i) ≤
        deadlineMidpointScale D b :=
    deadlineMidpointScale_mono D hlt.le
  have hspec := slowDeadlineWitness_spec D hD i
  omega

theorem slowDeadlineWitness_sublinear
    (D : Deadline)
    (hD : D.NatSuperlinear) :
    NatSublinear (slowDeadlineWitness D hD) := by
  intro q hq
  let a := 2 * q
  obtain ⟨N, hN⟩ := hD (a * a) (Nat.mul_pos (by omega) (by omega))
  let N' := max N 1
  refine ⟨q * N', ?_⟩
  intro i hi
  let n := i / q
  have hnN' : N' ≤ n := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa [n, Nat.mul_comm] using hi
  have hnN : N ≤ n := (le_max_left N 1).trans hnN'
  have hnOne : 1 ≤ n := (le_max_right N 1).trans hnN'
  have hdeadline : (a * a) * n ≤ D n :=
    hN n hnN
  have hiUpper : i ≤ a * n := by
    have hdiv : i < q * (i / q + 1) :=
      Nat.lt_mul_div_succ i hq
    have hqle : q ≤ q * n := by
      simpa using Nat.mul_le_mul_left q hnOne
    calc
      i ≤ q * (i / q + 1) := hdiv.le
      _ = q * n + q := by simp [n, Nat.mul_add]
      _ ≤ q * n + q * n := Nat.add_le_add_left hqle _
      _ = a * n := by simp [a, two_mul, add_mul]
  have hsquare :
      (a * n) * (a * n) ≤ n * D n := by
    calc
      (a * n) * (a * n) = n * ((a * a) * n) := by ring
      _ ≤ n * D n := Nat.mul_le_mul_left n hdeadline
  have hmid : a * n ≤ deadlineMidpointScale D n := by
    exact Nat.le_sqrt.mpr hsquare
  have hslow : slowDeadlineWitness D hD i ≤ n :=
    slowDeadlineWitness_min D hD (hiUpper.trans hmid)
  calc
    q * slowDeadlineWitness D hD i ≤ q * n :=
      Nat.mul_le_mul_left q hslow
    _ ≤ i := by
      simpa [n, Nat.mul_comm] using Nat.mul_div_le i q

theorem slowDeadlineWitness_superlinearAlong
    (D : Deadline)
    (hD : D.NatSuperlinear) :
    NatSuperlinearAlong D (slowDeadlineWitness D hD) := by
  intro q hq
  obtain ⟨N, hN⟩ := hD (q * q) (Nat.mul_pos hq hq)
  have heventually :
      ∀ᶠ i : ℕ in atTop, N ≤ slowDeadlineWitness D hD i :=
    (tendsto_atTop.1 (slowDeadlineWitness_tendsto_atTop D hD)) N
  obtain ⟨I, hI⟩ := eventually_atTop.1 heventually
  refine ⟨I, ?_⟩
  intro i hi
  let g := slowDeadlineWitness D hD i
  have hgN : N ≤ g := hI i hi
  have hscale : (q * q) * g ≤ D g := hN g hgN
  have hsqrt :
      deadlineMidpointScale D g * deadlineMidpointScale D g ≤
        g * D g := by
    exact Nat.sqrt_le _
  have hsquares :
      (q * deadlineMidpointScale D g) *
          (q * deadlineMidpointScale D g) ≤
        D g * D g := by
    calc
      (q * deadlineMidpointScale D g) *
          (q * deadlineMidpointScale D g)
          = (q * q) *
              (deadlineMidpointScale D g *
                deadlineMidpointScale D g) := by ring
      _ ≤ (q * q) * (g * D g) :=
        Nat.mul_le_mul_left (q * q) hsqrt
      _ = ((q * q) * g) * D g := by ring
      _ ≤ D g * D g := Nat.mul_le_mul_right (D g) hscale
  have hroot : q * deadlineMidpointScale D g ≤ D g :=
    Nat.mul_self_le_mul_self_iff.mp hsquares
  exact
    (Nat.mul_le_mul_left q
      (slowDeadlineWitness_spec D hD i)).trans hroot

theorem natSuperlinearAlong_tendsto
    (D : Deadline)
    (g : ℕ → ℕ)
    (h : NatSuperlinearAlong D g) :
    Tendsto (fun i : ℕ => (D (g i) : ℝ) / i) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨q, hbq⟩ := exists_nat_gt b
  obtain ⟨N, hN⟩ := h (q + 1) (Nat.succ_pos q)
  filter_upwards [eventually_ge_atTop (max N 1)] with i hi
  have hiN : N ≤ i := (le_max_left _ _).trans hi
  have hiPos : 0 < i :=
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hi)
  have hscaled : (q + 1) * i ≤ D (g i) := hN i hiN
  have hiReal : (0 : ℝ) < i := by exact_mod_cast hiPos
  have hratio : (q + 1 : ℝ) ≤ (D (g i) : ℝ) / i := by
    rw [le_div_iff₀ hiReal]
    exact_mod_cast hscaled
  exact (le_of_lt (hbq.trans_le (by norm_num))).trans hratio

theorem slowDeadlineWitness_superlinear
    (D : Deadline)
    (hD : D.NatSuperlinear) :
    Tendsto
      (fun i : ℕ => (D (slowDeadlineWitness D hD i) : ℝ) / i)
      atTop atTop :=
  natSuperlinearAlong_tendsto D (slowDeadlineWitness D hD)
    (slowDeadlineWitness_superlinearAlong D hD)

/-! ## Generalized-inverse envelopes below a natural budget -/

/-- Integer-scaled form of `a(t) = o(B(t))`.

In the source application, `a(t)` is the generalized inverse of the
element-wise deadline and `B(t)` is the integer part of `t H(t)`. -/
def NatLittleOAlongBudget (a B : ℕ → ℕ) : Prop :=
  ∀ q, 0 < q → ∃ T, ∀ t, T ≤ t → q * a t ≤ B t

/-- A cutoff beyond which the budget is larger than
`(m+1)(n+1)`.  The denominator is written `m+1` so the family is indexed
from zero while every source denominator remains positive. -/
noncomputable def budgetSublevelCutoff
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (m n : ℕ) : ℕ :=
  Classical.choose <|
    eventually_atTop.1 <|
      (tendsto_atTop.1 hB) ((m + 1) * (n + 1))

theorem budgetSublevelCutoff_spec
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (m n t : ℕ)
    (ht : budgetSublevelCutoff B hB m n ≤ t) :
    (m + 1) * (n + 1) ≤ B t :=
  Classical.choose_spec
    (eventually_atTop.1 <|
      (tendsto_atTop.1 hB) ((m + 1) * (n + 1))) t ht

theorem inverseBudgetBound_exists
    (D : Deadline)
    (hD : D.IsUnbounded)
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (m n : ℕ) :
    ∃ Q : ℕ, 0 < Q ∧
      ∀ t, B t / (m + 1) ≤ n → D.inverse hD t < Q := by
  let C := budgetSublevelCutoff B hB m n
  let M := (Finset.range C).sup (fun t => D.inverse hD t)
  refine ⟨M + 1, Nat.succ_pos M, ?_⟩
  intro t ht
  have htC : t < C := by
    by_contra hnot
    have hbudget :
        (m + 1) * (n + 1) ≤ B t :=
      budgetSublevelCutoff_spec B hB m n t
        (Nat.le_of_not_gt hnot)
    have hquotient : n + 1 ≤ B t / (m + 1) := by
      apply (Nat.le_div_iff_mul_le (Nat.succ_pos m)).2
      simpa [Nat.mul_comm] using hbudget
    omega
  exact
    (Finset.le_sup
      (s := Finset.range C)
      (f := fun u => D.inverse hD u)
      (b := t) (Finset.mem_range.mpr htC)).trans_lt
      (Nat.lt_succ_self M)

/-- The least positive strict upper bound on inverse values whose normalized
budget is at most `n`.

This is definitionally independent of any chosen finite cutoff and is
equivalent to the source's
`1 + max {D⁻¹(t) : floor(B(t)/(m+1)) ≤ n}`. -/
noncomputable def inverseBudgetEnvelope
    (D : Deadline)
    (hD : D.IsUnbounded)
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (m n : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (inverseBudgetBound_exists D hD B hB m n)

theorem inverseBudgetEnvelope_pos
    (D : Deadline)
    (hD : D.IsUnbounded)
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (m n : ℕ) :
    0 < inverseBudgetEnvelope D hD B hB m n := by
  classical
  exact (Nat.find_spec (inverseBudgetBound_exists D hD B hB m n)).1

theorem inverse_lt_inverseBudgetEnvelope
    (D : Deadline)
    (hD : D.IsUnbounded)
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (m n t : ℕ)
    (ht : B t / (m + 1) ≤ n) :
    D.inverse hD t < inverseBudgetEnvelope D hD B hB m n := by
  classical
  exact
    (Nat.find_spec (inverseBudgetBound_exists D hD B hB m n)).2 t ht

theorem inverseBudgetEnvelope_min
    (D : Deadline)
    (hD : D.IsUnbounded)
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (m n Q : ℕ)
    (hQ : 0 < Q)
    (hbound : ∀ t, B t / (m + 1) ≤ n → D.inverse hD t < Q) :
    inverseBudgetEnvelope D hD B hB m n ≤ Q := by
  classical
  exact
    Nat.find_min' (inverseBudgetBound_exists D hD B hB m n)
      ⟨hQ, hbound⟩

theorem inverseBudgetEnvelope_mono
    (D : Deadline)
    (hD : D.IsUnbounded)
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (m : ℕ) :
    Monotone (inverseBudgetEnvelope D hD B hB m) := by
  intro n n' hnn'
  apply inverseBudgetEnvelope_min D hD B hB m n
    (inverseBudgetEnvelope D hD B hB m n')
    (inverseBudgetEnvelope_pos D hD B hB m n')
  intro t ht
  exact inverse_lt_inverseBudgetEnvelope D hD B hB m n' t
    (ht.trans hnn')

theorem inverseBudgetEnvelope_sublinear
    (D : Deadline)
    (hD : D.IsUnbounded)
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (hinverse :
      NatLittleOAlongBudget (D.inverse hD) B)
    (m : ℕ) :
    NatSublinear (inverseBudgetEnvelope D hD B hB m) := by
  intro q hq
  let c := (2 * q) * (m + 1)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  obtain ⟨T, hT⟩ := hinverse c hc
  let M := (Finset.range T).sup (fun t => D.inverse hD t)
  refine ⟨max (q * (M + 1)) (2 * q), ?_⟩
  intro n hn
  have hnEarly : q * (M + 1) ≤ n :=
    (le_max_left _ _).trans hn
  have hnScale : 2 * q ≤ n :=
    (le_max_right _ _).trans hn
  have hqn : q ≤ n := by omega
  have hquotientPos : 0 < n / q :=
    Nat.div_pos hqn hq
  have henvelope :
      inverseBudgetEnvelope D hD B hB m n ≤ n / q := by
    apply inverseBudgetEnvelope_min D hD B hB m n (n / q)
      hquotientPos
    intro t ht
    by_cases htT : t < T
    · have hinverseM : D.inverse hD t ≤ M :=
        Finset.le_sup
          (s := Finset.range T)
          (f := fun u => D.inverse hD u)
          (b := t) (Finset.mem_range.mpr htT)
      have hMquotient : M + 1 ≤ n / q := by
        apply (Nat.le_div_iff_mul_le hq).2
        simpa [Nat.mul_comm] using hnEarly
      exact hinverseM.trans_lt
        ((Nat.lt_succ_self M).trans_le hMquotient)
    · have htLate : T ≤ t := Nat.le_of_not_gt htT
      have hscaled : c * D.inverse hD t ≤ B t :=
        hT t htLate
      have hbudget :
          B t < (n + 1) * (m + 1) := by
        apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).1
        exact Nat.lt_succ_of_le ht
      have hproduct :
          (m + 1) * ((2 * q) * D.inverse hD t) <
            (m + 1) * (n + 1) := by
        calc
          (m + 1) * ((2 * q) * D.inverse hD t)
              = c * D.inverse hD t := by
                simp [c, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ ≤ B t := hscaled
          _ < (n + 1) * (m + 1) := hbudget
          _ = (m + 1) * (n + 1) := by
            rw [Nat.mul_comm]
      have htwice :
          (2 * q) * D.inverse hD t ≤ n := by
        have :=
          (Nat.mul_lt_mul_left (Nat.succ_pos m)).mp hproduct
        omega
      by_cases hinv : D.inverse hD t = 0
      · simpa [hinv] using hquotientPos
      · have hinvPos : 1 ≤ D.inverse hD t :=
          Nat.one_le_iff_ne_zero.mpr hinv
        have hqle :
            q ≤ q * D.inverse hD t := by
          simpa using Nat.mul_le_mul_left q hinvPos
        have hsucc :
            q * (D.inverse hD t + 1) ≤ n := by
          calc
            q * (D.inverse hD t + 1)
                = q * D.inverse hD t + q := by
                  rw [Nat.mul_add, Nat.mul_one]
            _ ≤ q * D.inverse hD t +
                  q * D.inverse hD t :=
              Nat.add_le_add_left hqle _
            _ = (2 * q) * D.inverse hD t := by
              simp [two_mul, add_mul]
            _ ≤ n := htwice
        have :
            D.inverse hD t + 1 ≤ n / q :=
          (Nat.le_div_iff_mul_le hq).2
            (by simpa [Nat.mul_comm] using hsucc)
        omega
  calc
    q * inverseBudgetEnvelope D hD B hB m n
        ≤ q * (n / q) := Nat.mul_le_mul_left q henvelope
    _ ≤ n := by
      simpa [Nat.mul_comm] using Nat.mul_div_le n q

/-! ## Natural-valued deterministic profile estimates -/

/-- Eventual strict growth, the exact property used when the source turns
an index strictly above `D⁻¹(t)` into a deadline strictly after `t`.

The paper assumes discrete convexity and superlinearity for feasible
deadlines; those hypotheses imply this eventual property. -/
def Deadline.EventuallyStrict (D : Deadline) : Prop :=
  ∃ N, ∀ ⦃a b : ℕ⦄, N ≤ a → a < b → D a < D b

/-- Natural discrete convexity: successive deadline increments are
nondecreasing. -/
def Deadline.DiscreteConvex (D : Deadline) : Prop :=
  Monotone (fun n => D (n + 1) - D n)

theorem Deadline.exists_strict_step
    (D : Deadline)
    (hD : D.IsUnbounded) :
    ∃ j, D j < D (j + 1) := by
  obtain ⟨n, hn⟩ := hD (D 0 + 1)
  have h0n : D 0 < D n := by omega
  have aux :
      ∀ k : ℕ, D 0 < D k →
        ∃ j, j < k ∧ D j < D (j + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro hk
        by_cases hprev : D 0 < D k
        · obtain ⟨j, hjk, hj⟩ := ih hprev
          exact ⟨j, hjk.trans (Nat.lt_succ_self k), hj⟩
        · have hk0 : D k ≤ D 0 := Nat.le_of_not_gt hprev
          have h0k : D 0 ≤ D k := D.monotone' (Nat.zero_le k)
          have heq : D k = D 0 := Nat.le_antisymm hk0 h0k
          exact ⟨k, Nat.lt_succ_self k, by simpa [heq] using hk⟩
  obtain ⟨j, -, hj⟩ := aux n h0n
  exact ⟨j, hj⟩

theorem Deadline.NatSuperlinear.eventuallyStrict_of_discreteConvex
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (hconvex : D.DiscreteConvex) :
    D.EventuallyStrict := by
  obtain ⟨j, hj⟩ :=
    D.exists_strict_step hD.isUnbounded
  refine ⟨j, ?_⟩
  intro a b hja hab
  have hincrement :
      D (j + 1) - D j ≤ D (a + 1) - D a :=
    hconvex hja
  have hpositive : 0 < D (a + 1) - D a :=
    (Nat.sub_pos_iff_lt.mpr hj).trans_le hincrement
  have hstep : D a < D (a + 1) :=
    Nat.sub_pos_iff_lt.mp hpositive
  exact hstep.trans_le (D.monotone' (Nat.succ_le_of_lt hab))

theorem Deadline.inverse_tendsto_atTop
    (D : Deadline)
    (hD : D.IsUnbounded) :
    Tendsto (D.inverse hD) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (D b + 1)] with t ht
  by_contra hnot
  have hinv : D.inverse hD t ≤ b :=
    (Nat.lt_of_not_ge hnot).le
  have hvalue :
      D (D.inverse hD t) ≤ D b :=
    D.monotone' hinv
  have hspec := D.le_inverse_value hD t
  omega

/-- The natural-valued deterministic assumptions used by Appendix-D's
deadline construction.

`budget t` represents the integer part of `t H(t)`.  Its divergence and
the `inverseLittleO` field are precisely the two properties of that product
used in the `q_m` diagonal. -/
structure NaturalFeasibleProfile where
  deadline : Deadline
  deadlineSuperlinear : deadline.NatSuperlinear
  deadlineEventuallyStrict : deadline.EventuallyStrict
  budget : ℕ → ℕ
  budget_tendsto : Tendsto budget atTop atTop
  inverseLittleO :
    NatLittleOAlongBudget
      (deadline.inverse deadlineSuperlinear.isUnbounded) budget

/-- Constructor matching the paper's stated deterministic deadline
assumptions.  Discrete convexity is used only to derive eventual strictness. -/
def NaturalFeasibleProfile.ofDiscreteConvex
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (hconvex : D.DiscreteConvex)
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (hinverse :
      NatLittleOAlongBudget (D.inverse hD.isUnbounded) B) :
    NaturalFeasibleProfile where
  deadline := D
  deadlineSuperlinear := hD
  deadlineEventuallyStrict :=
    hD.eventuallyStrict_of_discreteConvex D hconvex
  budget := B
  budget_tendsto := hB
  inverseLittleO := hinverse

namespace NaturalFeasibleProfile

/-- The source family `{g,q₁,q₂,...}`, with zero-based envelope indices. -/
noncomputable def diagonalFamily
    (P : NaturalFeasibleProfile) : ℕ → ℕ → ℕ
  | 0 => slowDeadlineWitness P.deadline P.deadlineSuperlinear
  | m + 1 =>
      inverseBudgetEnvelope P.deadline
        P.deadlineSuperlinear.isUnbounded
        P.budget P.budget_tendsto m

theorem diagonalFamily_zero
    (P : NaturalFeasibleProfile) :
    P.diagonalFamily 0 =
      slowDeadlineWitness P.deadline P.deadlineSuperlinear :=
  rfl

theorem diagonalFamily_succ
    (P : NaturalFeasibleProfile)
    (m : ℕ) :
    P.diagonalFamily (m + 1) =
      inverseBudgetEnvelope P.deadline
        P.deadlineSuperlinear.isUnbounded
        P.budget P.budget_tendsto m :=
  rfl

theorem diagonalFamily_mono
    (P : NaturalFeasibleProfile)
    (m : ℕ) :
    Monotone (P.diagonalFamily m) := by
  cases m with
  | zero =>
      exact slowDeadlineWitness_mono
        P.deadline P.deadlineSuperlinear
  | succ m =>
      exact inverseBudgetEnvelope_mono P.deadline
        P.deadlineSuperlinear.isUnbounded
        P.budget P.budget_tendsto m

theorem diagonalFamily_sublinear
    (P : NaturalFeasibleProfile)
    (m : ℕ) :
    NatSublinear (P.diagonalFamily m) := by
  cases m with
  | zero =>
      exact slowDeadlineWitness_sublinear
        P.deadline P.deadlineSuperlinear
  | succ m =>
      exact inverseBudgetEnvelope_sublinear P.deadline
        P.deadlineSuperlinear.isUnbounded
        P.budget P.budget_tendsto
        P.inverseLittleO m

/-- The instantiated countable diagonal from the source family
`{g,q₁,q₂,...}`. -/
noncomputable def diagonal
    (P : NaturalFeasibleProfile) : ℕ → ℕ :=
  countableDiagonal P.diagonalFamily P.diagonalFamily_sublinear

theorem diagonal_mono
    (P : NaturalFeasibleProfile) :
    Monotone P.diagonal :=
  countableDiagonal_mono P.diagonalFamily
    P.diagonalFamily_sublinear P.diagonalFamily_mono

theorem diagonal_sublinear
    (P : NaturalFeasibleProfile) :
    NatSublinear P.diagonal :=
  countableDiagonal_sublinear P.diagonalFamily
    P.diagonalFamily_sublinear

theorem diagonal_tendsto_atTop
    (P : NaturalFeasibleProfile) :
    Tendsto P.diagonal atTop atTop :=
  countableDiagonal_tendsto_atTop P.diagonalFamily
    P.diagonalFamily_sublinear

theorem slowDeadlineWitness_eventually_le_diagonal
    (P : NaturalFeasibleProfile) :
    ∀ᶠ i : ℕ in atTop,
      slowDeadlineWitness P.deadline P.deadlineSuperlinear i ≤
        P.diagonal i := by
  simpa [diagonal, diagonalFamily] using
    (countableDiagonal_eventually_dominates
      P.diagonalFamily P.diagonalFamily_sublinear 0)

theorem inverseBudgetEnvelope_eventually_le_diagonal
    (P : NaturalFeasibleProfile)
    (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      inverseBudgetEnvelope P.deadline
          P.deadlineSuperlinear.isUnbounded
          P.budget P.budget_tendsto m n ≤
        P.diagonal n := by
  simpa [diagonal, diagonalFamily] using
    (countableDiagonal_eventually_dominates
      P.diagonalFamily P.diagonalFamily_sublinear (m + 1))

/-- Appendix-D's concrete prefix deadline `D_pfx(i)=D_el(s(i))`. -/
noncomputable def prefixDeadline
    (P : NaturalFeasibleProfile) : Deadline :=
  slowedDeadline P.deadline P.diagonalFamily
    P.diagonalFamily_sublinear P.diagonalFamily_mono

theorem prefixDeadline_apply
    (P : NaturalFeasibleProfile)
    (i : ℕ) :
    P.prefixDeadline i = P.deadline (P.diagonal i) :=
  rfl

theorem prefixDeadline_isUnbounded
    (P : NaturalFeasibleProfile) :
    P.prefixDeadline.IsUnbounded :=
  slowedDeadline_isUnbounded P.deadline
    P.deadlineSuperlinear.isUnbounded
    P.diagonalFamily P.diagonalFamily_sublinear
    P.diagonalFamily_mono

theorem prefixDeadline_superlinear
    (P : NaturalFeasibleProfile) :
    Tendsto
      (fun i : ℕ => (P.prefixDeadline i : ℝ) / i)
      atTop atTop := by
  exact slowedDeadline_superlinear_of_member P.deadline
    P.diagonalFamily P.diagonalFamily_sublinear
    P.diagonalFamily_mono 0
    (by
      simpa [diagonalFamily] using
        slowDeadlineWitness_superlinear
          P.deadline P.deadlineSuperlinear)

theorem prefixDeadline_exceptionRatio_tendsto_zero
    (P : NaturalFeasibleProfile) :
    Tendsto
      (deadlineExceptionRatio P.deadline P.prefixDeadline)
      atTop (nhds 0) :=
  deadlineExceptionRatio_slowed_tendsto_zero P.deadline
    P.diagonalFamily P.diagonalFamily_sublinear
    P.diagonalFamily_mono

theorem lowerPrefixWiseDensity_prefixDeadline_le
    (P : NaturalFeasibleProfile)
    (S R : ℕ → α)
    (hR : Function.Injective R) :
    lowerPrefixWiseDensity S R P.prefixDeadline ≤
      lowerTimelyDensity S R P.deadline :=
  lowerPrefixWiseDensity_slowed_le_lowerTimelyDensity S R hR
    P.deadline P.diagonalFamily P.diagonalFamily_sublinear
    P.diagonalFamily_mono

/-! ## Strict inverse and the source's `τ` estimate -/

/-- Least index whose deadline is strictly after `t`.

For natural-valued deadlines this is the ordinary generalized inverse at
`t+1`. -/
noncomputable def strictDeadlineInverse
    (D : Deadline)
    (hD : D.IsUnbounded)
    (t : ℕ) : ℕ :=
  D.inverse hD (t + 1)

theorem lt_strictDeadlineInverse_value
    (D : Deadline)
    (hD : D.IsUnbounded)
    (t : ℕ) :
    t < D (strictDeadlineInverse D hD t) := by
  exact Nat.lt_of_succ_le (D.le_inverse_value hD (t + 1))

theorem strictDeadlineInverse_min
    (D : Deadline)
    (hD : D.IsUnbounded)
    {t n : ℕ}
    (hn : t < D n) :
    strictDeadlineInverse D hD t ≤ n := by
  apply D.inverse_min hD
  exact Nat.succ_le_of_lt hn

theorem strictDeadlineInverse_mono
    (D : Deadline)
    (hD : D.IsUnbounded) :
    Monotone (strictDeadlineInverse D hD) := by
  intro s t hst
  exact D.inverse_mono hD (Nat.succ_le_succ hst)

theorem strictDeadlineInverse_tendsto_atTop
    (D : Deadline)
    (hD : D.IsUnbounded) :
    Tendsto (strictDeadlineInverse D hD) atTop atTop := by
  simpa [strictDeadlineInverse] using
    (D.inverse_tendsto_atTop hD).comp
      (tendsto_add_atTop_nat 1)

theorem tendsto_nat_div_atTop
    (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (q : ℕ)
    (hq : 0 < q) :
    Tendsto (fun t => B t / q) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards
    [(tendsto_atTop.1 hB) (n * q)] with t ht
  exact (Nat.le_div_iff_mul_le hq).2 ht

/-- The strict inverse `τ(t)=min{n:D_pfx(n)>t}` used by the source. -/
noncomputable def prefixTau
    (P : NaturalFeasibleProfile)
    (t : ℕ) : ℕ :=
  strictDeadlineInverse P.prefixDeadline
    P.prefixDeadline_isUnbounded t

theorem prefixTau_le_budget_div_eventually
    (P : NaturalFeasibleProfile)
    (m : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      P.prefixTau t ≤ P.budget t / (m + 1) := by
  let n : ℕ → ℕ := fun t => P.budget t / (m + 1)
  have hnTop : Tendsto n atTop atTop := by
    exact tendsto_nat_div_atTop P.budget P.budget_tendsto
      (m + 1) (Nat.succ_pos m)
  have hdom :
      ∀ᶠ t : ℕ in atTop,
        inverseBudgetEnvelope P.deadline
            P.deadlineSuperlinear.isUnbounded
            P.budget P.budget_tendsto m (n t) ≤
          P.diagonal (n t) :=
    hnTop.eventually (P.inverseBudgetEnvelope_eventually_le_diagonal m)
  obtain ⟨Nstrict, hstrict⟩ := P.deadlineEventuallyStrict
  have hinverseTop :
      ∀ᶠ t : ℕ in atTop,
        Nstrict ≤
          P.deadline.inverse
            P.deadlineSuperlinear.isUnbounded t :=
    (tendsto_atTop.1
      (P.deadline.inverse_tendsto_atTop
        P.deadlineSuperlinear.isUnbounded)) Nstrict
  filter_upwards [hdom, hinverseTop] with t hdomt hinverseN
  have henvelope :
      P.deadline.inverse
          P.deadlineSuperlinear.isUnbounded t <
        inverseBudgetEnvelope P.deadline
          P.deadlineSuperlinear.isUnbounded
          P.budget P.budget_tendsto m (n t) := by
    apply inverse_lt_inverseBudgetEnvelope
    exact le_rfl
  have hinverseDiagonal :
      P.deadline.inverse
          P.deadlineSuperlinear.isUnbounded t <
        P.diagonal (n t) :=
    henvelope.trans_le hdomt
  have hdeadlineStrict :
      P.deadline
          (P.deadline.inverse
            P.deadlineSuperlinear.isUnbounded t) <
        P.deadline (P.diagonal (n t)) :=
    hstrict hinverseN hinverseDiagonal
  have ht :
      t < P.prefixDeadline (n t) := by
    rw [P.prefixDeadline_apply]
    exact
      (P.deadline.le_inverse_value
        P.deadlineSuperlinear.isUnbounded t).trans_lt
        hdeadlineStrict
  exact strictDeadlineInverse_min P.prefixDeadline
    P.prefixDeadline_isUnbounded ht

/-- Natural-valued conclusion `τ(t)=o(tH(t))` of the source's window
construction, with `budget(t)` representing `floor(tH(t))`. -/
theorem prefixTau_littleO_budget
    (P : NaturalFeasibleProfile) :
    NatLittleOAlongBudget P.prefixTau P.budget := by
  intro q hq
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have heventually :=
    P.prefixTau_le_budget_div_eventually m
  obtain ⟨T, hT⟩ := eventually_atTop.1 heventually
  refine ⟨T, ?_⟩
  intro t ht
  calc
    (m + 1) * P.prefixTau t
        ≤ (m + 1) * (P.budget t / (m + 1)) :=
      Nat.mul_le_mul_left (m + 1) (hT t ht)
    _ ≤ P.budget t := by
      simpa [Nat.mul_comm] using
        Nat.mul_div_le (P.budget t) (m + 1)

/-! ## A natural-valued prefix hallucination budget -/

theorem prefixTau_tendsto_atTop
    (P : NaturalFeasibleProfile) :
    Tendsto P.prefixTau atTop atTop := by
  simpa [prefixTau] using
    strictDeadlineInverse_tendsto_atTop P.prefixDeadline
      P.prefixDeadline_isUnbounded

/-- Integer geometric mean of the strict-inverse scale and the original
hallucination budget.

This is the natural-valued counterpart of the source's
`H_pfx = H_el / sqrt(a)`: it lies asymptotically strictly between `τ` and
the original budget whenever `τ=o(budget)`. -/
noncomputable def prefixBudget
    (P : NaturalFeasibleProfile)
    (t : ℕ) : ℕ :=
  Nat.sqrt (P.prefixTau t * P.budget t)

theorem prefixTau_littleO_prefixBudget
    (P : NaturalFeasibleProfile) :
    NatLittleOAlongBudget P.prefixTau P.prefixBudget := by
  intro q hq
  obtain ⟨T, hT⟩ :=
    P.prefixTau_littleO_budget (q * q) (Nat.mul_pos hq hq)
  refine ⟨T, ?_⟩
  intro t ht
  apply Nat.le_sqrt.mpr
  calc
    (q * P.prefixTau t) * (q * P.prefixTau t)
        = P.prefixTau t *
            ((q * q) * P.prefixTau t) := by ring
    _ ≤ P.prefixTau t * P.budget t :=
      Nat.mul_le_mul_left (P.prefixTau t) (hT t ht)

theorem prefixBudget_littleO_budget
    (P : NaturalFeasibleProfile) :
    NatLittleOAlongBudget P.prefixBudget P.budget := by
  intro q hq
  obtain ⟨T, hT⟩ :=
    P.prefixTau_littleO_budget (q * q) (Nat.mul_pos hq hq)
  refine ⟨T, ?_⟩
  intro t ht
  have hsqrt :
      P.prefixBudget t * P.prefixBudget t ≤
        P.prefixTau t * P.budget t := by
    exact Nat.sqrt_le _
  have hsquares :
      (q * P.prefixBudget t) * (q * P.prefixBudget t) ≤
        P.budget t * P.budget t := by
    calc
      (q * P.prefixBudget t) * (q * P.prefixBudget t)
          = (q * q) *
              (P.prefixBudget t * P.prefixBudget t) := by ring
      _ ≤ (q * q) * (P.prefixTau t * P.budget t) :=
        Nat.mul_le_mul_left (q * q) hsqrt
      _ = ((q * q) * P.prefixTau t) * P.budget t := by ring
      _ ≤ P.budget t * P.budget t :=
        Nat.mul_le_mul_right (P.budget t) (hT t ht)
  exact Nat.mul_self_le_mul_self_iff.mp hsquares

theorem prefixBudget_eventually_le_budget
    (P : NaturalFeasibleProfile) :
    ∀ᶠ t : ℕ in atTop, P.prefixBudget t ≤ P.budget t := by
  obtain ⟨T, hT⟩ :=
    P.prefixBudget_littleO_budget 1 Nat.zero_lt_one
  filter_upwards [eventually_ge_atTop T] with t ht
  simpa using hT t ht

theorem prefixBudget_tendsto_atTop
    (P : NaturalFeasibleProfile) :
    Tendsto P.prefixBudget atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨T, hT⟩ :=
    P.prefixTau_littleO_budget 1 Nat.zero_lt_one
  filter_upwards
    [(tendsto_atTop.1 P.prefixTau_tendsto_atTop) b,
      eventually_ge_atTop T] with t hbt ht
  apply hbt.trans
  apply Nat.le_sqrt.mpr
  have hle : P.prefixTau t ≤ P.budget t := by
    simpa using hT t ht
  exact Nat.mul_le_mul_left (P.prefixTau t) hle

/-- Real rate canonically associated with the natural prefix budget. -/
noncomputable def prefixRate
    (P : NaturalFeasibleProfile)
    (t : ℕ) : ℝ :=
  natRatio P.prefixBudget t

theorem prefixRate_nonneg
    (P : NaturalFeasibleProfile)
    (t : ℕ) :
    0 ≤ P.prefixRate t :=
  natRatio_nonneg P.prefixBudget t

theorem prefixRate_eventually_le_original
    (P : NaturalFeasibleProfile) :
    ∀ᶠ t : ℕ in atTop,
      P.prefixRate t ≤ natRatio P.budget t := by
  filter_upwards [P.prefixBudget_eventually_le_budget] with t ht
  by_cases ht0 : t = 0
  · simp [prefixRate, natRatio, ht0]
  · simp only [prefixRate, natRatio, ht0, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast ht) (Nat.cast_nonneg t)

theorem prefixRate_tendsto_zero
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0)) :
    Tendsto P.prefixRate atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall P.prefixRate_nonneg
  · exact P.prefixRate_eventually_le_original
  · exact hvanishing

/-- Ratio of two natural-valued scales, totalized when the denominator
vanishes. -/
noncomputable def relativeNatRatio
    (a B : ℕ → ℕ)
    (t : ℕ) : ℝ :=
  if B t = 0 then 0 else (a t : ℝ) / B t

theorem relativeNatRatio_nonneg
    (a B : ℕ → ℕ)
    (t : ℕ) :
    0 ≤ relativeNatRatio a B t := by
  by_cases hB : B t = 0
  · simp [relativeNatRatio, hB]
  · simp only [relativeNatRatio, hB, if_false]
    positivity

theorem relativeNatRatio_tendsto_zero
    (a B : ℕ → ℕ)
    (h : NatLittleOAlongBudget a B) :
    Tendsto (relativeNatRatio a B) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hqε⟩ := exists_nat_one_div_lt hε
  obtain ⟨T, hT⟩ := h (q + 1) (Nat.succ_pos q)
  refine ⟨T, ?_⟩
  intro t ht
  by_cases hBzero : B t = 0
  · simpa [relativeNatRatio, hBzero] using hε
  · have hBpos : 0 < B t := Nat.pos_of_ne_zero hBzero
    have hscaled : (q + 1) * a t ≤ B t := hT t ht
    have hqPosReal : (0 : ℝ) < q + 1 := by positivity
    have hBPosReal : (0 : ℝ) < B t := by exact_mod_cast hBpos
    have hratio :
        (a t : ℝ) / B t ≤ 1 / (q + 1 : ℝ) := by
      rw [div_le_div_iff₀ hBPosReal hqPosReal]
      have hscaledReal :
          (((q + 1 : ℕ) : ℝ) * (a t : ℝ)) ≤ (B t : ℝ) := by
        exact_mod_cast hscaled
      simpa [mul_comm] using hscaledReal
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (relativeNatRatio_nonneg a B t)]
    rw [relativeNatRatio, if_neg hBzero]
    exact hratio.trans_lt hqε

theorem prefixTau_rate_ratio_tendsto_zero
    (P : NaturalFeasibleProfile) :
    Tendsto
      (fun t =>
        natRatio P.prefixTau t / P.prefixRate t)
      atTop (nhds 0) := by
  have hrelative :
      Tendsto
        (relativeNatRatio P.prefixTau P.prefixBudget)
        atTop (nhds 0) :=
    relativeNatRatio_tendsto_zero
      P.prefixTau P.prefixBudget
      P.prefixTau_littleO_prefixBudget
  have heq :
      ∀ᶠ t : ℕ in atTop,
        natRatio P.prefixTau t / P.prefixRate t =
          relativeNatRatio P.prefixTau P.prefixBudget t := by
    filter_upwards
      [(tendsto_atTop.1 P.prefixBudget_tendsto_atTop) 1,
        eventually_ge_atTop 1] with t hbudget ht
    have ht0 : t ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le ht)
    have hbudget0 : P.prefixBudget t ≠ 0 :=
      Nat.ne_of_gt (Nat.zero_lt_one.trans_le hbudget)
    simp only [prefixRate, natRatio, relativeNatRatio,
      ht0, hbudget0, if_false]
    field_simp
  exact Filter.Tendsto.congr'
    (Filter.EventuallyEq.symm heq) hrelative

theorem deadlineInverse_le_prefixTau
    (P : NaturalFeasibleProfile)
    (t : ℕ) :
    P.prefixDeadline.inverse P.prefixDeadline_isUnbounded t ≤
      P.prefixTau t := by
  exact P.prefixDeadline.inverse_mono
    P.prefixDeadline_isUnbounded (Nat.le_succ t)

/-- Feasibility conclusion for the constructed real prefix rate:
`D_pfx⁻¹(t)/t = o(H_pfx(t))`. -/
theorem prefixInverse_rate_ratio_tendsto_zero
    (P : NaturalFeasibleProfile) :
    Tendsto
      (fun t =>
        natRatio
            (P.prefixDeadline.inverse
              P.prefixDeadline_isUnbounded) t /
          P.prefixRate t)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t => by
      exact div_nonneg
        (natRatio_nonneg
          (P.prefixDeadline.inverse
            P.prefixDeadline_isUnbounded) t)
        (P.prefixRate_nonneg t)
  · exact Filter.Eventually.of_forall fun t => by
      apply div_le_div_of_nonneg_right
      · have hNat :
            natRatio
                (P.prefixDeadline.inverse
                  P.prefixDeadline_isUnbounded) t ≤
              natRatio P.prefixTau t := by
          by_cases ht : t = 0
          · simp [natRatio, ht]
          · simp only [natRatio, ht, if_false]
            exact div_le_div_of_nonneg_right
              (by exact_mod_cast P.deadlineInverse_le_prefixTau t)
              (Nat.cast_nonneg t)
        exact hNat
      · exact P.prefixRate_nonneg t
  · exact P.prefixTau_rate_ratio_tendsto_zero

/-- Deterministic rate estimates underlying Appendix-D Lemmas 5--8.

Starting from the source's natural budget `floor(t H_el(t))`, the
construction supplies a superlinear prefix deadline and a vanishing prefix
rate.  The new rate is eventually no larger than the original rate, while
the generalized inverse of the prefix deadline is little-o of its budget.
This theorem does not yet build the natural budget from a raw real-valued
`H_el`, replace `prefixRate` by a nonincreasing tail envelope, or prove
discrete convexity of the composed `prefixDeadline`.  Thus it proves the
deterministic asymptotic core rather than packaging a literal Definition-2
feasible profile; those are the remaining analytic steps before the
randomized reduction. -/
theorem appendixD_deterministic_profile_estimates
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0)) :
    Tendsto
        (fun i : ℕ => (P.prefixDeadline i : ℝ) / i)
        atTop atTop ∧
      Tendsto P.prefixRate atTop (nhds 0) ∧
      (∀ᶠ t : ℕ in atTop,
        P.prefixRate t ≤ natRatio P.budget t) ∧
      Tendsto
        (fun t =>
          natRatio
              (P.prefixDeadline.inverse
                P.prefixDeadline_isUnbounded) t /
            P.prefixRate t)
        atTop (nhds 0) ∧
      Tendsto
        (deadlineExceptionRatio P.deadline P.prefixDeadline)
        atTop (nhds 0) := by
  exact ⟨P.prefixDeadline_superlinear,
    P.prefixRate_tendsto_zero hvanishing,
    P.prefixRate_eventually_le_original,
    P.prefixInverse_rate_ratio_tendsto_zero,
    P.prefixDeadline_exceptionRatio_tendsto_zero⟩

end NaturalFeasibleProfile

end GenLimit.TimeSensitive
