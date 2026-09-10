import GenLimit.Paper30_TimeSensitiveLanguageGeneration.DensityReduction
import Mathlib.Data.Nat.Find
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Appendix-D countable deadline diagonal

This file formalizes the deterministic countable-domination construction in
Appendix-D Lemmas 6--7 of Ganju--McVoy--Dughmi--Teng,
arXiv:2605.11302v2.

The paper phrases `f(i) = o(i)` for natural-valued monotone functions.  The
predicate `NatSublinear` below records the equivalent integer-scaled form:
for every positive integer `q`, eventually `q * f(i) ≤ i`.  This avoids
silently changing codomains during the discrete diagonal construction.

The resulting diagonal is an actual function, not an assumed asymptotic
certificate.  Its active level is the largest cutoff stage reached by the
current index, and it takes the maximum of that level and the first finitely
many source functions.  The final theorems specialize the construction to a
slowed prefix deadline `D (s i)`, prove that its early-deadline exception
ratio tends to zero, and invoke the already checked Appendix-D density
comparison.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- Discrete natural-valued form of `f(i) = o(i)`.

For every positive integer scale `q`, the inequality `q * f(i) ≤ i` holds
from some point onward. -/
def NatSublinear (f : ℕ → ℕ) : Prop :=
  ∀ q, 0 < q → ∃ N, ∀ i, N ≤ i → q * f i ≤ i

/-- A chosen threshold for the `(q+1)`-scaled sublinearity estimate of the
`m`-th function. -/
noncomputable def sublinearThreshold
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (m q : ℕ) : ℕ :=
  Classical.choose (hf m (q + 1) (Nat.succ_pos q))

theorem sublinearThreshold_spec
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (m q i : ℕ)
    (hi : sublinearThreshold f hf m q ≤ i) :
    (q + 1) * f m i ≤ i :=
  Classical.choose_spec (hf m (q + 1) (Nat.succ_pos q)) i hi

/-- Increasing cutoffs used by the countable diagonal.

At stage `k+1` the cutoff is beyond `(k+1)^2`, beyond the preceding cutoff,
and beyond a simultaneous `(k+1)`-scaled sublinearity threshold for the
first `k+2` functions.  Including index `k+1` is harmless and makes the
zero-based statement slightly stronger than the paper's one-based version. -/
noncomputable def diagonalCutoff
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m)) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      max (diagonalCutoff f hf k + 1)
        (max ((k + 1) * (k + 1))
          ((Finset.range (k + 2)).sup
            (fun m => sublinearThreshold f hf m k)))

theorem diagonalCutoff_strictMono
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m)) :
    StrictMono (diagonalCutoff f hf) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [diagonalCutoff]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem diagonalCutoff_mono
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m)) :
    Monotone (diagonalCutoff f hf) :=
  (diagonalCutoff_strictMono f hf).monotone

theorem diagonalCutoff_square_le
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    {k : ℕ} (hk : 0 < k) :
    k * k ≤ diagonalCutoff f hf k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [diagonalCutoff]
  exact le_max_of_le_right (le_max_left _ _)

theorem sublinearThreshold_le_diagonalCutoff
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    {m k : ℕ} (hm : m ≤ k) (hk : 0 < k) :
    sublinearThreshold f hf m (k - 1) ≤
      diagonalCutoff f hf k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hmRange : m ∈ Finset.range (j + 2) := by
    simp only [Finset.mem_range]
    omega
  change sublinearThreshold f hf m j ≤
    diagonalCutoff f hf (j + 1)
  rw [diagonalCutoff]
  exact le_max_of_le_right <|
    le_max_of_le_right <|
      Finset.le_sup (f := fun n => sublinearThreshold f hf n j) hmRange

/-- Largest diagonal stage whose cutoff has been reached by index `i`. -/
noncomputable def diagonalLevel
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (i : ℕ) : ℕ :=
  Nat.findGreatest (fun k => diagonalCutoff f hf k ≤ i) i

theorem diagonalLevel_le
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (i : ℕ) :
    diagonalLevel f hf i ≤ i :=
  Nat.findGreatest_le i

theorem diagonalLevel_mono
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m)) :
    Monotone (diagonalLevel f hf) := by
  intro i j hij
  unfold diagonalLevel
  exact Nat.findGreatest_mono
    (fun _ hk => hk.trans hij) hij

theorem diagonalCutoff_level_le
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (i : ℕ) :
    diagonalCutoff f hf (diagonalLevel f hf i) ≤ i := by
  unfold diagonalLevel
  exact Nat.findGreatest_spec
    (P := fun k => diagonalCutoff f hf k ≤ i)
    (m := 0) (n := i)
    (Nat.zero_le i) (by simp [diagonalCutoff])

theorem le_diagonalLevel_of_cutoff_le
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    {k i : ℕ}
    (hki : k ≤ i)
    (hcutoff : diagonalCutoff f hf k ≤ i) :
    k ≤ diagonalLevel f hf i :=
  Nat.le_findGreatest hki hcutoff

theorem diagonalLevel_eventually_ge
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (k : ℕ) :
    ∀ᶠ i : ℕ in atTop, k ≤ diagonalLevel f hf i := by
  filter_upwards
    [eventually_ge_atTop (max k (diagonalCutoff f hf k))] with i hi
  exact le_diagonalLevel_of_cutoff_le f hf
    (le_trans (le_max_left _ _) hi)
    (le_trans (le_max_right _ _) hi)

/-- The paper's countable diagonal: at index `i`, take the maximum of the
active stage and the first `level+1` source functions. -/
noncomputable def countableDiagonal
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (i : ℕ) : ℕ :=
  max (diagonalLevel f hf i)
    ((Finset.range (diagonalLevel f hf i + 1)).sup (fun m => f m i))

theorem diagonalLevel_le_countableDiagonal
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (i : ℕ) :
    diagonalLevel f hf i ≤ countableDiagonal f hf i :=
  le_max_left _ _

theorem family_le_countableDiagonal
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    {m i : ℕ}
    (hm : m ≤ diagonalLevel f hf i) :
    f m i ≤ countableDiagonal f hf i := by
  apply le_max_of_le_right
  exact Finset.le_sup
    (s := Finset.range (diagonalLevel f hf i + 1))
    (f := fun n => f n i) (b := m)
    (by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hm)

theorem countableDiagonal_eventually_dominates
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (m : ℕ) :
    ∀ᶠ i : ℕ in atTop, f m i ≤ countableDiagonal f hf i := by
  filter_upwards [diagonalLevel_eventually_ge f hf m] with i hi
  exact family_le_countableDiagonal f hf hi

theorem diagonalLevel_mul_family_le
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    {m i : ℕ}
    (hm : m ≤ diagonalLevel f hf i) :
    diagonalLevel f hf i * f m i ≤ i := by
  by_cases hlevel : diagonalLevel f hf i = 0
  · simp [hlevel]
  · have hthreshold :
        sublinearThreshold f hf m (diagonalLevel f hf i - 1) ≤ i :=
      (sublinearThreshold_le_diagonalCutoff f hf hm
          (Nat.pos_of_ne_zero hlevel)).trans
        (diagonalCutoff_level_le f hf i)
    have hbound :=
      sublinearThreshold_spec f hf m
        (diagonalLevel f hf i - 1) i hthreshold
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hlevel)] using
      hbound

theorem diagonalLevel_mul_familySup_le
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (i : ℕ) :
    diagonalLevel f hf i *
        ((Finset.range (diagonalLevel f hf i + 1)).sup
          (fun m => f m i)) ≤ i := by
  apply Finset.sup_induction
    (s := Finset.range (diagonalLevel f hf i + 1))
    (f := fun m => f m i)
    (p := fun x => diagonalLevel f hf i * x ≤ i)
  · simp
  · intro a ha b hb
    rw [mul_max]
    exact max_le ha hb
  · intro m hm
    exact diagonalLevel_mul_family_le f hf
      (Nat.le_of_lt_succ (Finset.mem_range.mp hm))

theorem diagonalLevel_mul_self_le
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (i : ℕ) :
    diagonalLevel f hf i * diagonalLevel f hf i ≤ i := by
  by_cases hlevel : diagonalLevel f hf i = 0
  · simp [hlevel]
  · exact
      (diagonalCutoff_square_le f hf (Nat.pos_of_ne_zero hlevel)).trans
        (diagonalCutoff_level_le f hf i)

theorem diagonalLevel_mul_countableDiagonal_le
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (i : ℕ) :
    diagonalLevel f hf i * countableDiagonal f hf i ≤ i := by
  rw [countableDiagonal, mul_max]
  exact max_le
    (diagonalLevel_mul_self_le f hf i)
    (diagonalLevel_mul_familySup_le f hf i)

theorem countableDiagonal_sublinear
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m)) :
    NatSublinear (countableDiagonal f hf) := by
  intro q hq
  refine ⟨max q (diagonalCutoff f hf q), ?_⟩
  intro i hi
  have hqLevel : q ≤ diagonalLevel f hf i :=
    le_diagonalLevel_of_cutoff_le f hf
      (le_trans (le_max_left _ _) hi)
      (le_trans (le_max_right _ _) hi)
  exact
    (Nat.mul_le_mul_right (countableDiagonal f hf i) hqLevel).trans
      (diagonalLevel_mul_countableDiagonal_le f hf i)

theorem countableDiagonal_mono
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (hmono : ∀ m, Monotone (f m)) :
    Monotone (countableDiagonal f hf) := by
  intro i j hij
  have hlevel :
      diagonalLevel f hf i ≤ diagonalLevel f hf j :=
    diagonalLevel_mono f hf hij
  apply max_le
  · exact hlevel.trans (le_max_left _ _)
  · apply le_max_of_le_right
    apply Finset.sup_le
    intro m hm
    apply le_trans (hmono m hij)
    have hm' : m < diagonalLevel f hf i + 1 :=
      Finset.mem_range.mp hm
    exact Finset.le_sup
      (s := Finset.range (diagonalLevel f hf j + 1))
      (f := fun n => f n j) (b := m)
      (Finset.mem_range.mpr
        (lt_of_lt_of_le hm' (Nat.succ_le_succ hlevel)))

theorem countableDiagonal_tendsto_atTop
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m)) :
    Tendsto (countableDiagonal f hf) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [diagonalLevel_eventually_ge f hf b] with i hi
  exact hi.trans (diagonalLevel_le_countableDiagonal f hf i)

/-- Appendix-D's countable diagonal domination lemma, assembled in the
same existential form as the source.

The selected `s` is monotone, diverges, is sublinear, and eventually
dominates each member of the countable family. -/
theorem countable_diagonal_domination
    (f : ℕ → ℕ → ℕ)
    (hmono : ∀ m, Monotone (f m))
    (hf : ∀ m, NatSublinear (f m)) :
    ∃ s : ℕ → ℕ,
      Monotone s ∧
      Tendsto s atTop atTop ∧
      NatSublinear s ∧
      ∀ m, ∀ᶠ i : ℕ in atTop, f m i ≤ s i := by
  exact ⟨countableDiagonal f hf,
    countableDiagonal_mono f hf hmono,
    countableDiagonal_tendsto_atTop f hf,
    countableDiagonal_sublinear f hf,
    countableDiagonal_eventually_dominates f hf⟩

/-! ## Slowed deadline and density transfer -/

/-- Prefix deadline obtained by slowing an element-wise deadline along the
countable diagonal. -/
noncomputable def slowedDeadline
    (D : Deadline)
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (hmono : ∀ m, Monotone (f m)) : Deadline where
  toFun := fun i => D (countableDiagonal f hf i)
  monotone' :=
    D.monotone'.comp (countableDiagonal_mono f hf hmono)

/-- Slowing an unbounded deadline along the diverging diagonal preserves
unboundedness, so the generalized inverse of the new deadline is defined. -/
theorem slowedDeadline_isUnbounded
    (D : Deadline)
    (hD : D.IsUnbounded)
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (hmono : ∀ m, Monotone (f m)) :
    (slowedDeadline D f hf hmono).IsUnbounded := by
  intro t
  obtain ⟨n, hn⟩ := hD t
  have heventually :
      ∀ᶠ i : ℕ in atTop, n ≤ countableDiagonal f hf i :=
    (tendsto_atTop.1 (countableDiagonal_tendsto_atTop f hf)) n
  obtain ⟨i, hi⟩ := heventually.exists
  exact ⟨i, hn.trans (by
    simpa [slowedDeadline] using D.monotone' hi)⟩

/-- The source's superlinearity step in Lemma 7.

If one member `f m` of the diagonal family already makes
`D (f m i) / i` diverge, then the slowed deadline `D (s i)` is
superlinear because the diagonal eventually dominates that member. -/
theorem slowedDeadline_superlinear_of_member
    (D : Deadline)
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (hmono : ∀ m, Monotone (f m))
    (m : ℕ)
    (hsuper :
      Tendsto (fun i : ℕ => (D (f m i) : ℝ) / i) atTop atTop) :
    Tendsto
      (fun i : ℕ => (slowedDeadline D f hf hmono i : ℝ) / i)
      atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards
    [(tendsto_atTop.1 hsuper b),
      countableDiagonal_eventually_dominates f hf m] with i hi hdom
  have hdeadline :
      D (f m i) ≤ slowedDeadline D f hf hmono i := by
    simpa [slowedDeadline] using D.monotone' hdom
  exact hi.trans
    (div_le_div_of_nonneg_right
      (by exact_mod_cast hdeadline)
      (Nat.cast_nonneg i))

theorem deadlineExceptionCount_slowed_le
    (D : Deadline)
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (hmono : ∀ m, Monotone (f m))
    (i : ℕ) :
    deadlineExceptionCount D (slowedDeadline D f hf hmono) i ≤
      countableDiagonal f hf i := by
  unfold deadlineExceptionCount
  have hsubset :
      (Finset.range i).filter
          (fun j => D j < slowedDeadline D f hf hmono i) ⊆
        Finset.range (countableDiagonal f hf i) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    apply Finset.mem_range.mpr
    by_contra hnot
    have hsj : countableDiagonal f hf i ≤ j :=
      Nat.le_of_not_gt hnot
    have hdeadline :
        D (countableDiagonal f hf i) ≤ D j :=
      D.monotone' hsj
    have hjEarly :
        D j < D (countableDiagonal f hf i) := by
      simpa [slowedDeadline] using hj.2
    exact (not_lt_of_ge hdeadline) hjEarly
  calc
    ((Finset.range i).filter
        (fun j => D j < slowedDeadline D f hf hmono i)).card
        ≤ (Finset.range (countableDiagonal f hf i)).card :=
      Finset.card_le_card hsubset
    _ = countableDiagonal f hf i := Finset.card_range _

/-- Natural ratio associated with a natural-valued sequence, totalized at
the empty prefix. -/
noncomputable def natRatio (g : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (g i : ℝ) / i

theorem natRatio_nonneg
    (g : ℕ → ℕ) (i : ℕ) :
    0 ≤ natRatio g i := by
  by_cases hi : i = 0
  · simp [natRatio, hi]
  · simp only [natRatio, hi, if_false]
    positivity

theorem natRatio_tendsto_zero_of_sublinear
    (g : ℕ → ℕ)
    (hg : NatSublinear g) :
    Tendsto (natRatio g) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hqε⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hg (q + 1) (Nat.succ_pos q)
  refine ⟨max N 1, ?_⟩
  intro i hi
  have hiN : N ≤ i := (le_max_left _ _).trans hi
  have hiPos : 0 < i :=
    lt_of_lt_of_le
      (Nat.zero_lt_one.trans_le (le_max_right N 1)) hi
  have hscaled : (q + 1) * g i ≤ i := hN i hiN
  have hqPosReal : (0 : ℝ) < q + 1 := by positivity
  have hiPosReal : (0 : ℝ) < i := by exact_mod_cast hiPos
  have hratio :
      (g i : ℝ) / i ≤ 1 / (q + 1 : ℝ) := by
    rw [div_le_div_iff₀ hiPosReal hqPosReal]
    have hscaledReal :
        (((q + 1 : ℕ) : ℝ) * (g i : ℝ)) ≤ (i : ℝ) := by
      exact_mod_cast hscaled
    simpa [mul_comm] using hscaledReal
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (natRatio_nonneg g i)]
  rw [natRatio, if_neg (Nat.ne_of_gt hiPos)]
  exact hratio.trans_lt hqε

theorem deadlineExceptionRatio_slowed_le_natRatio
    (D : Deadline)
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (hmono : ∀ m, Monotone (f m))
    (i : ℕ) :
    deadlineExceptionRatio D (slowedDeadline D f hf hmono) i ≤
      natRatio (countableDiagonal f hf) i := by
  by_cases hi : i = 0
  · simp [deadlineExceptionRatio, natRatio, hi]
  · simp only [deadlineExceptionRatio, natRatio, hi, if_false]
    have hcount :
        (deadlineExceptionCount D
            (slowedDeadline D f hf hmono) i : ℝ) ≤
          countableDiagonal f hf i := by
      exact_mod_cast
        (deadlineExceptionCount_slowed_le D f hf hmono i)
    exact div_le_div_of_nonneg_right
      hcount
      (by positivity)

theorem deadlineExceptionRatio_slowed_tendsto_zero
    (D : Deadline)
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (hmono : ∀ m, Monotone (f m)) :
    Tendsto
      (deadlineExceptionRatio D (slowedDeadline D f hf hmono))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun i =>
      deadlineExceptionRatio_nonneg
        D (slowedDeadline D f hf hmono) i
  · exact Filter.Eventually.of_forall fun i =>
      deadlineExceptionRatio_slowed_le_natRatio
        D f hf hmono i
  · exact natRatio_tendsto_zero_of_sublinear
      (countableDiagonal f hf)
      (countableDiagonal_sublinear f hf)

/-- Density-only consequence of Appendix-D Lemmas 5--7 under an externally
supplied countable monotone sublinear family.

For the prefix deadline obtained from the actual countable diagonal, the
prefix-wise lower density is bounded by the original element-wise lower
density.  Thus the earlier reduction no longer assumes the vanishing
exception ratio as an external hypothesis. -/
theorem lowerPrefixWiseDensity_slowed_le_lowerTimelyDensity
    (S R : ℕ → α)
    (hR : Function.Injective R)
    (D : Deadline)
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ m, NatSublinear (f m))
    (hmono : ∀ m, Monotone (f m)) :
    lowerPrefixWiseDensity S R (slowedDeadline D f hf hmono) ≤
      lowerTimelyDensity S R D := by
  exact lowerPrefixWiseDensity_le_lowerTimelyDensity_of_exceptionRatio
    S R hR D (slowedDeadline D f hf hmono)
    (deadlineExceptionRatio_slowed_tendsto_zero D f hf hmono)

end GenLimit.TimeSensitive
