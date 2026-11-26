import Mathlib.Analysis.Complex.ExponentialBounds
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredDiscrepancy

/-! Static splitting of a point set on the geometric volume filter in
Theorem 5.5. Both color classes meet the required density threshold on
the same rectangles. Obtaining such coverage online also requires an
adversarial response strategy. -/
namespace GenLimit.KleinbergWei.Banach
open TierGeometry Real Finset Filter
open scoped Classical
noncomputable section

/-- Ordinary geometric volume on integer-endpoint rectangles. -/
def geometricVolume {d} (l u : Lattice d) := ∏ i, (u i-l i).toNat

private theorem span_le_volume {d} (l u : Lattice d) (positive : ∀ i, l i < u i) :
    span l u ≤ geometricVolume l u + 1 := by
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro i _
  exact Finset.single_le_prod' (f := fun j => (u j-l j).toNat)
    (fun j _ => by change 1 ≤ (u j-l j).toNat; have := positive j; omega) (Finset.mem_univ i)

private theorem sign_counts {V : Type*} (T : Finset V) (c : V → Bool) :
    (∑ v ∈ T, RandomSigns.sign (c v)) = 2*((T.filter (fun v => c v = true)).card:ℝ)-T.card ∧
    (∑ v ∈ T, RandomSigns.sign (c v)) = T.card-2*((T.filter (fun v => c v = false)).card:ℝ) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert v T hv ih =>
    cases h : c v <;>
      simp [Finset.sum_insert,hv,Finset.filter_insert,h,RandomSigns.sign] at ih ⊢ <;>
      constructor <;> linarith [ih.1,ih.2]

/-- For all sufficiently large geometric volumes and filtered target
counts, both colors occupy at least one-half minus ε of the target.
The thresholds work for all point sets. -/
theorem static_filtered_split {d : ℕ} (hd : 0 < d) {ε : ℝ} (he : 0 < ε)
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) :
    ∃ N : ℕ, ∀ P : Set (Lattice d), ∃ c : Lattice d → Bool, ∀ l u,
      (∀ i, l i < u i) → N ≤ geometricVolume l u →
      let V := geometricVolume l u
      let T := Rectangles.box P l u
      (N:ℝ)*f V*log V ≤ T.card →
      ∀ b : Bool, (1/2-ε)*(T.card:ℝ) ≤ (T.filter (fun v => c v=b)).card := by
  obtain ⟨C,nonneg,all⟩ := filtered_discrepancy hd ε he
  obtain ⟨n,nb⟩ := exists_nat_gt (3*C/ε)
  obtain ⟨t,after⟩ := eventually_atTop.mp ((tendsto_atTop.mp grows) 1)
  let N := max 4 (max n t)
  have nN : n ≤ N := (le_max_left ..).trans (le_max_right ..)
  have tN : t ≤ N := (le_max_right ..).trans (le_max_right ..)
  have cn : 3*C ≤ ε*N := by
    have h := (div_lt_iff₀ he).mp nb
    have le : (n:ℝ) ≤ N := by exact_mod_cast nN
    nlinarith [mul_le_mul_of_nonneg_left le he.le]
  refine ⟨N,fun P => ?_⟩
  obtain ⟨c,balanced⟩ := all P
  refine ⟨c,fun l u widths large => ?_⟩
  let V := geometricVolume l u
  let T := Rectangles.box P l u
  change (N:ℝ)*f V*log V ≤ T.card → ∀ b : Bool, (1/2-ε)*(T.card:ℝ) ≤ (T.filter (fun v => c v=b)).card
  intro enough b
  change (N:ℝ)*f V*log V ≤ T.card at enough
  change N ≤ V at large
  have four : 4 ≤ V := (le_max_left ..).trans large
  have ln : 1 ≤ log V := by
    apply (Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < V by omega))).2
    have v4 : (4:ℝ) ≤ V := by exact_mod_cast four
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have bound : (span l u : ℝ) ≤ 2*V := by
    have h := span_le_volume l u widths
    change _ ≤ V+1 at h
    exact_mod_cast (show span l u ≤ 2*V by omega)
  have logspan := Real.log_le_log (by exact_mod_cast (show 0 < span l u from Nat.succ_pos _)) bound
  rw [Real.log_mul (by norm_num) (by positivity : (V:ℝ) ≠ 0)] at logspan
  have logtwo : log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have weight : C*(1+log (span l u)) ≤ ε*T.card := by
    have sf := mul_le_mul_of_nonneg_left (after V (tN.trans large)) (Nat.cast_nonneg (α := ℝ) N)
    have size : (N:ℝ)*log V ≤ T.card :=
      (mul_le_mul_of_nonneg_right (by simpa using sf : (N:ℝ) ≤ N*f V) (by linarith)).trans enough
    calc
      _ ≤ C*(3*log V) := mul_le_mul_of_nonneg_left (by linarith) nonneg
      _ ≤ ε*(N*log V) := by nlinarith only [mul_le_mul_of_nonneg_right cn (show 0 ≤ log V by linarith)]
      _ ≤ _ := mul_le_mul_of_nonneg_left size he.le
  have hit := balanced l u
  change |∑ v ∈ T, RandomSigns.sign (c v)| ≤ ε*T.card+C*(1+log (span l u)) at hit
  obtain ⟨lo,hi⟩ := abs_le.mp hit
  obtain ⟨yes,no⟩ := sign_counts T c
  change _ ≤ ((T.filter (fun v => c v=b)).card : ℝ)
  cases b <;> linarith

end
end GenLimit.KleinbergWei.Banach
