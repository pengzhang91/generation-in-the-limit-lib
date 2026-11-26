import GenLimit.Paper25_PrivateGenerationAndIdentification.EpochGeneration
import GenLimit.Paper25_PrivateGenerationAndIdentification.IdentificationBarrier
import GenLimit.Paper24_PriceOfPrivacy.PrivateSelection
import Mathlib.NumberTheory.ZetaValues

/-! Algorithm 2 and Theorem C.5. At the end of the first 2^s observations,
the public candidate window includes at most s indices and its pairwise
overlaps are at most half the sample. The first output is the first index. -/
namespace GenLimit.PrivateLimit.OnlineIdentification

open Set Filter DiscreteIID PriceOfPrivacy Privacy MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- The largest eligible zero-based index, at the paper's epoch s = j+1. -/
def eligible (C : LanguageFamily) (j m : ℕ) : Prop :=
  ∀ i ≤ m, ∀ k ≤ m, i ≠ k → (C i ∩ C k).Finite ∧ (C i ∩ C k).ncard ≤ 2^j

def last (C : LanguageFamily) (j : ℕ) := Nat.findGreatest (eligible C j) j

theorem eligible_last (C : LanguageFamily) (j : ℕ) : eligible C j (last C j) :=
  Nat.findGreatest_spec (P := eligible C j) (Nat.zero_le j) (by
    intro i hi k hk ne; omega)

theorem eventually_in_window (C : LanguageFamily)
    (overlap : ∀ i k, i ≠ k → (C i ∩ C k).Finite) (z : ℕ) :
    ∀ᶠ j : ℕ in atTop, z ≤ last C j := by
  let I := Finset.range (z+1)
  let bound := I.sup fun i => I.sup fun k => (C i ∩ C k).ncard
  filter_upwards [eventually_ge_atTop (max z bound)] with j hj
  apply Nat.le_findGreatest ((le_max_left ..).trans hj)
  intro i hi k hk ne
  have ik : (C i ∩ C k).ncard ≤ bound :=
    (Finset.le_sup (f := fun k => (C i ∩ C k).ncard)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans
      (Finset.le_sup (f := fun i => I.sup fun k => (C i ∩ C k).ncard)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  exact ⟨overlap i k ne,ik.trans (((le_max_right ..).trans hj).trans Nat.lt_two_pow_self.le)⟩

/-- Matches minus sample length equals the negative inconsistency count. -/
def score (C : LanguageFamily) {w : ℕ} (xs : List ℕ) (i : Fin w) : ℝ :=
  ((xs.filter fun x => decide (x ∈ C i)).length:ℝ) - xs.length

def cost (ε : ℝ) (j : ℕ) : ℝ := (6*ε/Real.pi^2)*(1/(j:ℝ)^2)

private theorem cost_pos {ε : ℝ} (he : 0 < ε) {j : ℕ} (hj : 0 < j) : 0 < cost ε j := by
  unfold cost; positivity

private theorem total_cost {ε : ℝ} (he : 0 < ε) (I : Finset ℕ) : ∑ j ∈ I, cost ε j ≤ ε := by
  have h := sum_le_hasSum I (fun _ _ => by positivity) hasSum_zeta_two
  simp only [cost,←Finset.mul_sum]
  calc
    _ ≤ (6*ε/Real.pi^2)*(Real.pi^2/6) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = ε := by field_simp [Real.pi_ne_zero]

def selection (C : LanguageFamily) (ε : ℝ) (j : ℕ) (xs : List ℕ) : PMF ℕ :=
  Selection.pureLaw (w := last C j+1) (score C) 1 (cost ε (j+1)) xs

private theorem selection_private (C : LanguageFamily) {ε : ℝ} (he : 0 < ε) (j n : ℕ) :
    PrivateAt (cost ε (j+1)) 0 n (selection C ε j) := by
  apply Selection.pure_private (by norm_num) (cost_pos he (Nat.succ_pos _))
  intro pre x y post len i
  by_cases hx : x ∈ C i <;> by_cases hy : y ∈ C i <;>
    simp [score,hx,hy]

private def finish (j : ℕ) := 2^j-1

private def sample (C : LanguageFamily) (ε : ℝ) (s : ℕ → ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | j+1 => selection C ε j (Epoch.observations s (2^(j+1)))

private theorem depends (C : LanguageFamily) (ε : ℝ) (u v : ℕ → ℕ) (j : ℕ)
    (agree : ∀ i ≤ finish j, u i = v i) : sample C ε u j = sample C ε v j := by
  cases j with
  | zero => rfl
  | succ j =>
    apply congrArg (selection C ε j)
    apply List.map_congr_left
    intro i hi
    apply agree
    have h := List.mem_range.mp hi
    unfold finish; omega

def identifier (C : LanguageFamily) (ε : ℝ) : ContinualRelease ℕ ℕ :=
  Epoch.release finish rfl (sample C ε) (depends C ε)

theorem identifier_private (C : LanguageFamily) {ε : ℝ} (he : 0 < ε) :
    DifferentiallyPrivate ε 0 (identifier C ε).law := by
  apply Epoch.release_private
  apply private_independent_releases
  intro u v adj
  refine ⟨cost ε,total_cost he,?_⟩
  rintro (_ | j) y
  · rw [show cost ε 0 = 0 by simp [cost],Real.exp_zero,ENNReal.ofReal_one,one_mul]
    exact le_rfl
  · exact Epoch.private_prefix (cost_pos he (Nat.succ_pos _)).le (selection_private C he _ _) adj y

private theorem selection_error (C : LanguageFamily) {ε : ℝ} (he : 0 < ε) (j z : ℕ)
    (hz : z ≤ last C j) (s : ℕ → ℕ) (inj : Function.Injective s) (inK : range s ⊆ C z) :
    probability (sample C ε s (j+1)) {i | i ≠ z} ≤
      (j+1:ℝ)*Real.exp (-(cost ε (j+1)/2)*(2:ℝ)^j) := by
  let xs := Epoch.observations s (2^(j+1))
  let target : Fin (last C j+1) := ⟨z,Nat.lt_succ_of_le hz⟩
  have mem_z (x : ℕ) (hx : x ∈ xs) : x ∈ C z := by
    obtain ⟨i,_,rfl⟩ := Epoch.mem_observations.mp hx
    exact inK (mem_range_self _)
  have all : (xs.filter fun x => decide (x ∈ C z)) = xs :=
    List.filter_eq_self.mpr (by simpa using mem_z)
  have len : xs.length = 2^(j+1) := by simp [xs,Epoch.observations]
  have gap (i : Fin (last C j+1)) (ne : i.val ∈ {i | i ≠ z}) :
      (2:ℝ)^j ≤ score C xs target - score C xs i := by
    let hits := xs.filter fun x => decide (x ∈ C i)
    obtain ⟨fin,upper⟩ := eligible_last C j z hz i (Nat.le_of_lt_succ i.isLt) (Ne.symm ne)
    have sub : (↑hits.toFinset : Set ℕ) ⊆ C z ∩ C i := by
      intro x hx
      obtain ⟨hx,hi⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
      exact ⟨mem_z _ hx,of_decide_eq_true hi⟩
    have small := (Set.ncard_le_ncard sub fin).trans upper
    have nd : hits.Nodup := (List.nodup_range.map inj).filter _
    rw [Set.ncard_coe_finset,List.toFinset_card_of_nodup nd] at small
    have bound : (hits.length:ℝ) ≤ (2:ℝ)^j := by exact_mod_cast small
    change _ ≤ ((((xs.filter fun x => decide (x ∈ C z)).length:ℝ)-xs.length) -
      ((hits.length:ℝ)-xs.length))
    rw [all,len,Nat.cast_pow,Nat.cast_ofNat,pow_succ]; linarith
  have tail := Selection.pure_gap (score := score C) (by norm_num : (0:ℝ)<1)
    (cost_pos he (Nat.succ_pos j)) xs {i | i ≠ z} target gap
  apply tail.trans
  simp only [mul_one,Nat.cast_add,Nat.cast_one]
  gcongr
  exact Nat.findGreatest_le j

private theorem eventually_large_exponent {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, (j:ℝ) ≤ (cost ε (j+1)/2)*(2:ℝ)^j := by
  let c := 6*ε/Real.pi^2
  have hc : 0 < c := by dsimp [c]; positivity
  have lim := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1:ℝ)<2)
  filter_upwards [lim.eventually_lt_const (by positivity : 0 < c/8),eventually_ge_atTop 1] with j hj large
  have h := (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^j)).mp hj
  have jr : (1:ℝ) ≤ j := by exact_mod_cast large
  have sq := pow_le_pow_left₀ (by positivity : 0 ≤ (j:ℝ)+1)
    (show (j:ℝ)+1 ≤ 2*j by linarith) 2
  change (j:ℝ) ≤ (c*(1/((j+1:ℕ):ℝ)^2)/2)*(2:ℝ)^j
  push_cast
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left sq (show (0:ℝ) ≤ j by positivity)]

theorem identifier_correct (C : LanguageFamily) {ε : ℝ} (he : 0 < ε)
    (overlap : ∀ i k, i ≠ k → (C i ∩ C k).Finite) : IdentifiesOnline (identifier C ε) C := by
  intro z s inj eq
  let μ := Epoch.productLaw (sample C ε) s
  let B (j : ℕ) : Set (ℕ → ℕ) := (Function.eval (j+1)) ⁻¹' {i | i ≠ z}
  have bounds : ∀ᶠ j : ℕ in atTop, μ.real (B j) ≤ (j+1:ℝ)*(Real.exp (-1))^j := by
    filter_upwards [eventually_in_window C overlap z,eventually_large_exponent he] with j active large
    have hm : MeasurableSet {i : ℕ | i ≠ z} := .of_discrete
    have ev := measurePreserving_eval_infinitePi (fun j => (sample C ε s j).toMeasure) (j+1)
    change ((Measure.infinitePi (fun t => (sample C ε s t).toMeasure))
      ((Function.eval (j+1)) ⁻¹' {i : ℕ | i ≠ z})).toReal ≤ _
    rw [ev.measure_preimage hm.nullMeasurableSet,PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
    apply (selection_error C he j z active s inj eq.subset).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Real.exp_nat_mul,Real.exp_le_exp]
    linarith
  have avoid := Voting.eventually_avoid μ B (Voting.summable_linear_geometric
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num))) bounds
  have stable : ∀ᵐ y ∂μ, ∀ᶠ j in atTop, y j = z := by
    filter_upwards [avoid] with y hy
    obtain ⟨n,hn⟩ := eventually_atTop.mp hy
    refine eventually_atTop.mpr ⟨n+1,?_⟩
    rintro (_ | j) hj
    · omega
    · exact Classical.not_not.mp (hn j (by omega))
  filter_upwards [Epoch.release_stabilizes finish rfl _ (depends C ε) s z stable] with y hy
  exact ⟨z,rfl,hy⟩

end
end GenLimit.PrivateLimit.OnlineIdentification
