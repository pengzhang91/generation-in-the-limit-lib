import GenLimit.Paper25_PrivateGenerationAndIdentification.EpochGeneration

/-! Theorem C.1. Doubling the excess over the closure dimension while
using telescoping privacy budgets gives a uniform tail for the last
incorrect output. Times in the statement count observations from one. -/
namespace GenLimit.PrivateLimit.Epoch

open Set MeasureTheory Privacy
open scoped Classical
noncomputable section

def finiteFinish (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => d+2^(r+1)-1

def finiteScheme {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ} (bd : SubcollectionClosureBound (range C) d) : Scheme where
  count _ := k
  family _ := C
  dim _ := d
  bound _ := bd
  finish := finiteFinish d
  initial := rfl

def strength (ε : ℝ) (k r : ℕ) := ε*(2:ℝ)^r/(2*k*((r:ℝ)+1)*(r+2))

private theorem error_finite {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ} (bd : SubcollectionClosureBound (range C) d)
    (ε : ℝ) {r : ℕ} (hr : 0 < r) :
    errorAt (finiteScheme C bd) ε r = 5*Real.exp (-strength ε k r) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have e : d+2^(j+1)-1+1 = d+2^(j+1) := by have := Nat.two_pow_pos (j+1); omega
  simp only [errorAt,finiteScheme,finiteFinish,e,FiniteCore.errorTerm,strength,cost]
  simp only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,add_sub_cancel_left]
  congr 2
  simp only [div_eq_mul_inv,mul_inv_rev]; ring

private theorem growth {ε : ℝ} (he : 0 < ε) {k : ℕ} (hk : 0 < k) {r : ℕ} (hr : 5 ≤ r) :
    (3/2:ℝ)*strength ε k r ≤ strength ε k (r+1) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hr' : (5:ℝ) ≤ r := by exact_mod_cast hr
  unfold strength
  rw [pow_succ]
  push_cast
  field_simp
  nlinarith only [show 0 ≤ (r+2:ℝ) * (r-5:ℝ) by
    exact mul_nonneg (by positivity) (by linarith)]

private theorem tail_growth {ε : ℝ} (he : 0 < ε) {k r : ℕ} (hk : 0 < k) (hr : 5 ≤ r) (l : ℕ) :
    strength ε k r*(1+(l:ℝ)/2) ≤ strength ε k (r+l) := by
  have nonneg : 0 ≤ strength ε k r := by unfold strength; positivity
  induction l with
  | zero => simp
  | succ l ih =>
    have h := growth he hk (r := r+l) (by omega)
    simp only [Nat.cast_succ,← Nat.add_assoc]
    nlinarith [mul_nonneg nonneg (show (0:ℝ) ≤ l by positivity)]

private theorem epoch_rate {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ} (bd : SubcollectionClosureBound (range C) d)
    {ε : ℝ} (he : 0 < ε) (s : ℕ → ℕ) (nd : Function.Injective s) (z : Fin k) (inK : range s ⊆ C z)
    {r t : ℕ} (hr : 5 ≤ r) (ready : max r (finiteFinish d r) ≤ t) :
    ((generator (finiteScheme C bd) ε).law s).real (failsAfter (C z) s t) ≤
      10*Real.exp (-strength ε k r) := by
  let X := strength ε k r
  have hk : 0 < k := (Nat.zero_le _).trans_lt z.isLt
  by_cases large : Real.log 2 ≤ X/2
  · let b (l : ℕ) := (5*Real.exp (-X))*(1/2:ℝ)^l
    have geom := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    apply (tail_bound _ _ _ _ ready b (fun _ => by dsimp [b]; positivity) (geom.mul_left _) ?_).trans_eq
    · rw [Summable.tsum_mul_left _ geom,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      dsimp [X]; ring
    · intro l
      apply (badEpoch_bound (finiteScheme C bd) he s nd (r+l) z inK).trans
      rw [error_finite C bd ε (by omega)]
      have h := tail_growth he hk hr l
      have neg : Real.exp (-strength ε k (r+l)) ≤ Real.exp (-X+(l:ℝ)*(-Real.log 2)) := by
        apply Real.exp_le_exp.mpr
        change X*(1+↑l/2) ≤ _ at h
        nlinarith [mul_nonneg (show (0:ℝ) ≤ l by positivity) (sub_nonneg.mpr large)]
      dsimp [b]
      rw [Real.exp_add,Real.exp_nat_mul,Real.exp_neg (Real.log 2),Real.exp_log (by norm_num : (0:ℝ)<2)] at neg
      nlinarith
  · have h : Real.exp (-(2*Real.log 2)) ≤ Real.exp (-X) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg,show 2*Real.log 2 = (2:ℕ)*Real.log 2 by norm_num,Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0:ℝ)<2)] at h
    norm_num at h
    letI := (generator (finiteScheme C bd) ε).probability s
    apply measureReal_le_one.trans
    change 1 ≤ 10*Real.exp (-X)
    linarith

/-- A uniform explicit version of the continual-release rate. When m
observations have arrived, the event includes failure at time m or at
any later time. -/
theorem finite_generation_rate {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ} (bd : SubcollectionClosureBound (range C) d)
    {ε : ℝ} (he : 0 < ε) :
    ∃ M : ContinualRelease ℕ ℕ, DifferentiallyPrivate ε 0 M.law ∧
      ∀ (z : Fin k) (s : ℕ → ℕ), Function.Injective s → range s ⊆ C z →
      ∀ m : ℕ, 32 ≤ m-d → (M.law s).real (failsAfter (C z) s (m-1)) ≤
        10*Real.exp (-ε*(m-d : ℕ)/(4*k*((Nat.log 2 (m-d):ℝ)+2)^2)) := by
  refine ⟨generator (finiteScheme C bd) ε,generator_private _ he,?_⟩
  intro z s nd inK m hm
  let u := m-d
  let r := Nat.log 2 u
  have hr : 5 ≤ r := Nat.le_log_of_pow_le (by decide) hm
  have lo : 2^r ≤ u := Nat.pow_le_of_le_log (by dsimp [u]; omega) le_rfl
  have hi : u < 2^r*2 := by simpa [r,pow_succ] using Nat.lt_pow_succ_log_self (b := 2) (by decide) u
  have ready : max r (finiteFinish d r) ≤ m-1 := by
    have self : r < 2^r := Nat.lt_two_pow_self
    have formula (j : ℕ) (h : 0 < j) : finiteFinish d j = d+2^j-1 := by cases j with | zero => omega | succ _ => rfl
    have eq := formula r (by omega)
    rw [eq,max_le_iff]; dsimp [u] at lo; omega
  apply (epoch_rate C bd he s nd z inK hr ready).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hk : (0:ℝ) < k := by exact_mod_cast ((Nat.zero_le _).trans_lt z.isLt)
  have upper : (u:ℝ) ≤ (2:ℝ)^r*2 := by exact_mod_cast hi.le
  change -(strength ε k r) ≤ -ε*(u:ℝ)/(4*k*((r:ℝ)+2)^2)
  unfold strength
  rw [neg_mul,neg_div,neg_le_neg_iff]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ (ε*((2:ℝ)^r*2))*(2*k*((r:ℝ)+1)*(r+2)) := by gcongr
    _ ≤ _ := by nlinarith only [show 0 ≤ ε*(2:ℝ)^r*k*(r+2) by positivity]

/-- The paper allows dimension −1 when all subcollection intersections
are infinite. Stating the rate with a signed bound includes this case. -/
theorem finite_generation_signed {k : ℕ} (C : Fin k → Set ℕ) (d : ℤ) (hd : -1 ≤ d)
    (bound : ∀ V ⊆ range C, (⋂₀ V).Finite → ((⋂₀ V).ncard : ℤ) ≤ d)
    {ε : ℝ} (he : 0 < ε) :
    ∃ M : ContinualRelease ℕ ℕ, DifferentiallyPrivate ε 0 M.law ∧
      ∀ (z : Fin k) (s : ℕ → ℕ), Function.Injective s → range s ⊆ C z →
      ∀ m : ℕ, let u := ((m:ℤ)-d).toNat
        33 ≤ u → (M.law s).real (failsAfter (C z) s (m-1)) ≤
          10*Real.exp (-ε*(u:ℝ)/(8*k*((Nat.log 2 u:ℝ)+2)^2)) := by
  have bd : SubcollectionClosureBound (range C) d.toNat := by
    intro V sub fin; have := bound V sub fin; omega
  obtain ⟨M,dp,ok⟩ := finite_generation_rate C bd he
  refine ⟨M,dp,?_⟩
  intro z s nd inK m u hu
  let v := m-d.toNat
  have comp : v ≤ u ∧ u ≤ 2*v ∧ 32 ≤ v := by dsimp [u,v] at *; omega
  apply (ok z s nd inK m comp.2.2).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hk : (0:ℝ) < k := by exact_mod_cast ((Nat.zero_le _).trans_lt z.isLt)
  have log_le : (Nat.log 2 v:ℝ) ≤ Nat.log 2 u := by exact_mod_cast Nat.log_mono_right comp.1
  have h : (u:ℝ) ≤ 2*(v:ℝ) := by exact_mod_cast comp.2.1
  change -ε*(v:ℝ)/(4*k*((Nat.log 2 v:ℝ)+2)^2) ≤ _
  rw [neg_mul,neg_div,neg_mul,neg_div,neg_le_neg_iff]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ (ε*(2*(v:ℝ)))*(4*k*((Nat.log 2 u:ℝ)+2)^2) := by gcongr
    _ = _ := by ring

end
end GenLimit.PrivateLimit.Epoch
