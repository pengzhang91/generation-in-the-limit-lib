import GenLimit.Paper24_PriceOfPrivacy.Testing
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Coupled experiments sharing a three-quarter atom in Theorems 5.2 and 5.4. -/

namespace GenLimit.PriceOfPrivacy

open DiscreteIID
open scoped ENNReal Classical
noncomputable section

private def coin : PMF Bool := PMF.bernoulli (3/4 : NNReal)
  (by norm_num1; exact (div_le_one (by norm_num)).mpr (by norm_num))

private theorem coin_true : coin true = 3/4 := by simp [coin,PMF.bernoulli_apply]

private theorem threeQuarters_finite : (3/4 : ℝ≥0∞) ≠ ⊤ := coin_true ▸ coin.apply_ne_top true

private theorem coin_false : coin false = 1/4 := by
  rw [show coin false = 1 - (3/4 : ℝ≥0∞) by simp [coin,PMF.bernoulli_apply]]
  exact ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    (by norm_num) |>.mp (by
      have le : (3/4 : ℝ≥0∞) ≤ 1 := by
        rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      rw [ENNReal.toReal_sub_of_le le ENNReal.one_ne_top]
      norm_num)

/-- The latent label is absent at the common atom and has law q otherwise. -/
def latent (q : PMF Z) : PMF (Option Z) :=
  coin.bind (fun b => if b then PMF.pure none else q.map some)

/-- The common atom has weight 3/4 and the private tail has weight 1/4.
The definition also applies when atoms on the two branches coincide. -/
def spiked (q : PMF Z) (a : X) (f : Z → X) : PMF X :=
  (latent q).map (fun z => z.elim a f)

theorem spiked_support (q : PMF Z) (a : X) (f : Z → X) :
    (spiked q a f).support = insert a (f '' q.support) := by
  have hc (b : Bool) : b ∈ coin.support := by
    cases b <;> rw [PMF.mem_support_iff]
    · rw [coin_false]; norm_num
    · rw [coin_true]; norm_num
  ext x
  rw [spiked,PMF.mem_support_map_iff]
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨b,_,hb⟩ := (PMF.mem_support_bind_iff ..).mp hz
    cases b with
    | true =>
      change z ∈ (PMF.pure none).support at hb
      obtain rfl : z = none := by simpa using hb
      exact Set.mem_insert ..
    | false =>
      change z ∈ (q.map some).support at hb
      obtain ⟨v,hv,rfl⟩ := (PMF.mem_support_map_iff ..).mp hb
      exact Or.inr ⟨v,hv,rfl⟩
  · rintro (rfl | ⟨v,hv,rfl⟩)
    · exact ⟨none,(PMF.mem_support_bind_iff ..).mpr ⟨true,hc _,by simp⟩,rfl⟩
    · exact ⟨some v,(PMF.mem_support_bind_iff ..).mpr ⟨false,hc _,
        (PMF.mem_support_map_iff ..).mpr ⟨v,hv,rfl⟩⟩,rfl⟩

private theorem moment_latent (q : PMF Z) (h : Option Z → ℝ≥0∞) :
    moment (latent q) h = (3/4 : ℝ≥0∞) * h none + (1/4 : ℝ≥0∞) * moment q (h ∘ some) := by
  rw [latent,moment_bind,moment,tsum_bool]
  simp [coin_false,coin_true,moment_pure,moment_map,Function.comp_def,add_comm]

private theorem moment_const (q : PMF Z) (c : ℝ≥0∞) : moment q (fun _ => c) = c := by
  simp [moment,ENNReal.tsum_mul_right,q.tsum_coe]

theorem spiked_event (q : PMF Z) (a : X) (f : Z → X) (F : Set X) :
    probability (spiked q a f) F =
      (if a ∈ F then 3/4 else 0) + (1/4) * probability (q.map f) F := by
  classical
  let h : Option Z → ℝ≥0∞ := fun z => if z.elim a f ∈ F then 1 else 0
  have eq : (spiked q a f).toOuterMeasure F = moment (latent q) h := by
    rw [spiked,PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_apply]
    exact tsum_congr fun z => by by_cases hz : z.elim a f ∈ F <;> simp [h,Set.indicator,Set.preimage,hz]
  have eq' : moment q (h ∘ some) = (q.map f).toOuterMeasure F := by
    rw [PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_apply]
    exact tsum_congr fun z => by by_cases hz : f z ∈ F <;> simp [h,Set.indicator,Set.preimage,hz]
  unfold probability
  have hn : h none ≠ ⊤ := by
    by_cases ha : a ∈ F <;> simp [h,ha]
  rw [eq,moment_latent,eq',ENNReal.toReal_add (ENNReal.mul_ne_top threeQuarters_finite hn)
    (ENNReal.mul_ne_top (by norm_num) (event_ne_top _ _))]
  by_cases ha : a ∈ F <;> simp [h,ha,ENNReal.toReal_mul,ENNReal.toReal_div]

/-- The one-coordinate expected retention for the shared-atom pair. -/
def commonRate (ε : ℝ≥0∞) := 1 - (1 - retention ε)/4

theorem spiked_testing {A : List X → PMF Y} {ε} (dp : IsPrivate ε A)
    (q : PMF Z) (a : X) (f g : Z → X) (F : Set Y) (n : ℕ) :
    commonRate ε ^ n ≤ probability ((samples (spiked q a f) n).bind A) Fᶜ +
      probability ((samples (spiked q a g) n).bind A) F := by
  let D : Set (Option Z) := {z | z ≠ none}
  have h := private_two_point dp (latent q) (fun z => z.elim a f) (fun z => z.elim a g)
    D (fun z hz => by cases z <;> simp_all [D]) F n
  have eq : (moment (latent q) (coordinateWeight ε D)).toReal = commonRate ε := by
    rw [moment_latent]
    have tail : (coordinateWeight ε D ∘ some) = fun _ : Z => ENNReal.ofReal (retention ε) := by
      funext z; simp [D,coordinateWeight]
    rw [tail,moment_const]
    have hw : coordinateWeight ε D none = 1 := by simp [D,coordinateWeight]
    rw [hw,mul_one,ENNReal.toReal_add threeQuarters_finite
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top),ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (retention_mem ε).1]
    norm_num [commonRate]
    ring
  rwa [eq] at h

theorem commonRate_ge_exponential (ε : ℝ≥0∞) (n : ℕ) :
    Real.exp (-((min 1 ε).toReal) * n / 3) ≤ commonRate ε ^ n := by
  have budget : 1 - retention ε ≤ (min 1 ε).toReal := by
    by_cases top : ε = ⊤
    · simp [top,retention]
    · rw [ENNReal.toReal_min ENNReal.one_ne_top top,ENNReal.toReal_one]
      apply le_min
      · linarith [(retention_mem ε).1]
      · simp only [retention,if_neg top]
        linarith [Real.add_one_le_exp (-ε.toReal)]
  have range := retention_mem ε
  have lower : (3/4 : ℝ) ≤ commonRate ε := by unfold commonRate; linarith [range.1]
  have pos : 0 < commonRate ε := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos pos
  have hinv : -(1-retention ε)/3 ≤ 1-(commonRate ε)⁻¹ := by
    rw [← one_div]
    apply (le_sub_comm).mpr
    apply (div_le_iff₀ pos).mpr
    have h := mul_le_mul_of_nonneg_right lower (sub_nonneg.mpr range.2)
    unfold commonRate at h ⊢
    nlinarith
  have base : Real.exp (-((min 1 ε).toReal)/3) ≤ commonRate ε :=
    (Real.le_log_iff_exp_le pos).mp (by linarith)
  have powers := pow_le_pow_left₀ (Real.exp_pos _).le base n
  rwa [←Real.exp_nat_mul, show (n:ℝ) * (-((min 1 ε).toReal)/3) =
    -((min 1 ε).toReal) * n/3 by ring] at powers

end
end GenLimit.PriceOfPrivacy
