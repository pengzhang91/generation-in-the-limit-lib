import GenLimit.Paper24_PriceOfPrivacy.Testing
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model

/-! Approximate-private resampling for Theorem 4.7. Replacing observations
by a fixed map outside a small set leaves the single-coordinate likelihood
ratio at most 1 + t (exp ε − 1), where t is the mass of that set. -/

namespace GenLimit.PriceOfPrivacy

open AgnosticLanguage DiscreteIID Set
open scoped ENNReal Classical
noncomputable section

/-- Definition 2.1 at a fixed sample size. This form allows δ to vary with n. -/
def PrivateAt (ε δ : ℝ) (n : ℕ) (A : List X → PMF Y) : Prop :=
  ∀ pre (x y : X) post, pre.length + post.length + 1 = n → ∀ F : Set Y,
    probability (A (pre ++ x :: post)) F ≤
      Real.exp ε * probability (A (pre ++ y :: post)) F + δ

theorem privateAt_of_pure {A : List X → PMF Y} {ε : ℝ≥0∞} (hε : ε ≠ ⊤)
    (dp : IsPrivate ε A) (n : ℕ) : PrivateAt ε.toReal 0 n A := by
  intro pre x y post _ F
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (event_ne_top _ _)) (dp hε pre x y post F)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,add_zero,
    probability] using h

private def avg (p : PMF X) (v : X → ℝ) := ∑' x, (p x).toReal * v x

private theorem avg_const (p : PMF X) (c : ℝ) : avg p (fun _ => c) = c := by
  rw [avg,tsum_mul_right,← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x),p.tsum_coe]
  simp

private theorem avg_le_affine (p : PMF X) (u v : X → ℝ) (D : Set X) (a b : ℝ)
    (hu : ∀ x, u x ∈ Icc 0 1) (hv : ∀ x, v x ∈ Icc 0 1)
    (h : ∀ x ∈ p.support, u x ≤ a * v x + b * (if x ∈ D then 1 else 0)) :
    avg p u ≤ a * avg p v + b * probability p D := by
  have si := weighted_summable p (v := fun x => if x ∈ D then 1 else 0)
    (fun x => by by_cases hx : x ∈ D <;> simp [hx,Icc])
  rw [avg,avg,prob_event_tsum,←tsum_mul_left,←tsum_mul_left,
    ←((weighted_summable p hv).mul_left a).tsum_add (si.mul_left b)]
  apply (weighted_summable p hu).tsum_le_tsum _ (((weighted_summable p hv).mul_left a).add (si.mul_left b))
  intro x
  by_cases hx : x ∈ p.support
  · simpa only [mul_add,mul_left_comm (p x).toReal] using
      mul_le_mul_of_nonneg_left (h x hx) (ENNReal.toReal_nonneg (a := p x))
  · simp [show p x = 0 from Classical.not_not.mp hx]

private theorem avg_affine_all (p : PMF X) (u v : X → ℝ) (a b : ℝ)
    (hu : ∀ x, u x ∈ Icc 0 1) (hv : ∀ x, v x ∈ Icc 0 1)
    (h : ∀ x ∈ p.support, u x ≤ a*v x+b) :
    avg p u ≤ a*avg p v+b := by
  simpa using avg_le_affine p u v univ a b hu hv (by simpa using h)

/-- Integrate a conditional error bound over the good samples. -/
theorem bind_event_off_exception (p : PMF X) (A : X → PMF Y) (F : Set Y)
    (bad : Set X) {b : ℝ} (hb : 0 ≤ b)
    (good : ∀ x ∈ p.support, x ∉ bad → probability (A x) F ≤ b) :
    probability (p.bind A) F ≤ probability p bad + b := by
  have h := avg_le_affine p (fun x => probability (A x) F) (fun _ => 1) bad b 1
    (fun _ => ⟨probability_nonneg ..,probability_le_one ..⟩) (fun _ => ⟨zero_le_one,le_rfl⟩)
    (fun x hx => by
      by_cases he : x ∈ bad
      · simp only [he,if_true,mul_one]; linarith [probability_le_one (A x) F]
      · simpa [he] using good x hx he)
  rw [avg_const,mul_one,one_mul,add_comm] at h
  simpa only [avg,probability_bind_eq_tsum] using h

/-- A public random seed, sampled independently of the data, can be used
to post-process a private release without increasing the privacy slack. -/
theorem privateAt_random_map {A : List X → PMF Y} {ε δ : ℝ} {n : ℕ}
    (dp : PrivateAt ε δ n A) (q : PMF Z) (f : Y → Z → V) :
    PrivateAt ε δ n (fun xs => (A xs).bind (fun y => q.map (f y))) := by
  intro pre x y post len F
  have commute (xs : List X) : (A xs).bind (fun i => q.map (f i)) =
      q.bind (fun z => (A xs).map fun i => f i z) := PMF.bind_comm ..
  dsimp only
  simp only [commute,probability_bind_eq_tsum]
  have unit (xs : List X) (z : Z) : probability ((A xs).map fun i => f i z) F ∈ Icc 0 1 :=
    ⟨probability_nonneg ..,probability_le_one ..⟩
  exact avg_affine_all q _ _ (Real.exp ε) δ (unit _) (unit _) (fun z _ => by
    simpa only [probability,PMF.toOuterMeasure_map_apply] using dp pre x y post len ((fun i => f i z) ⁻¹' F))

private theorem single_replacement (p : PMF X) (g : X → X) (D : Set X)
    (same : ∀ x ∉ D, g x = x) (v : X → ℝ) (hv : ∀ x, v x ∈ Icc 0 1)
    (b δ : ℝ) (hb : 1 ≤ b) (dp : ∀ x y, v x ≤ b*v y + δ) :
    avg p (v ∘ g) ≤ (1 + probability p D * (b-1)) * avg p v + probability p D * δ := by
  have spread (x y : X) : v (g x) ≤ v x + (b-1)*v y + δ := by
    rcases le_total (v x) (v y) with h | h
    · nlinarith [dp (g x) x,mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr h)]
    · linarith [dp (g x) y]
  have cost (x : X) : v (g x) ≤ v x + (b-1)*avg p v + δ := by
    have h := avg_affine_all p (fun _ => v (g x)) v (b-1) (v x+δ)
      (fun _ => hv _) hv (fun y _ => by linarith [spread x y])
    rw [avg_const] at h
    linarith
  have h := avg_le_affine p (v ∘ g) v D 1 ((b-1)*avg p v+δ) (fun x => hv _) hv
    (fun x _ => by
      by_cases hx : x ∈ D
      · simpa [Function.comp_def,hx,add_assoc] using cost x
      · simp [hx,same x hx])
  linarith only [h]

/-- Probability of F in the randomized output after n independent samples. -/
def sampleEvent (p : PMF X) (A : List X → PMF Y) (F : Set Y) (n : ℕ) :=
  probability ((samples p n).bind A) F

private theorem sampleEvent_step (p : PMF X) (g : X → X) (A : List X → PMF Y)
    (F : Set Y) (n : ℕ) : sampleEvent (p.map g) A F (n+1) =
    avg p (fun x => sampleEvent (p.map g) (fun ys => A (g x :: ys)) F n) := by
  unfold sampleEvent
  rw [samples,PMF.bind_bind,PMF.bind_map,probability_bind_eq_tsum]
  simp only [avg,Function.comp_apply,PMF.bind_map,Function.comp_def]

private theorem sampleEvent_step_self (p : PMF X) (A : List X → PMF Y)
    (F : Set Y) (n : ℕ) : sampleEvent p A F (n+1) =
    avg p (fun x => sampleEvent p (fun ys => A (x :: ys)) F n) := by
  simpa only [PMF.map_id,id_eq] using sampleEvent_step p id A F n

/-- Finite-sample resampling bound for an arbitrary deterministic replacement
on a set of probability t. The bound applies to every output event. -/
theorem private_resample (p : PMF X) (g : X → X) (D : Set X) (same : ∀ x ∉ D, g x = x)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (F : Set Y) (n : ℕ)
    (A : List X → PMF Y) (dp : PrivateAt ε δ n A) :
    sampleEvent (p.map g) A F n ≤ (1 + probability p D * (Real.exp ε - 1))^n *
      (sampleEvent p A F n + n*δ) := by
  let t := probability p D
  let k := 1+t*(Real.exp ε-1)
  have bpos := Real.one_le_exp_iff.mpr hε
  have kge : 1 ≤ k := by dsimp [k,t]; nlinarith [mul_nonneg (probability_nonneg p D) (sub_nonneg.mpr bpos)]
  induction n generalizing A with
  | zero => simp [sampleEvent,samples]
  | succ n ih =>
    let tail (x : X) (ys : List X) := A (x::ys)
    let v (x : X) := sampleEvent p (tail x) F n
    have unit (q : PMF X) (x : X) : sampleEvent q (tail x) F n ∈ Icc (0:ℝ) 1 :=
      ⟨probability_nonneg ..,probability_le_one ..⟩
    have privateTail (x) : PrivateAt ε δ n (tail x) := by
      intro pre u v post len F
      exact dp (x::pre) u v post (by simp; omega) F
    have one (x y) : v x ≤ Real.exp ε * v y + δ := by
      have h := avg_affine_all (samples p n) (fun ys => probability (A (x::ys)) F)
        (fun ys => probability (A (y::ys)) F) (Real.exp ε) δ
        (fun _ => ⟨probability_nonneg ..,probability_le_one ..⟩)
        (fun _ => ⟨probability_nonneg ..,probability_le_one ..⟩)
        (fun ys hy => dp [] x y ys (by simp [(samples_support p n ys).mp hy |>.1]) F)
      simpa only [v,sampleEvent,probability_bind_eq_tsum,avg,tail] using h
    have first := single_replacement p g D same v (unit p) (Real.exp ε) δ bpos one
    change avg p (v ∘ g) ≤ k * avg p v + t*δ at first
    have rest := avg_affine_all p (fun x => sampleEvent (p.map g) (tail (g x)) F n)
      (v ∘ g) (k^n) (k^n*(n*δ)) (fun _ => unit ..) (fun _ => unit ..)
      (fun x _ => by simpa [v,k,t,mul_add] using ih (tail (g x)) (privateTail _))
    rw [sampleEvent_step,sampleEvent_step_self]
    change _ ≤ k^(n+1) * (avg p v + (n+1:ℕ)*δ)
    have slack : t*δ + n*δ ≤ k*((n:ℝ)+1)*δ := by
      have hn : 0 ≤ (n:ℝ)+1 := by positivity
      have h := mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hn kge) hδ
      nlinarith [mul_le_mul_of_nonneg_right (probability_le_one p D) hδ]
    calc
      _ ≤ k^n * (k * avg p v + t*δ) + k^n*(n*δ) :=
        rest.trans (add_le_add_right (mul_le_mul_of_nonneg_left first (pow_nonneg (by linarith) _)) _)
      _ ≤ _ := by
        rw [pow_succ,Nat.cast_add,Nat.cast_one]
        nlinarith [mul_le_mul_of_nonneg_left slack (pow_nonneg (by linarith : 0 ≤ k) n)]

end
end GenLimit.PriceOfPrivacy
