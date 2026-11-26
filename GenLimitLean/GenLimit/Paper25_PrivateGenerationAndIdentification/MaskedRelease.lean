import GenLimit.Paper25_PrivateGenerationAndIdentification.FiniteWordRelease
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A one-observation private generator for every family of 4h languages
with closure dimension at most zero. It omits one uniformly chosen block of
h labels. The other membership bits can be privately released for a budget
of 3h log 2 + log 128. This tests the one-shot claim following Theorem C.3. -/
namespace GenLimit.PrivateLimit.MaskedRelease

open Set DiscreteIID PriceOfPrivacy Filter
open scoped Classical ENNReal
noncomputable section

abbrev Label (h : ℕ) := Fin 4 × Fin h
abbrev Signal (h : ℕ) := Fin 4 × (Fin 3 × Fin h → Bool)

def truthful {h : ℕ} (C : Label h → Set ℕ) (x : ℕ) (b : Fin 4) : Signal h :=
  (b, fun ij => decide (x ∈ C (b.succAbove ij.1, ij.2)))

def selected {h : ℕ} (C : Label h → Set ℕ) (v : Signal h) : Set (Set ℕ) :=
  {L | ∃ i j, v.2 (i,j) = true ∧ L = C (v.1.succAbove i,j)}

def signalLaw {h : ℕ} (C : Label h → Set ℕ) (x : ℕ) : PMF (Signal h) :=
  (PMF.bernoulli (1/32) ((div_le_one (by norm_num)).mpr (by norm_num))).bind fun noise =>
    if noise then PMF.uniformOfFintype _ else (PMF.uniformOfFintype _).map (truthful C x)

def budget (h : ℕ) : ℝ := Real.log (128 * 2^(3*h) : ℝ)

/-- Along arbitrarily large sizes k = 4h, one observation costs strictly
less than k log 2 minus any prescribed logarithmic allowance. -/
theorem below_published_bound (a b : ℝ) :
    ∀ᶠ h : ℕ in Filter.atTop, budget h < 4*(h:ℝ)*Real.log 2 - a*Real.log (4*h) - b := by
  have logs : Tendsto (fun h : ℕ => Real.log h/(h:ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have inv : Filter.Tendsto (fun h : ℕ => (1:ℝ)/(h:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop _
  have lim : Filter.Tendsto
      (fun h : ℕ => (Real.log 128 + b + a*Real.log 4 + a*Real.log h)/(h:ℝ))
      Filter.atTop (nhds 0) := by
    have l := (inv.const_mul (Real.log 128 + b + a*Real.log 4)).add (logs.const_mul a)
    convert l using 1
    · funext h; ring
    · simp
  filter_upwards [lim.eventually_lt_const (Real.log_pos (by norm_num : (1:ℝ)<2)),
    Filter.eventually_ge_atTop 1] with h hlt hpos
  have hp : 0 < (h:ℝ) := by exact_mod_cast hpos
  have step := (div_lt_iff₀ hp).mp hlt
  rw [budget, Real.log_mul (by norm_num) (by positivity),Real.log_pow,
    Real.log_mul (by norm_num) hp.ne']
  push_cast
  linarith

theorem signal_compare {h : ℕ} (C : Label h → Set ℕ) (x y : ℕ) (F : Set (Signal h)) :
    probability (signalLaw C x) F ≤ Real.exp (budget h) * probability (signalLaw C y) F := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨v,hv⟩
  · simp [probability]
  have lower := probability_bind_ge (PMF.bernoulli (1/32) ((div_le_one (by norm_num)).mpr (by norm_num)))
    (fun noise : Bool => if noise then PMF.uniformOfFintype (Signal h)
      else (PMF.uniformOfFintype _).map (truthful C y)) F true
  have atom := probability_mono (PMF.uniformOfFintype (Signal h)) (singleton_subset_iff.mpr hv)
  simp only [if_true] at lower
  change _ ≤ probability (signalLaw C y) F at lower
  have card : Fintype.card (Signal h) = 4 * 2^(3*h) := by simp [Signal]
  have atomEq : probability (PMF.uniformOfFintype (Signal h)) {v} = (4 * 2^(3*h) : ℝ)⁻¹ := by
    rw [probability, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, card]
    simp
  rw [atomEq] at atom
  norm_num [PMF.bernoulli_apply] at lower
  rw [budget,Real.exp_log (by positivity)]
  apply (probability_le_one ..).trans
  have pos : 0 < (2:ℝ)^(3*h) := by positivity
  have a := (inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < 4*2^(3*h))).mp atom
  nlinarith [mul_le_mul_of_nonneg_left lower pos.le]

def badSignal {h : ℕ} (C : Label h → Set ℕ) (z : Label h) : Set (Signal h) :=
  {v | ¬((⋂₀ selected C v).Infinite ∧ ⋂₀ selected C v ⊆ C z)}

private theorem truthful_safe {h : ℕ} (C : Label h → Set ℕ)
    (bound : SubcollectionClosureBound (range C) 0) (z : Label h) {x : ℕ} (hx : x ∈ C z)
    (b : Fin 4) (keep : z.1 ≠ b) : truthful C x b ∉ badSignal C z := by
  have sub : selected C (truthful C x b) ⊆ range C := by
    rintro _ ⟨i,j,_,rfl⟩; exact ⟨_,rfl⟩
  have contains : x ∈ ⋂₀ selected C (truthful C x b) := by
    apply mem_sInter.mpr
    rintro _ ⟨i,j,H,rfl⟩
    simpa [truthful] using H
  obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq keep
  have target : C z ∈ selected C (truthful C x b) := by
    exact ⟨i,z.2,by simpa [truthful,hi] using hx,by simp [truthful,hi]⟩
  change ¬¬_
  apply not_not_intro
  refine ⟨fun fin => ?_, sInter_subset_of_mem target⟩
  have pos := Set.ncard_pos (s := ⋂₀ selected C (truthful C x b)) (hs := fin) |>.mpr ⟨_,contains⟩
  exact (Nat.not_lt_of_ge (bound _ sub fin)) pos

theorem unsafe_probability {h : ℕ} (C : Label h → Set ℕ)
    (bound : SubcollectionClosureBound (range C) 0) (z : Label h) {x : ℕ} (hx : x ∈ C z) :
    probability (signalLaw C x) (badSignal C z) ≤ 1/32 + 1/4 := by
  let F := badSignal C z
  have sub : (truthful C x) ⁻¹' F ⊆ {z.1} := by
    intro b hb
    by_contra ne
    exact truthful_safe C bound z hx b (Ne.symm ne) hb
  have bad := probability_mono (PMF.uniformOfFintype (Fin 4)) sub
  have quarter : probability (PMF.uniformOfFintype (Fin 4)) {z.1} = 1/4 := by
    rw [probability, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
    norm_num
  rw [quarter] at bad
  change probability _ F ≤ _
  refine (bind_event_off_exception _ _ F ({true} : Set Bool) (b := 1/4) (by norm_num) ?_).trans ?_
  · rintro (_ | _) _ hn
    · simpa only [Bool.false_eq_true, if_false, probability, PMF.toOuterMeasure_map_apply] using bad
    · simp at hn
  · rw [probability, PMF.toOuterMeasure_apply_singleton]
    norm_num [PMF.bernoulli_apply]

def generator {h : ℕ} (C : Label h → Set ℕ) (pool : ℕ) [NeZero pool] (xs : List ℕ) : PMF ℕ :=
  (signalLaw C (xs.headD 0)).bind fun v =>
    (PMF.uniformOfFintype (Fin pool)).map fun j =>
      Generation.word (Equiv.refl ℕ) (⋂₀ selected C v) j.val

theorem generator_private {h : ℕ} (C : Label h → Set ℕ) (pool : ℕ) [NeZero pool] :
    PrivateAt (budget h) 0 1 (generator C pool) := by
  apply privateAt_random_map (A := fun xs => signalLaw C (xs.headD 0))
  intro pre x y post _ F
  simpa using signal_compare C ((pre ++ x::post).headD 0) ((pre ++ y::post).headD 0) F

theorem generator_error {h : ℕ} (C : Label h → Set ℕ)
    (bound : SubcollectionClosureBound (range C) 0) (z : Label h) {x : ℕ} (hx : x ∈ C z)
    (avoid : List ℕ) (pool : ℕ) [NeZero pool] :
    probability (generator C pool [x]) {y | y ∉ C z ∨ y ∈ avoid} ≤
      (1/32 + 1/4) + avoid.length/(pool:ℝ) := by
  let F := {y | y ∉ C z ∨ y ∈ avoid}
  apply (bind_event_off_exception _ _ F (badSignal C z) (b := avoid.length/(pool:ℝ))
    (by positivity) ?_).trans (add_le_add_right (unsafe_probability C bound z hx) _)
  intro v _ hv
  obtain ⟨inf,sub⟩ := Classical.not_not.mp hv
  let word := Generation.word (Equiv.refl ℕ) (⋂₀ selected C v)
  have pre : (fun j : Fin pool => word j.val) ⁻¹' F = {j : Fin pool | word j.val ∈ avoid} := by
    ext j
    have mem : word j.val ∈ C z := sub (Nat.nth_mem_of_infinite inf _)
    simp [F,mem]
  change probability ((PMF.uniformOfFintype (Fin pool)).map fun j => word j.val) F ≤ _
  rw [probability, PMF.toOuterMeasure_map_apply, pre]
  exact Generation.collision (Equiv.refl ℕ) inf avoid

theorem one_sample {h : ℕ} (C : Label h → Set ℕ)
    (bound : SubcollectionClosureBound (range C) 0) :
    PrivateAt (budget h) 0 1 (generator C 32) ∧ ∀ z x, x ∈ C z →
      probability (generator C 32 [x]) {y | y ∉ C z ∨ y = x} ≤ 1/3 := by
  refine ⟨generator_private C 32, fun z x hx => ?_⟩
  have small := generator_error C bound z hx [x] 32
  simp only [List.mem_singleton, List.length_singleton, Nat.cast_one, Nat.cast_ofNat] at small
  linarith

/-- The finite-sample assertion following C.3 fails with unrestricted
positive privacy budgets, even allowing arbitrary constants in O(log k).
Every zero-dimensional family of these sizes admits the countermechanism. -/
theorem one_shot_counterexample (a b : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ C : Fin (4*h) → Set ℕ, SubcollectionClosureBound (range C) 0 →
      ∃ (ε : ℝ) (A : List ℕ → PMF ℕ), 0 < ε ∧
        ε < (4*h:ℕ)*Real.log 2 - a*Real.log (4*h) - b ∧ PrivateAt ε 0 1 A ∧
        ∀ z x, x ∈ C z → probability (A [x]) {y | y ∉ C z ∨ y = x} ≤ 1/3 := by
  filter_upwards [below_published_bound a b] with h below
  intro C bound
  let e : Label h ≃ Fin (4*h) := finProdFinEquiv
  have eq : range (C ∘ e) = range C := e.surjective.range_comp C
  obtain ⟨privateA,correct⟩ := one_sample (C ∘ e) (eq ▸ bound)
  have scale : 1 ≤ (2:ℝ)^(3*h) := one_le_pow₀ (by norm_num)
  refine ⟨budget h, generator (C ∘ e) 32, Real.log_pos (by linarith : 1 < 128*(2:ℝ)^(3*h)),
    by simpa using below, privateA, ?_⟩
  intro z x hx
  obtain ⟨i,rfl⟩ := e.surjective z
  exact correct i x hx

end
end GenLimit.PrivateLimit.MaskedRelease
