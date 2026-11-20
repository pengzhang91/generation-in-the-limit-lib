import GenLimit.NoRegretLanguageGeneration.PredictionRates
import GenLimit.NoRegretLanguageGeneration.Uniform
import GenLimit.NoRegretLanguageGeneration.AnytimeAgnosticReal

namespace PredictionToGeneration
open Classical
open scoped ENNReal

/-- Sequential capacity of a finite class is bounded by its total mass at every depth. -/
theorem capacity_finite_sum (F : Finset (Hypothesis X)) (H : HypothesisClass X)
    (hF : ∀ h, H h → h ∈ F) (w : Hypothesis X → ℝ≥0∞) (n : Nat) :
    capacity H w n ≤ ∑ h ∈ F, w h := by
  induction n generalizing H F with
  | zero =>
    apply sSup_le
    rintro _ ⟨h, hh, rfl⟩
    exact Finset.single_le_sum (fun _ _ => zero_le _) (hF h hh)
  | succ n ih =>
    apply iSup_le
    intro x
    have h0 := ih (F.filter (fun h => h x = false)) (restrict H x false)
      (fun h hh => Finset.mem_filter.mpr ⟨hF h hh.1, hh.2⟩)
    have h1 := ih (F.filter (fun h => h x = true)) (restrict H x true)
      (fun h hh => Finset.mem_filter.mpr ⟨hF h hh.1, hh.2⟩)
    have he : (∑ h ∈ F.filter (fun h => h x = false), w h) +
        (∑ h ∈ F.filter (fun h => h x = true), w h) = ∑ h ∈ F, w h := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      cases h x <;> simp
    exact (add_le_add h0 h1).trans he.le

theorem capacity_finite_card (F : Finset (Hypothesis X)) (n : Nat) :
    capacity (fun h => h ∈ F) (fun _ => 1) n ≤ (F.card : ℝ≥0∞) := by
  simpa using capacity_finite_sum F (fun h => h ∈ F) (fun _ hh => hh) (fun _ => 1) n

private noncomputable def finiteMass (F : Finset (Hypothesis X)) (w : Hypothesis X → Nat) : Nat :=
  ∑ h ∈ F, w h

private noncomputable def positiveMass (F : Finset (Hypothesis X)) (w : Hypothesis X → Nat) (x : X) : Nat :=
  ∑ h ∈ F, if h x then w h else 0

private theorem positiveMass_le (F : Finset (Hypothesis X)) (w : Hypothesis X → Nat) (x : X) :
    positiveMass F w x ≤ finiteMass F w := by
  apply Finset.sum_le_sum
  intro h hh
  cases h x <;> simp

private theorem positiveMass_maximizer (F : Finset (Hypothesis X)) (w : Hypothesis X → Nat)
    (fallback : Generator X) (τ : Trajectory X) :
    ∃ z, Fresh τ z ∧ ∀ x, Fresh τ x → positiveMass F w x ≤ positiveMass F w z := by
  let f := positiveMass F w
  let D := {x | Fresh τ x}
  have hn : D.Nonempty := ⟨fallback.output (demonstrations τ), fallback.fresh _⟩
  have hf : (f '' D).Finite := (Set.finite_Iic (finiteMass F w)).subset (by
    rintro _ ⟨x, _, rfl⟩
    exact positiveMass_le F w x)
  obtain ⟨z, hz, he⟩ := (hn.image f).csSup_mem hf
  refine ⟨z, hz, fun x hx => ?_⟩
  change f x ≤ f z
  rw [he]
  exact le_csSup hf.bddAbove ⟨x, hx, rfl⟩

private noncomputable def finiteRealizableWeight (τ : Trajectory X) (h : Hypothesis X) : Nat :=
  if Realizes h τ then 2 ^ mistakes h τ else 0

private theorem finite_weight_update (F : Finset (Hypothesis X)) (τ : Trajectory X) (z x : X)
    (hmax : positiveMass F (finiteRealizableWeight τ) x ≤ positiveMass F (finiteRealizableWeight τ) z) :
    finiteMass F (finiteRealizableWeight ((z,x)::τ)) ≤ finiteMass F (finiteRealizableWeight τ) := by
  have hs : finiteMass F (finiteRealizableWeight ((z,x)::τ)) + positiveMass F (finiteRealizableWeight τ) z ≤
      finiteMass F (finiteRealizableWeight τ) + positiveMass F (finiteRealizableWeight τ) x := by
    unfold finiteMass positiveMass
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro h hh
    by_cases hr : Realizes h τ
    · cases hz : h z <;> cases hx : h x <;>
        simp [finiteRealizableWeight, Realizes, mistakes, loss, hr, hz, hx, pow_succ, pow_add]
      all_goals omega
    · simp [finiteRealizableWeight, Realizes, hr]
  omega

/-- Finite-class mass controls arbitrary well-founded forcing, not merely fixed horizons. -/
theorem finite_wellFounded_exponential (F : Finset (Hypothesis X)) (fallback : Generator X)
    (m : Nat) (τ : Trajectory X) (hf : WellFoundedForces (RealizableBad (fun h => h ∈ F) m) τ) :
    2 ^ m ≤ finiteMass F (finiteRealizableWeight τ) := by
  induction hf with
  | @leaf τ hb =>
    obtain ⟨h, hh, hr, hm⟩ := hb
    have hp : 2^m ≤ 2^mistakes h τ := Nat.pow_le_pow_right (by decide) hm
    have hs := Finset.single_le_sum (fun h (_ : h ∈ F) => Nat.zero_le (finiteRealizableWeight τ h)) hh
    have he : finiteRealizableWeight τ h = 2^mistakes h τ := by simp [finiteRealizableWeight, hr]
    exact hp.trans (he ▸ hs)
  | @step τ response legal children ih =>
    obtain ⟨z, hz, hm⟩ := positiveMass_maximizer F (finiteRealizableWeight τ) fallback τ
    exact (ih z hz).trans (finite_weight_update F τ z (response z hz) (hm _ (legal z hz)))

/-- The finite-class uniform mistake bound, with base-two integer logarithm. -/
theorem finite_class_uniform_bound (F : Finset (Hypothesis X))
    (hu : UUS (fun h => h ∈ F)) (hne : F.Nonempty) :
    ∃ G : Generator X, UniformMistakeBound G (fun h => h ∈ F) (Nat.log 2 F.card) := by
  apply (realizable_uniform_characterization (fun h => h ∈ F) hu hne _).mp
  intro hf
  have hb := finite_wellFounded_exponential F (generatorOfUUS _ hu hne) _ [] hf
  have hl := Nat.lt_pow_succ_log_self (by decide : 1<2) F.card
  simp [finiteMass, finiteRealizableWeight, Realizes, mistakes] at hb
  omega

theorem finite_class_agnostic_potential (F : Finset (Hypothesis X))
    (hu : UUS (fun h => h ∈ F)) (hne : F.Nonempty) (T : Nat)
    (η : ℝ≥0∞) (hη : η ≤ 1) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → xs.length = T →
      ∀ h, h ∈ F → agnosticWeight η h (G.play xs) ≤ (F.card : ℝ≥0∞) := by
  obtain ⟨s, hs⟩ := capacity_agnostic_strategy (generatorOfUUS _ hu hne) η hη T []
    (fun h => h ∈ F) (fun _ => 1) Set.finite_range_const (by intro h _; rfl)
  have ht : Guarantees (fun leaf => ∀ h, h ∈ F → agnosticWeight η h leaf ≤ (F.card : ℝ≥0∞)) s := by
    apply guarantees_mono s (hs := hs)
    intro leaf hb h hh
    exact (hb h hh).trans (capacity_finite_card F (2*T))
  obtain ⟨G, hg⟩ := (strategy_iff_generator (generatorOfUUS _ hu hne) _ T).mp ⟨s, ht⟩
  exact ⟨G, (G.guarantees_iff_histories _ T).mp hg⟩

private theorem finite_class_agnostic_eta (F : Finset (Hypothesis X))
    (hu : UUS (fun h => h ∈ F)) (hne : F.Nonempty) (T : Nat)
    (η : ℝ) (hη : 0 < η) (hhalf : η ≤ 1/2) :
    (SMF (fun h => h ∈ F) T : ℝ) ≤ Real.logb 2 (F.card : ℝ) / η + η*(T : ℝ) := by
  let lam := η * Real.log 2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlu : Real.log 2 ≤ 1 := by have ht := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num); linarith
  have hlam : 0 < lam := mul_pos hη hl
  have hlamhalf : lam ≤ 1/2 := by dsimp [lam]; nlinarith
  obtain ⟨G, hg⟩ := finite_class_agnostic_potential F hu hne T (ENNReal.ofReal lam)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨xs, h, hx, ht, hh, hm⟩ := smf_generator_lower_bound (fun h => h ∈ F) hu hne T G
  have hw := hg xs hx ht h hh
  rw [← realWeight_ofReal lam hlam.le hlamhalf h (G.play xs)] at hw
  have hreal : realWeight lam h (G.play xs) ≤ (F.card : ℝ) := by exact_mod_cast hw
  have hpos := realWeight_pos lam hlam.le hlamhalf h (G.play xs)
  have hlog := Real.log_le_log hpos hreal
  have hlower := log_weight_lower lam hlam.le hlamhalf h (G.play xs)
  have hlen : (G.play xs).length = T := by
    have := congrArg List.length (G.demonstrations_play xs)
    simpa [demonstrations, ht] using this
  rw [hlen] at hlower
  have hmi : (SMF (fun h => h ∈ F) T : ℝ) ≤ (regret h (G.play xs) : ℝ) := by exact_mod_cast hm
  have hbound : lam*(SMF (fun h => h ∈ F) T : ℝ) ≤ Real.log (F.card : ℝ)+lam^2*(T : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hmi hlam.le]
  rw [Real.logb]
  calc
    (SMF (fun h => h ∈ F) T : ℝ) ≤ (Real.log (F.card : ℝ)+lam^2*(T : ℝ))/lam :=
      (le_div_iff₀ hlam).mpr (by nlinarith [hbound])
    _ = Real.log (F.card : ℝ)/Real.log 2/η + lam*(T : ℝ) := by
      dsimp [lam]
      field_simp
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right
      (show lam ≤ η by dsimp [lam]; nlinarith) (Nat.cast_nonneg T)) _

/-- The manuscript's finite-class agnostic square-root bound. -/
theorem finite_class_agnostic_bound (F : Finset (Hypothesis X))
    (hu : UUS (fun h => h ∈ F)) (hne : F.Nonempty) (T : Nat) :
    (SMF (fun h => h ∈ F) T : ℝ) ≤ Real.sqrt (8*(T : ℝ)*Real.logb 2 (F.card : ℝ)) := by
  let A := Real.logb 2 (F.card : ℝ)
  have hcard : (1 : ℝ) ≤ F.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hA : 0 ≤ A := div_nonneg (Real.log_nonneg hcard) (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hb := optimize_regret (SMF (fun h => h ∈ F) T : ℝ) A (T : ℝ) hA (Nat.cast_nonneg T)
    (by exact_mod_cast smf_le_horizon (fun h => h ∈ F) T)
    (fun η hp hh => finite_class_agnostic_eta F hu hne T η hp hh)
  have hAT : 0 ≤ A*(T : ℝ) := mul_nonneg hA (Nat.cast_nonneg T)
  have h8 : 0 ≤ 8*(T : ℝ)*A := by positivity
  have hs := Real.sq_sqrt hAT
  have hs8 := Real.sq_sqrt h8
  have hp8 := Real.sqrt_nonneg (8*(T : ℝ)*A)
  have hp := Real.sqrt_nonneg (A*(T : ℝ))
  change _ ≤ Real.sqrt (8*(T : ℝ)*A)
  nlinarith

theorem finite_class_agnostic_sublinear (F : Finset (Hypothesis X))
    (hu : UUS (fun h => h ∈ F)) (hne : F.Nonempty) : NatSublinear (SMF (fun h => h ∈ F)) := by
  intro k
  let A := Real.logb 2 (F.card : ℝ)
  obtain ⟨N, hN⟩ := exists_nat_gt (8*(k : ℝ)^2*A)
  refine ⟨max 1 N, fun t ht => ?_⟩
  have htN : (N : ℝ) ≤ t := by exact_mod_cast (show N ≤ t by omega)
  have ht0 : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
  have hlim : 8*(k : ℝ)^2*A ≤ t := by linarith
  have hb := finite_class_agnostic_bound F hu hne t
  change (SMF (fun h => h ∈ F) t : ℝ) ≤ Real.sqrt (8*(t : ℝ)*A) at hb
  have hcard : (1 : ℝ) ≤ F.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hA : 0 ≤ A := div_nonneg (Real.log_nonneg hcard) (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hs := Real.sq_sqrt (show 0 ≤ 8*(t : ℝ)*A by positivity)
  have hsp := Real.sqrt_nonneg (8*(t : ℝ)*A)
  have hv0 : 0 ≤ (SMF (fun h => h ∈ F) t : ℝ) := Nat.cast_nonneg _
  have hv : (SMF (fun h => h ∈ F) t : ℝ)^2 ≤ 8*(t : ℝ)*A := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hv (sq_nonneg (k : ℝ))
  have htMul := mul_le_mul_of_nonneg_right hlim ht0
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hprod : (k : ℝ)*(SMF (fun h => h ∈ F) t : ℝ) ≤ t := by nlinarith
  exact_mod_cast hprod

theorem finite_class_agnostic_no_regret (F : Finset (Hypothesis X))
    (hu : UUS (fun h => h ∈ F)) (hne : F.Nonempty) : AgnosticNoRegret (fun h => h ∈ F) :=
  (agnostic_no_regret_iff _ hu hne).mpr (finite_class_agnostic_sublinear F hu hne)

theorem finite_class_agnostic_isLittleO (F : Finset (Hypothesis X))
    (hu : UUS (fun h => h ∈ F)) (hne : F.Nonempty) :
    Asymptotics.IsLittleO Filter.atTop (fun t => (SMF (fun h => h ∈ F) t : ℝ)) (fun t => (t : ℝ)) :=
  (natSublinear_iff_isLittleO _).mp (finite_class_agnostic_sublinear F hu hne)

end PredictionToGeneration
