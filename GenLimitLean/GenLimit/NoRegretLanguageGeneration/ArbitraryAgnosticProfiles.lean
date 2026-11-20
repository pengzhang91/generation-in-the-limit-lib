import GenLimit.NoRegretLanguageGeneration.ArbitraryProfiles
import GenLimit.NoRegretLanguageGeneration.AnytimeAgnostic

namespace PredictionToGeneration.Blocks

/-- The same distinct-output block strategy controls signed regret for arbitrary
streams, since comparator demonstration loss is nonnegative. -/
theorem smf_upper (size capacity : Nat → Nat) (hpositive : ∀ n, 0 < size n)
    (n T : Nat) (hsize : 2 * T ≤ size n) : SMF (Class size capacity) T ≤ capacity n := by
  obtain ⟨s, hs⟩ := block_strategy size capacity n T hsize T [] (by simp) List.nodup_nil (by simp)
  have hr : Guarantees (fun τ => ∀ h, Class size capacity h → regret h τ ≤ (capacity n : Int)) s := by
    apply guarantees_mono s (hs := hs)
    intro τ ht h hh
    have hm := ht h hh
    unfold regret
    omega
  have hf := (agnostic_finite_characterization (Class size capacity) T (capacity n : Int)).mpr ⟨s,hr⟩
  by_contra hh
  have hforce := (smf_spec (Class size capacity) (uus size capacity hpositive) (nonempty_class size capacity) T).1
  apply hf
  apply forces_mono (n := T) (τ := []) (hf := hforce)
  rintro τ ⟨h,hh',hm⟩
  exact ⟨h,hh',by omega⟩

end PredictionToGeneration.Blocks

namespace PredictionToGeneration.ArbitraryProfiles

/-- The agnostic half uses precisely the same cofinite block class. -/
theorem agnostic_upper (f : Nat → Nat) (hmono : Monotone f) (T : Nat) (hT : 4 ≤ T) :
    SMF (H f) T ≤ f (8*T) := by
  let n := coveringBlock (2*T)
  have hs : 2*T ≤ size n := coveringBlock_spec _
  have hn : n ≠ 0 := by
    intro he
    simp [he,size] at hs
    omega
  have hp := below_coveringBlock (2*T) (n-1) (by dsimp [n]; omega)
  have he : n-1+1=n := by omega
  dsimp [size] at hp
  rw [he] at hp
  have hsize : size n ≤ 8*T := by
    simp only [size,Nat.pow_succ]
    omega
  exact Nat.le_trans (Blocks.smf_upper size (capacity f) size_positive n T hs) (hmono hsize)

/-- Full finite-horizon arbitrary agnostic profile theorem. -/
theorem arbitrary_agnostic_profile (f : Nat → Nat) (hmono : Monotone f)
    (hbound : ∀ t, 1 ≤ t → 1 ≤ f t ∧ f t ≤ t) :
    Countable {h // H f h} ∧ UUS (H f) ∧
      ∀ T, 4 ≤ T → f (T/4) ≤ MF (H f) T ∧
        MF (H f) T ≤ SMF (H f) T ∧ SMF (H f) T ≤ f (8*T) := by
  have hu := Blocks.uus size (capacity f) size_positive
  have hne := Blocks.nonempty_class size (capacity f)
  refine ⟨Blocks.countable_class size (capacity f),hu,?_⟩
  intro T hT
  exact ⟨lower f hmono (fun t ht => (hbound t ht).2) T hT,
    mf_le_smf (H f) hu hne T,agnostic_upper f hmono T hT⟩

end PredictionToGeneration.ArbitraryProfiles

namespace PredictionToGeneration.ArbitraryProfiles

theorem agnostic_no_regret (f : Nat → Nat) (hmono : Monotone f) (hf : NatSublinear f) :
    AgnosticNoRegret (H f) := by
  apply (agnostic_no_regret_iff (H f) (Blocks.uus size (capacity f) size_positive)
    (Blocks.nonempty_class size (capacity f))).mpr
  intro k
  obtain ⟨N,hN⟩ := hf (8*k)
  refine ⟨max 4 N,?_⟩
  intro t ht
  have hu := agnostic_upper f hmono t (by omega)
  have hc := Nat.mul_le_mul_left k hu
  have hs := hN (8*t) (by omega)
  rw [Nat.mul_assoc] at hs
  omega

theorem agnostic_theta_of_rescaling (f : Nat → Nat) (hmono : Monotone f)
    (hbound : ∀ t, 1 ≤ t → f t ≤ t)
    (hstable : ∃ C N : Nat, ∀ t, N ≤ t → f (8*t) ≤ C*f t) :
    (fun t : Nat => (SMF (H f) t : ℝ)) =Θ[Filter.atTop] (fun t : Nat => (f t : ℝ)) := by
  obtain ⟨C,N,hC⟩ := hstable
  have hu := Blocks.uus size (capacity f) size_positive
  have hne := Blocks.nonempty_class size (capacity f)
  constructor
  · apply Asymptotics.IsBigO.of_bound (C : ℝ)
    apply Filter.eventually_atTop.mpr
    refine ⟨max 4 N,?_⟩
    intro t ht
    have hb := agnostic_upper f hmono t (by omega)
    have hc := hC t (by omega)
    simp only [Real.norm_natCast]
    exact_mod_cast Nat.le_trans hb hc
  · apply Asymptotics.IsBigO.of_bound (C : ℝ)
    apply Filter.eventually_atTop.mpr
    refine ⟨max 4 (4*N),?_⟩
    intro t ht
    have hlo := Nat.le_trans (lower f hmono hbound t (by omega)) (mf_le_smf (H f) hu hne t)
    have hmono' := hmono (show t ≤ 8*(t/4) by omega)
    have hc := hC (t/4) (by omega)
    have hm := Nat.mul_le_mul_left C hlo
    simp only [Real.norm_natCast]
    exact_mod_cast Nat.le_trans hmono' (Nat.le_trans hc hm)

end PredictionToGeneration.ArbitraryProfiles

