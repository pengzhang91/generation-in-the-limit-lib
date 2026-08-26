import GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity

/-!
# #23 Nice window schedules

Claim 4.4, repeated as Appendix Claim 7.1. The source uses one-based finite
sequences; the definition below is its zero-based translation.
-/

namespace GenLimit.KleinbergWei.Banach

/-- The four conditions defining a nice function. -/
def Nice (f : ℕ → ℕ) : Prop :=
  ∀ T : ℕ, ∃ m : ℕ, ∃ k a : ℕ → ℕ,
    2 ≤ m ∧
      (∀ i j, i < m → j < m → i ≤ j → k i ≤ k j) ∧
      (∀ i j, i < m → j < m → i < j → a i < a j) ∧
      T < a 0 ∧
      (∀ i : ℕ, i + 1 < m → a i + k i + 1 ≤ a (i + 1)) ∧
      ∀ i : ℕ, i < m → a i ≤ f (k i)

/-- Pointwise absence of a universal finite upper bound. -/
def UniversallyUnbounded (f : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ n : ℕ, M < f n

theorem nice_universallyUnbounded
    {f : ℕ → ℕ} (hnice : Nice f) :
    UniversallyUnbounded f := by
  intro M
  obtain ⟨m, k, a, hm, _hk, _ha, hM, _hspace, hbound⟩ := hnice M
  exact ⟨k 0, hM.trans_le (hbound 0 (by omega))⟩

theorem universallyUnbounded_nice
    {f : ℕ → ℕ} (hmono : Monotone f)
    (hunbounded : UniversallyUnbounded f) :
    Nice f := by
  intro T
  obtain ⟨k₀, hk₀⟩ := hunbounded T
  let a₀ := f k₀
  let a₁ := a₀ + k₀ + 1
  obtain ⟨k', hk'⟩ := hunbounded a₁
  let k₁ := max k₀ k'
  have hk₀k₁ : k₀ ≤ k₁ := Nat.le_max_left _ _
  have hk'k₁ : k' ≤ k₁ := Nat.le_max_right _ _
  have ha₁fk₁ : a₁ ≤ f k₁ :=
    (Nat.le_of_lt hk').trans (hmono hk'k₁)
  let k : ℕ → ℕ := fun i => if i = 0 then k₀ else k₁
  let a : ℕ → ℕ := fun i => if i = 0 then a₀ else a₁
  refine ⟨2, k, a, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;>
      rcases hj' with rfl | rfl <;>
      simp_all [k]
  · intro i j hi hj hij
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;>
      rcases hj' with rfl | rfl <;>
      simp_all [a, a₁]
    all_goals omega
  · simpa [a, a₀] using hk₀
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp [a, k, a₁]
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · simp [a, k, a₀]
    · simpa [a, k] using ha₁fk₁

/-- Claim 4.4. -/
theorem claim_4_4
    {f : ℕ → ℕ} (hmono : Monotone f) :
    Nice f ↔ UniversallyUnbounded f :=
  ⟨nice_universallyUnbounded, universallyUnbounded_nice hmono⟩

/-- Appendix Claim 7.1. -/
theorem claim_7_1
    {f : ℕ → ℕ} (hmono : Monotone f) :
    Nice f ↔ UniversallyUnbounded f :=
  claim_4_4 hmono

end GenLimit.KleinbergWei.Banach
