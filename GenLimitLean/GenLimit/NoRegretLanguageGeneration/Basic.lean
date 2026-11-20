import Std

/-!
# The generation game

Source: paper/Manuscript/1main.tex, definitions in Section 2.
Trajectories and demonstration histories are stored newest round first.
Only past demonstrations are forbidden; outputs can repeat and the current
demonstration can equal the current output. No label feedback is supplied.
-/

namespace PredictionToGeneration

abbrev Hypothesis (X : Type) := X → Bool
abbrev HypothesisClass (X : Type) := Hypothesis X → Prop
abbrev Trajectory (X : Type) := List (X × X)

def demonstrations (τ : Trajectory X) : List X := τ.map Prod.snd

def Fresh (τ : Trajectory X) (x : X) : Prop := x ∉ demonstrations τ

def Legal : Trajectory X → Prop
  | [] => True
  | (z, x) :: τ => Legal τ ∧ Fresh τ z ∧ Fresh τ x

/-- The finite-avoidance formulation of infinite support. -/
def UUS (H : HypothesisClass X) : Prop :=
  ∀ h, H h → ∀ seen : List X, ∃ x, x ∉ seen ∧ h x = true

def Realizes (h : Hypothesis X) : Trajectory X → Prop
  | [] => True
  | (_, x) :: τ => h x = true ∧ Realizes h τ

def VersionSpace (H : HypothesisClass X) (τ : Trajectory X) : HypothesisClass X :=
  fun h => H h ∧ Realizes h τ

def loss (h : Hypothesis X) (x : X) : Nat := if h x then 0 else 1

def mistakes (h : Hypothesis X) : Trajectory X → Nat
  | [] => 0
  | (z, _) :: τ => loss h z + mistakes h τ

def demonstrationLoss (h : Hypothesis X) : Trajectory X → Nat
  | [] => 0
  | (_, x) :: τ => loss h x + demonstrationLoss h τ

/-- Integer subtraction is essential: regret can be negative. -/
def regret (h : Hypothesis X) (τ : Trajectory X) : Int :=
  (mistakes h τ : Int) - (demonstrationLoss h τ : Int)

theorem loss_le_one (h : Hypothesis X) (x : X) : loss h x ≤ 1 := by
  unfold loss
  cases h x <;> decide

theorem loss_of_positive (h : Hypothesis X) (x : X) (hx : h x = true) :
    loss h x = 0 := by simp [loss, hx]

theorem mistakes_le_length (h : Hypothesis X) (τ : Trajectory X) :
    mistakes h τ ≤ τ.length := by
  induction τ with
  | nil => simp [mistakes]
  | cons p τ ih =>
    have := loss_le_one h p.1
    simp only [mistakes, List.length_cons]
    omega

theorem demonstrationLoss_le_length (h : Hypothesis X) (τ : Trajectory X) :
    demonstrationLoss h τ ≤ τ.length := by
  induction τ with
  | nil => simp [demonstrationLoss]
  | cons p τ ih =>
    have := loss_le_one h p.2
    simp only [demonstrationLoss, List.length_cons]
    omega

theorem regret_bounds (h : Hypothesis X) (τ : Trajectory X) :
    -(τ.length : Int) ≤ regret h τ ∧ regret h τ ≤ (τ.length : Int) := by
  have := mistakes_le_length h τ
  have := demonstrationLoss_le_length h τ
  unfold regret
  omega

theorem regret_cons (h : Hypothesis X) (z x : X) (τ : Trajectory X) :
    regret h ((z, x) :: τ) = regret h τ + (loss h z : Int) - (loss h x : Int) := by
  simp [regret, mistakes, demonstrationLoss]
  omega

theorem regret_copy (h : Hypothesis X) (x : X) (τ : Trajectory X) :
    regret h ((x, x) :: τ) = regret h τ := by
  rw [regret_cons]
  omega

theorem demonstrationLoss_eq_zero (h : Hypothesis X) (τ : Trajectory X)
    (hr : Realizes h τ) : demonstrationLoss h τ = 0 := by
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    obtain ⟨hx, ht⟩ := hr
    simp [demonstrationLoss, loss_of_positive h p.2 hx, ih ht]

theorem regret_eq_mistakes (h : Hypothesis X) (τ : Trajectory X)
    (hr : Realizes h τ) : regret h τ = (mistakes h τ : Int) := by
  simp [regret, demonstrationLoss_eq_zero h τ hr]

/-- Proposition `prop:agnostic-contamination-transfer`, finite-horizon inequality. -/
theorem contamination_transfer (h : Hypothesis X) (τ : Trajectory X) (r : Int)
    (hr : regret h τ ≤ r) :
    (mistakes h τ : Int) ≤ r + (demonstrationLoss h τ : Int) := by
  unfold regret at hr
  omega

theorem fresh_positive (H : HypothesisClass X) (hu : UUS H)
    (h : Hypothesis X) (hh : H h) (τ : Trajectory X) :
    ∃ x, Fresh τ x ∧ h x = true := hu h hh (demonstrations τ)

theorem realizable_extension (H : HypothesisClass X) (hu : UUS H)
    (h : Hypothesis X) (hh : H h) (τ : Trajectory X)
    (hl : Legal τ) (hr : Realizes h τ) (z : X) (hz : Fresh τ z) :
    ∃ x, Legal ((z, x) :: τ) ∧ Realizes h ((z, x) :: τ) := by
  obtain ⟨x, hx, hp⟩ := fresh_positive H hu h hh τ
  exact ⟨x, ⟨hl, hz, hx⟩, hp, hr⟩

/-- Strongly total on all finite histories; only distinct histories are played. -/
structure Generator (X : Type) where
  output : List X → X
  fresh : ∀ xs, output xs ∉ xs

def Generator.play (G : Generator X) : List X → Trajectory X
  | [] => []
  | x :: xs => (G.output xs, x) :: G.play xs

theorem Generator.demonstrations_play (G : Generator X) (xs : List X) :
    demonstrations (G.play xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Generator.play, demonstrations] at ih ⊢; exact ih

theorem Generator.play_legal (G : Generator X) (xs : List X) (hx : xs.Nodup) :
    Legal (G.play xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hx
    exact ⟨ih hnodup, by simpa [Fresh, G.demonstrations_play] using G.fresh xs,
      by simpa [Fresh, G.demonstrations_play] using hnot⟩

end PredictionToGeneration
