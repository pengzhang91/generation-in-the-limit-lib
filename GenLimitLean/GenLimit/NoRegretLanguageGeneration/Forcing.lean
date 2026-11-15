import GenLimit.NoRegretLanguageGeneration.Basic

/-!
# Finite-horizon forcing and safe strategies

The recursive forcing predicate is a generator-complete adversarial tree:
for every legal output there is a legal response with a forcing subtree.
It permits arbitrary (including infinite) branching and places a single
comparator witness at each terminal trajectory, never one per round.
-/

namespace PredictionToGeneration

def Forces (bad : Trajectory X → Prop) : Nat → Trajectory X → Prop
  | 0, τ => bad τ
  | n + 1, τ => ∀ z, Fresh τ z → ∃ x, Fresh τ x ∧ Forces bad n ((z, x) :: τ)

/-- A finite deterministic strategy, with legal outputs built into its type.
The continuation sees only the revealed example, not the hypothesis or loss. -/
inductive Strategy (X : Type) : Nat → Trajectory X → Type where
  | done (τ) : Strategy X 0 τ
  | step {n τ} (z : X) (hz : Fresh τ z)
      (next : (x : X) → Fresh τ x → Strategy X n ((z, x) :: τ)) :
      Strategy X (n + 1) τ

def Guarantees (good : Trajectory X → Prop) : {n : Nat} → {τ : Trajectory X} →
    Strategy X n τ → Prop
  | 0, τ, .done _ => good τ
  | _ + 1, _, .step _ _ next => ∀ x hx, Guarantees good (next x hx)

theorem safe_move (bad : Trajectory X → Prop) (n : Nat) (τ : Trajectory X)
    (hn : ¬ Forces bad (n + 1) τ) :
    ∃ z, Fresh τ z ∧ ∀ x, Fresh τ x → ¬ Forces bad n ((z, x) :: τ) := by
  classical
  apply Classical.byContradiction
  intro h
  apply hn
  intro z hz
  apply Classical.byContradiction
  intro hx
  apply h
  refine ⟨z, hz, ?_⟩
  intro x hlegal hforce
  exact hx ⟨x, hlegal, hforce⟩

theorem forcing_excludes_safe (bad : Trajectory X → Prop) {n : Nat}
    {τ : Trajectory X} (s : Strategy X n τ) (hf : Forces bad n τ) :
    ¬ Guarantees (fun t => ¬ bad t) s := by
  induction s with
  | done τ => exact fun h => h hf
  | step z hz next ih =>
    obtain ⟨x, hx, hforce⟩ := hf z hz
    intro hs
    exact ih x hx hforce (hs x hx)

/-- The safe-strategy construction in both finite-horizon characterization proofs. -/
theorem not_forcing_iff_safe (bad : Trajectory X → Prop) (n : Nat)
    (τ : Trajectory X) :
    (¬ Forces bad n τ) ↔
      ∃ s : Strategy X n τ, Guarantees (fun t => ¬ bad t) s := by
  classical
  constructor
  · induction n generalizing τ with
    | zero => intro h; exact ⟨.done τ, h⟩
    | succ n ih =>
      intro h
      obtain ⟨z, hz, hs⟩ := safe_move bad n τ h
      have children := fun x hx => ih ((z, x) :: τ) (hs x hx)
      refine ⟨.step z hz (fun x hx => Classical.choose (children x hx)), ?_⟩
      intro x hx
      exact Classical.choose_spec (children x hx)
  · rintro ⟨s, hs⟩ hf
    exact forcing_excludes_safe bad s hf hs

theorem guarantees_mono {P Q : Trajectory X → Prop} {n : Nat} {τ : Trajectory X}
    (s : Strategy X n τ) (hpq : ∀ t, P t → Q t) (hs : Guarantees P s) :
    Guarantees Q s := by
  induction s with
  | done τ => exact hpq τ hs
  | step z hz next ih => exact fun x hx => ih x hx (hs x hx)

theorem forces_mono {P Q : Trajectory X → Prop} (hpq : ∀ t, P t → Q t)
    (n : Nat) (τ : Trajectory X) (hf : Forces P n τ) : Forces Q n τ := by
  induction n generalizing τ with
  | zero => exact hpq τ hf
  | succ n ih =>
    intro z hz
    obtain ⟨x, hx, ht⟩ := hf z hz
    exact ⟨x, hx, ih _ ht⟩

def RealizableBad (H : HypothesisClass X) (m : Nat) (τ : Trajectory X) : Prop :=
  ∃ h, H h ∧ Realizes h τ ∧ m ≤ mistakes h τ

def SignedBad (H : HypothesisClass X) (m : Int) (τ : Trajectory X) : Prop :=
  ∃ h, H h ∧ m ≤ regret h τ

abbrev MFForces (H : HypothesisClass X) (T m : Nat) :=
  Forces (RealizableBad H m) T []

abbrev SMFForces (H : HypothesisClass X) (T : Nat) (m : Int) :=
  Forces (SignedBad H m) T []

theorem not_realizableBad_iff (H : HypothesisClass X) (B : Nat) (τ : Trajectory X) :
    (¬ RealizableBad H (B + 1) τ) ↔
      ∀ h, H h → Realizes h τ → mistakes h τ ≤ B := by
  constructor
  · intro hn h hh hr
    have : ¬ B + 1 ≤ mistakes h τ := fun hm => hn ⟨h, hh, hr, hm⟩
    omega
  · intro hb ⟨h, hh, hr, hm⟩
    have := hb h hh hr
    omega

theorem not_signedBad_iff (H : HypothesisClass X) (B : Int) (τ : Trajectory X) :
    (¬ SignedBad H (B + 1) τ) ↔ ∀ h, H h → regret h τ ≤ B := by
  constructor
  · intro hn h hh
    have : ¬ B + 1 ≤ regret h τ := fun hm => hn ⟨h, hh, hm⟩
    omega
  · intro hb ⟨h, hh, hm⟩
    have := hb h hh
    omega

/-- Exact threshold form of `thm:mf-finite-characterization`. -/
theorem realizable_finite_characterization (H : HypothesisClass X) (T B : Nat) :
    (¬ MFForces H T (B + 1)) ↔
      ∃ s : Strategy X T [], Guarantees
        (fun τ => ∀ h, H h → Realizes h τ → mistakes h τ ≤ B) s := by
  rw [not_forcing_iff_safe]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, guarantees_mono s (fun τ => (not_realizableBad_iff H B τ).mp) hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, guarantees_mono s (fun τ => (not_realizableBad_iff H B τ).mpr) hs⟩

/-- Exact threshold form of `thm:smf-characterization`, including negative bounds. -/
theorem agnostic_finite_characterization (H : HypothesisClass X) (T : Nat) (B : Int) :
    (¬ SMFForces H T (B + 1)) ↔
      ∃ s : Strategy X T [], Guarantees
        (fun τ => ∀ h, H h → regret h τ ≤ B) s := by
  rw [not_forcing_iff_safe]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, guarantees_mono s (fun τ => (not_signedBad_iff H B τ).mp) hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, guarantees_mono s (fun τ => (not_signedBad_iff H B τ).mpr) hs⟩

theorem realizable_forcing_implies_signed (H : HypothesisClass X) (T m : Nat)
    (hf : MFForces H T m) : SMFForces H T (m : Int) := by
  apply forces_mono (n := T) (τ := []) (hf := hf)
  intro τ ⟨h, hh, hr, hm⟩
  refine ⟨h, hh, ?_⟩
  rw [regret_eq_mistakes h τ hr]
  omega

end PredictionToGeneration
