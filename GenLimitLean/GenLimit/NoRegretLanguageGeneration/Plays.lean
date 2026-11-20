import GenLimit.NoRegretLanguageGeneration.Forcing

namespace PredictionToGeneration

/-- Terminal trajectories reachable by legal adversarial responses. -/
def Outcome : {n : Nat} → {τ : Trajectory X} → Strategy X n τ → Trajectory X → Prop
  | 0, τ, .done _, leaf => leaf = τ
  | _ + 1, _, .step _ _ next, leaf => ∃ x hx, Outcome (next x hx) leaf

theorem guarantees_iff_outcomes (P : Trajectory X → Prop) {n : Nat}
    {τ : Trajectory X} (s : Strategy X n τ) :
    Guarantees P s ↔ ∀ leaf, Outcome s leaf → P leaf := by
  induction s with
  | done τ => simp [Guarantees, Outcome]
  | step z hz next ih =>
    constructor
    · intro hg leaf ⟨x, hx, ho⟩
      exact (ih x hx).mp (hg x hx) leaf ho
    · intro hg x hx
      exact (ih x hx).mpr (fun leaf ho => hg leaf ⟨x, hx, ho⟩)

theorem outcome_length {n : Nat} {τ : Trajectory X} (s : Strategy X n τ)
    (leaf : Trajectory X) (ho : Outcome s leaf) : leaf.length = τ.length + n := by
  induction s with
  | done τ => change leaf = τ at ho; subst leaf; simp
  | @step n τ z hz next ih =>
    obtain ⟨x, hx, ht⟩ := ho
    have hl := ih x hx ht
    simp only [List.length_cons] at hl
    omega

theorem outcome_legal {n : Nat} {τ : Trajectory X} (s : Strategy X n τ)
    (hl : Legal τ) (leaf : Trajectory X) (ho : Outcome s leaf) : Legal leaf := by
  induction s with
  | done τ => change leaf = τ at ho; subst leaf; exact hl
  | step z hz next ih =>
    obtain ⟨x, hx, ht⟩ := ho
    exact ih x hx ⟨hl, hz, hx⟩ ht

/-- A forcing tree defeats each fixed strategy with one complete terminal witness. -/
theorem forcing_outcome (bad : Trajectory X → Prop) {n : Nat}
    {τ : Trajectory X} (s : Strategy X n τ) (hf : Forces bad n τ) :
    ∃ leaf, Outcome s leaf ∧ bad leaf := by
  induction s with
  | done τ => exact ⟨τ, rfl, hf⟩
  | step z hz next ih =>
    obtain ⟨x, hx, ht⟩ := hf z hz
    obtain ⟨leaf, ho, hb⟩ := ih x hx ht
    exact ⟨leaf, ⟨x, hx, ho⟩, hb⟩

/-- Lower-bound half with explicit legal trajectory, length, and single target. -/
theorem realizable_lower_bound (H : HypothesisClass X) (T m : Nat)
    (hf : MFForces H T m) (s : Strategy X T []) :
    ∃ leaf h, Outcome s leaf ∧ Legal leaf ∧ leaf.length = T ∧
      H h ∧ Realizes h leaf ∧ m ≤ mistakes h leaf := by
  obtain ⟨leaf, ho, h, hh, hr, hm⟩ := forcing_outcome _ s hf
  exact ⟨leaf, h, ho, outcome_legal s trivial leaf ho,
    by simpa using outcome_length s leaf ho, hh, hr, hm⟩

theorem agnostic_lower_bound (H : HypothesisClass X) (T : Nat) (m : Int)
    (hf : SMFForces H T m) (s : Strategy X T []) :
    ∃ leaf h, Outcome s leaf ∧ Legal leaf ∧ leaf.length = T ∧
      H h ∧ m ≤ regret h leaf := by
  obtain ⟨leaf, ho, h, hh, hm⟩ := forcing_outcome _ s hf
  exact ⟨leaf, h, ho, outcome_legal s trivial leaf ho,
    by simpa using outcome_length s leaf ho, hh, hm⟩

/-- An anytime generator induces a finite strategy without accessing validity labels. -/
def Generator.strategy (G : Generator X) : (n : Nat) → (τ : Trajectory X) → Strategy X n τ
  | 0, τ => .done τ
  | n + 1, τ => .step (G.output (demonstrations τ)) (G.fresh (demonstrations τ))
      (fun x _ => G.strategy n ((G.output (demonstrations τ), x) :: τ))

/-- Every outcome of the induced strategy agrees with the original generator. -/
theorem Generator.strategy_consistent (G : Generator X) (n : Nat) (τ : Trajectory X)
    (hc : G.play (demonstrations τ) = τ) (leaf : Trajectory X)
    (ho : Outcome (G.strategy n τ) leaf) : G.play (demonstrations leaf) = leaf := by
  induction n generalizing τ with
  | zero => simpa [Generator.strategy, Outcome] using ho ▸ hc
  | succ n ih =>
    obtain ⟨x, hx, ht⟩ := ho
    apply ih _ _ ht
    simp only [demonstrations, List.map_cons, Generator.play]
    exact congrArg (List.cons (G.output (demonstrations τ), x)) hc

theorem agnostic_guarantee_implies_realizable (H : HypothesisClass X) (T B : Nat)
    (s : Strategy X T [])
    (hs : Guarantees (fun τ => ∀ h, H h → regret h τ ≤ (B : Int)) s) :
    Guarantees (fun τ => ∀ h, H h → Realizes h τ → mistakes h τ ≤ B) s := by
  apply guarantees_mono s (hs := hs)
  intro τ hb h hh hr
  have ht := hb h hh
  rw [regret_eq_mistakes h τ hr] at ht
  omega

end PredictionToGeneration


