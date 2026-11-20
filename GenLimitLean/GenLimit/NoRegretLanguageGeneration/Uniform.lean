import GenLimit.NoRegretLanguageGeneration.Plays

namespace PredictionToGeneration

/-- Arbitrarily branching well-founded forcing, with no common deadline. -/
inductive WellFoundedForces (bad : Trajectory X → Prop) : Trajectory X → Prop where
  | leaf {τ} : bad τ → WellFoundedForces bad τ
  | step {τ} (response : (z : X) → Fresh τ z → X)
      (legal : ∀ z hz, Fresh τ (response z hz))
      (children : ∀ z hz, WellFoundedForces bad ((z, response z hz) :: τ)) :
      WellFoundedForces bad τ

theorem wellFounded_safe_move (bad : Trajectory X → Prop) (τ : Trajectory X)
    (hn : ¬ WellFoundedForces bad τ) :
    ∃ z, Fresh τ z ∧ ∀ x, Fresh τ x → ¬ WellFoundedForces bad ((z,x)::τ) := by
  classical
  apply Classical.byContradiction
  intro h
  apply hn
  have children : ∀ z, Fresh τ z → ∃ x, Fresh τ x ∧ WellFoundedForces bad ((z,x)::τ) := by
    intro z hz
    apply Classical.byContradiction
    intro hx
    apply h
    exact ⟨z, hz, fun x hlegal hforce => hx ⟨x, hlegal, hforce⟩⟩
  exact .step (fun z hz => Classical.choose (children z hz))
    (fun z hz => (Classical.choose_spec (children z hz)).1)
    (fun z hz => (Classical.choose_spec (children z hz)).2)

theorem finite_forces_wellFounded (bad : Trajectory X → Prop) (n : Nat)
    (τ : Trajectory X) (hf : Forces bad n τ) : WellFoundedForces bad τ := by
  classical
  induction n generalizing τ with
  | zero => exact .leaf hf
  | succ n ih =>
    exact .step (fun z hz => Classical.choose (hf z hz))
      (fun z hz => (Classical.choose_spec (hf z hz)).1)
      (fun z hz => ih _ (Classical.choose_spec (hf z hz)).2)

def Generator.Safe (G : Generator X) (bad : Trajectory X → Prop) : Prop :=
  ∀ xs, xs.Nodup → ¬ bad (G.play xs)

private noncomputable def safeDecision (fallback : Generator X)
    (bad : Trajectory X → Prop) (τ : Trajectory X) : X := by
  classical
  exact if hn : ¬ WellFoundedForces bad τ then
    Classical.choose (wellFounded_safe_move bad τ hn)
  else fallback.output (demonstrations τ)

private theorem safeDecision_fresh (fallback : Generator X)
    (bad : Trajectory X → Prop) (τ : Trajectory X) :
    Fresh τ (safeDecision fallback bad τ) := by
  classical
  unfold safeDecision
  split
  · rename_i hn
    exact (Classical.choose_spec (wellFounded_safe_move bad τ hn)).1
  · exact fallback.fresh _

private theorem safeDecision_safe (fallback : Generator X)
    (bad : Trajectory X → Prop) (τ : Trajectory X)
    (hn : ¬ WellFoundedForces bad τ) (x : X) (hx : Fresh τ x) :
    ¬ WellFoundedForces bad ((safeDecision fallback bad τ, x)::τ) := by
  classical
  simpa [safeDecision, hn] using
    (Classical.choose_spec (wellFounded_safe_move bad τ hn)).2 x hx

private noncomputable def safeHistory (fallback : Generator X)
    (bad : Trajectory X → Prop) : List X → Trajectory X
  | [] => []
  | x::xs => (safeDecision fallback bad (safeHistory fallback bad xs), x) ::
      safeHistory fallback bad xs

private theorem safeHistory_demos (fallback : Generator X)
    (bad : Trajectory X → Prop) (xs : List X) :
    demonstrations (safeHistory fallback bad xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [safeHistory, demonstrations] using congrArg (List.cons x) ih

noncomputable def safeGenerator (fallback : Generator X)
    (bad : Trajectory X → Prop) : Generator X where
  output xs := safeDecision fallback bad (safeHistory fallback bad xs)
  fresh xs := by
    have := safeDecision_fresh fallback bad (safeHistory fallback bad xs)
    simpa [Fresh, safeHistory_demos] using this

private theorem safeGenerator_play (fallback : Generator X)
    (bad : Trajectory X → Prop) (xs : List X) :
    (safeGenerator fallback bad).play xs = safeHistory fallback bad xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (_, x) :: (safeGenerator fallback bad).play xs = (_, x) :: safeHistory fallback bad xs
    rw [ih]
    rfl

theorem safeGenerator_invariant (fallback : Generator X)
    (bad : Trajectory X → Prop) (hn : ¬ WellFoundedForces bad [])
    (xs : List X) (hx : xs.Nodup) :
    ¬ WellFoundedForces bad ((safeGenerator fallback bad).play xs) := by
  rw [safeGenerator_play]
  induction xs with
  | nil => exact hn
  | cons x xs ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hx
    apply safeDecision_safe fallback bad _ (ih hnodup)
    simpa [Fresh, safeHistory_demos] using hnot

theorem wellFounded_forcing_outcome (G : Generator X) (bad : Trajectory X → Prop)
    (τ : Trajectory X) (hf : WellFoundedForces bad τ) :
    ∀ xs, xs.Nodup → G.play xs = τ → ∃ ys, ys.Nodup ∧ bad (G.play ys) := by
  induction hf with
  | leaf hb => intro xs hx he; exact ⟨xs, hx, he ▸ hb⟩
  | @step τ response legal children ih =>
    intro xs hx he
    have hz : Fresh τ (G.output xs) := by
      rw [← he]
      simpa [Fresh, G.demonstrations_play] using G.fresh xs
    let x := response (G.output xs) hz
    have hnot : x ∉ xs := by
      have hl := legal (G.output xs) hz
      simpa [Fresh, ← he, G.demonstrations_play] using hl
    exact ih (G.output xs) hz (x::xs)
      (List.nodup_cons.mpr ⟨hnot, hx⟩) (by simp [Generator.play, he, x])

/-- Exact well-founded forcing / history-based anytime safety duality. -/
theorem not_wellFounded_iff_safe (fallback : Generator X) (bad : Trajectory X → Prop) :
    (¬ WellFoundedForces bad []) ↔ ∃ G : Generator X, G.Safe bad := by
  constructor
  · intro hn
    refine ⟨safeGenerator fallback bad, fun xs hx hb => ?_⟩
    exact safeGenerator_invariant fallback bad hn xs hx (.leaf hb)
  · rintro ⟨G, hs⟩ hf
    obtain ⟨xs, hx, hb⟩ := wellFounded_forcing_outcome G bad [] hf [] (by simp) rfl
    exact hs xs hx hb

noncomputable def uusGenerator (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) : Generator X where
  output xs := Classical.choose (hu (Classical.choose hne) (Classical.choose_spec hne) xs)
  fresh xs := (Classical.choose_spec
    (hu (Classical.choose hne) (Classical.choose_spec hne) xs)).1

/-- One generator bounds mistakes at every finite time. -/
def UniformMistakeBound (G : Generator X) (H : HypothesisClass X) (B : Nat) : Prop :=
  ∀ xs, xs.Nodup → ∀ h, H h → Realizes h (G.play xs) → mistakes h (G.play xs) ≤ B

/-- Threshold form of the uniform total-mistake characterization. -/
theorem realizable_uniform_characterization (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (B : Nat) :
    (¬ WellFoundedForces (RealizableBad H (B+1)) []) ↔
      ∃ G : Generator X, UniformMistakeBound G H B := by
  rw [not_wellFounded_iff_safe (uusGenerator H hu hne)]
  constructor
  · rintro ⟨G, hs⟩
    exact ⟨G, fun xs hx => (not_realizableBad_iff H B _).mp (hs xs hx)⟩
  · rintro ⟨G, hs⟩
    exact ⟨G, fun xs hx => (not_realizableBad_iff H B _).mpr (hs xs hx)⟩

/-- An infinite sequence represented by its nested finite histories, newest first.
This representation records freshness and positivity at every round. -/
structure PositiveContinuation (h : Hypothesis X) (initial : List X) where
  history : Nat → List X
  start : history 0 = initial
  step : ∀ n, ∃ x, x ∉ history n ∧ h x = true ∧ history (n+1) = x :: history n

private noncomputable def positiveHistories (H : HypothesisClass X) (hu : UUS H)
    (h : Hypothesis X) (hh : H h) (xs : List X) : Nat → List X
  | 0 => xs
  | n+1 => Classical.choose (hu h hh (positiveHistories H hu h hh xs n)) ::
      positiveHistories H hu h hh xs n

/-- UUS extends every finite prefix for arbitrarily many rounds, using one target. -/
noncomputable def positiveContinuation (H : HypothesisClass X) (hu : UUS H)
    (h : Hypothesis X) (hh : H h) (xs : List X) : PositiveContinuation h xs where
  history := positiveHistories H hu h hh xs
  start := rfl
  step _ := ⟨_, (Classical.choose_spec (hu h hh _)).1,
    (Classical.choose_spec (hu h hh _)).2, rfl⟩

private def PositiveContinuation.prepend {h : Hypothesis X} {xs : List X} {x : X}
    (C : PositiveContinuation h (x::xs)) (hx : x ∉ xs) (hp : h x = true) :
    PositiveContinuation h xs where
  history
    | 0 => xs
    | n+1 => C.history n
  start := rfl
  step
    | 0 => ⟨x, hx, hp, C.start⟩
    | n+1 => C.step n

theorem PositiveContinuation.nodup {h : Hypothesis X} {xs : List X}
    (C : PositiveContinuation h xs) (hx : xs.Nodup) (n : Nat) :
    (C.history n).Nodup := by
  induction n with
  | zero => simpa [C.start] using hx
  | succ n ih =>
    obtain ⟨x, hf, hp, he⟩ := C.step n
    rw [he]
    exact List.nodup_cons.mpr ⟨hf, ih⟩

theorem PositiveContinuation.realizes {h : Hypothesis X} {xs : List X}
    (C : PositiveContinuation h xs) (G : Generator X)
    (hr : Realizes h (G.play xs)) (n : Nat) : Realizes h (G.play (C.history n)) := by
  induction n with
  | zero => simpa [C.start] using hr
  | succ n ih =>
    obtain ⟨x, hf, hp, he⟩ := C.step n
    rw [he]
    exact ⟨hp, ih⟩

/-- Insert an arbitrary legal positive prefix before its infinite continuation. -/
theorem PositiveContinuation.embed {h : Hypothesis X} {xs : List X}
    (C : PositiveContinuation h xs) (G : Generator X)
    (hn : xs.Nodup) (hr : Realizes h (G.play xs)) :
    ∃ D : PositiveContinuation h [], ∀ n, D.history (xs.length+n) = C.history n := by
  induction xs with
  | nil => exact ⟨C, fun n => by simp⟩
  | cons x xs ih =>
    obtain ⟨hf, ht⟩ := List.nodup_cons.mp hn
    obtain ⟨hp, hr⟩ := hr
    let C' := C.prepend hf hp
    obtain ⟨D, hd⟩ := ih C' ht hr
    refine ⟨D, fun n => ?_⟩
    have he := hd (n+1)
    simpa [C', PositiveContinuation.prepend, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using he

/-- Total mistakes are bounded when all finite prefix sums on an infinite play are bounded. -/
def InfiniteMistakeBound (G : Generator X) (H : HypothesisClass X) (B : Nat) : Prop :=
  ∀ h, H h → ∀ C : PositiveContinuation h [], ∀ n,
    mistakes h (G.play (C.history n)) ≤ B

/-- Under UUS, infinite realizable plays and all finite realizable prefixes give the
same uniform bound. The reverse implication uses a single fixed target extension. -/
theorem uniform_iff_infinite (H : HypothesisClass X) (hu : UUS H)
    (G : Generator X) (B : Nat) :
    UniformMistakeBound G H B ↔ InfiniteMistakeBound G H B := by
  constructor
  · intro hb h hh C n
    exact hb _ (C.nodup (by simp) n) h hh (C.realizes G trivial n)
  · intro hb xs hn h hh hr
    let C := positiveContinuation H hu h hh xs
    obtain ⟨D, hd⟩ := C.embed G hn hr
    have he : D.history xs.length = xs := by
      simpa [C.start] using hd 0
    simpa [he] using hb h hh D xs.length

/-- Exact uniform total-mistake characterization over infinite realizable plays. -/
theorem realizable_infinite_characterization (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (B : Nat) :
    (¬ WellFoundedForces (RealizableBad H (B+1)) []) ↔
      ∃ G : Generator X, InfiniteMistakeBound G H B := by
  rw [realizable_uniform_characterization H hu hne]
  constructor
  · rintro ⟨G, hg⟩
    exact ⟨G, (uniform_iff_infinite H hu G B).mp hg⟩
  · rintro ⟨G, hg⟩
    exact ⟨G, (uniform_iff_infinite H hu G B).mpr hg⟩

theorem wellFounded_forces_mono {P Q : Trajectory X → Prop}
    (hpq : ∀ τ, P τ → Q τ) {τ : Trajectory X}
    (hf : WellFoundedForces P τ) : WellFoundedForces Q τ := by
  induction hf with
  | leaf hp => exact .leaf (hpq _ hp)
  | step response legal children ih => exact .step response legal ih

/-- Mistakes already incurred cannot be removed by a positive continuation. -/
theorem PositiveContinuation.mistakes_persist {h : Hypothesis X} {xs : List X}
    (C : PositiveContinuation h xs) (G : Generator X) (n : Nat) :
    mistakes h (G.play xs) ≤ mistakes h (G.play (C.history n)) := by
  induction n with
  | zero => simp [C.start]
  | succ n ih =>
    obtain ⟨x, hf, hp, he⟩ := C.step n
    rw [he]
    change _ ≤ loss h (G.output (C.history n)) + mistakes h (G.play (C.history n))
    omega

/-- A well-founded forcing witness defeats every generator on one infinite
realizable play, with one fixed target and all later prefix losses at least m. -/
theorem wellFounded_infinite_lower_bound (H : HypothesisClass X) (hu : UUS H)
    (m : Nat) (hf : WellFoundedForces (RealizableBad H m) []) (G : Generator X) :
    ∃ h, H h ∧ ∃ D : PositiveContinuation h [], ∃ T,
      ∀ n, m ≤ mistakes h (G.play (D.history (T+n))) := by
  obtain ⟨xs, hn, h, hh, hr, hm⟩ :=
    wellFounded_forcing_outcome G (RealizableBad H m) [] hf [] (by simp) rfl
  let C := positiveContinuation H hu h hh xs
  obtain ⟨D, hd⟩ := C.embed G hn hr
  refine ⟨h, hh, D, xs.length, fun n => ?_⟩
  rw [hd n]
  exact Nat.le_trans hm (C.mistakes_persist G n)

/-- The infinite value case: unbounded well-founded thresholds are equivalent
to every anytime generator having unbounded worst-case total mistakes. -/
theorem uniform_unbounded_characterization (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) :
    (∀ B, WellFoundedForces (RealizableBad H (B+1)) []) ↔
      ∀ G : Generator X, ∀ B, ¬ InfiniteMistakeBound G H B := by
  classical
  constructor
  · intro hf G B hb
    exact (realizable_infinite_characterization H hu hne B).mpr ⟨G, hb⟩ (hf B)
  · intro hall B
    apply Classical.byContradiction
    intro hn
    obtain ⟨G, hg⟩ := (realizable_infinite_characterization H hu hne B).mp hn
    exact hall G B hg

end PredictionToGeneration
