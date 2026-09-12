import GenLimit.Paper22_LanguageGenerationWithReplay.Uniform

/-!
# Proper generation in the limit with replay

Source: Giorgio Racca, Michal Valko, and Amartya Sanyal,
*Language Generation with Replay: A Learning-Theoretic View of Model
Collapse*, arXiv:2603.11784v2, Definition 3.5 and Theorem 7.3.

The source's hard class consists of four languages over `ℤ`.  After the
common first example `0`, the adversary uses the first output hypothesis to
choose one of two streams.  Either stream is simultaneously an enumeration
with replay for two targets, but no member of the four-language class is
contained in both targets.
-/

namespace GenLimit
namespace Replay

open GenLimit.Generic

/-- A proper generator selects an index for one member of its fixed family. -/
abbrev ProperGenerator (ι α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → ι

/-- Run a proper generator on the prefix strictly before time `t`. -/
def properOutput
    (gen : ProperGenerator ι α) (stream : Generic.Stream α)
    (t : ℕ) : ι :=
  gen t (fun i => stream i)

/-- Definition 3.5's replay legality condition, with zero-based input
indices.  An output made after `k` examples may be replayed at input index
`n` exactly when `0 < k ≤ n`. -/
def IsProperReplaySequence
    (family : ι → Generic.Language α)
    (gen : ProperGenerator ι α) (target : ι)
    (stream : Generic.Stream α) : Prop :=
  ∀ n, stream n ∈ family target ∨
    ∃ k, 0 < k ∧ k ≤ n ∧
      stream n ∈ family (properOutput gen stream k)

/-- Definition 3.5's full input condition: replay legality together with
eventual revelation of every target element. -/
def IsProperReplayEnumeration
    (family : ι → Generic.Language α)
    (gen : ProperGenerator ι α) (target : ι)
    (stream : Generic.Stream α) : Prop :=
  IsProperReplaySequence family gen target stream ∧
    ∀ x, x ∈ family target → ∃ n, stream n = x

/-- Proper correctness at time `t`: the selected family member is contained
in the target language. -/
def ProperCorrectAt
    (family : ι → Generic.Language α)
    (gen : ProperGenerator ι α) (target : ι)
    (stream : Generic.Stream α) (t : ℕ) : Prop :=
  family (properOutput gen stream t) ⊆ family target

/-- A fixed proper generator succeeds in the limit against replay. -/
def IsProperLimitReplayGenerator
    (family : ι → Generic.Language α)
    (gen : ProperGenerator ι α) : Prop :=
  ∀ target stream, IsProperReplayEnumeration family gen target stream →
    ∃ T, ∀ t, T ≤ t → ProperCorrectAt family gen target stream t

/-- Definition 3.5 for an indexed hypothesis family. -/
def ProperlyGeneratableInLimitWithReplay
    (family : ι → Generic.Language α) : Prop :=
  ∃ gen : ProperGenerator ι α,
    IsProperLimitReplayGenerator family gen

/-- Reusable two-target obstruction: if one stream is a replay enumeration
of two targets but the family has no member contained in their intersection,
then the fixed generator cannot succeed. -/
theorem twoTarget_replay_obstruction
    {family : ι → Generic.Language α}
    (gen : ProperGenerator ι α) {left right : ι}
    {stream : Generic.Stream α}
    (hleft :
      IsProperReplayEnumeration family gen left stream)
    (hright :
      IsProperReplayEnumeration family gen right stream)
    (hnoCommon :
      ∀ i, ¬(family i ⊆ family left ∧ family i ⊆ family right)) :
    ¬IsProperLimitReplayGenerator family gen := by
  intro hgen
  obtain ⟨leftTime, hleftTime⟩ := hgen left stream hleft
  obtain ⟨rightTime, hrightTime⟩ := hgen right stream hright
  let commonTime := max leftTime rightTime
  exact hnoCommon (properOutput gen stream commonTime)
    ⟨hleftTime commonTime (le_max_left _ _),
      hrightTime commonTime (le_max_right _ _)⟩

/-- Names for the four hypotheses in Theorem 7.3. -/
inductive HardHypothesis
  | minusOne
  | minusTwo
  | plusOne
  | plusTwo
  deriving DecidableEq

instance : Fintype HardHypothesis where
  elems :=
    {.minusOne, .minusTwo, .plusOne, .plusTwo}
  complete := by
    intro i
    cases i <;> simp

/-- The source's literal four-language class:
`hᵢ⁻ = ℤ≤0 ∪ {i}` and `hᵢ⁺ = ℤ≥0 ∪ {-i}` for `i = 1, 2`. -/
def properReplayHardFamily :
    HardHypothesis → Generic.Language ℤ
  | .minusOne => {z | z ≤ 0 ∨ z = 1}
  | .minusTwo => {z | z ≤ 0 ∨ z = 2}
  | .plusOne => {z | 0 ≤ z ∨ z = -1}
  | .plusTwo => {z | 0 ≤ z ∨ z = -2}

theorem properReplayHardFamily_card :
    Fintype.card HardHypothesis = 4 := by
  decide

/-- Every member of the source's hard class has infinite support, as required
by the paper's standing UUS convention. -/
theorem properReplayHardFamily_infinite
    (i : HardHypothesis) :
    (properReplayHardFamily i).Infinite := by
  cases i with
  | minusOne =>
      have hrange :
          Set.range (fun n : ℕ => -((n : ℤ) + 1)) ⊆
            properReplayHardFamily .minusOne := by
        rintro _ ⟨n, rfl⟩
        change -((n : ℤ) + 1) ≤ 0 ∨ -((n : ℤ) + 1) = 1
        exact Or.inl (by omega)
      exact
        (Set.infinite_range_of_injective
          (fun _ _ h => by omega)).mono hrange
  | minusTwo =>
      have hrange :
          Set.range (fun n : ℕ => -((n : ℤ) + 1)) ⊆
            properReplayHardFamily .minusTwo := by
        rintro _ ⟨n, rfl⟩
        change -((n : ℤ) + 1) ≤ 0 ∨ -((n : ℤ) + 1) = 2
        exact Or.inl (by omega)
      exact
        (Set.infinite_range_of_injective
          (fun _ _ h => by omega)).mono hrange
  | plusOne =>
      have hrange :
          Set.range (fun n : ℕ => (n : ℤ)) ⊆
            properReplayHardFamily .plusOne := by
        rintro _ ⟨n, rfl⟩
        simp [properReplayHardFamily]
      exact
        (Set.infinite_range_of_injective
          (fun _ _ h => by omega)).mono hrange
  | plusTwo =>
      have hrange :
          Set.range (fun n : ℕ => (n : ℤ)) ⊆
            properReplayHardFamily .plusTwo := by
        rintro _ ⟨n, rfl⟩
        simp [properReplayHardFamily]
      exact
        (Set.infinite_range_of_injective
          (fun _ _ h => by omega)).mono hrange

/-- The paper's stream `0,-1,-2,1,2,...`, used after a negative-half-line
hypothesis is selected at the first round. -/
def positiveChallengeStream : Generic.Stream ℤ
  | 0 => 0
  | 1 => -1
  | 2 => -2
  | n + 3 => n + 1

/-- The sign-reversed stream `0,1,2,-1,-2,...`. -/
def negativeChallengeStream : Generic.Stream ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => -(n + 1)

/-- Every nonnegative integer occurs in the positive challenge stream. -/
theorem exists_positiveChallengeStream_eq_of_nonneg
    {z : ℤ} (hz : 0 ≤ z) :
    ∃ n, positiveChallengeStream n = z := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  cases n with
  | zero =>
      exact ⟨0, rfl⟩
  | succ n =>
      exact ⟨n + 3, by simp [positiveChallengeStream]⟩

/-- Every nonpositive integer occurs in the negative challenge stream. -/
theorem exists_negativeChallengeStream_eq_of_nonpos
    {z : ℤ} (hz : z ≤ 0) :
    ∃ n, negativeChallengeStream n = z := by
  by_cases hzero : z = 0
  · subst z
    exact ⟨0, rfl⟩
  · obtain ⟨n, rfl⟩ :=
      Int.eq_negSucc_of_lt_zero (lt_of_le_of_ne hz hzero)
    exact ⟨n + 3, by simp [negativeChallengeStream]; omega⟩

/-- Every element of `h₁⁺` occurs in the positive challenge stream. -/
theorem positiveChallengeStream_covers_plusOne :
    ∀ z, z ∈ properReplayHardFamily .plusOne →
      ∃ n, positiveChallengeStream n = z := by
  intro z hz
  change 0 ≤ z ∨ z = -1 at hz
  rcases hz with hz | rfl
  · exact exists_positiveChallengeStream_eq_of_nonneg hz
  · exact ⟨1, rfl⟩

/-- Every element of `h₂⁺` occurs in the positive challenge stream. -/
theorem positiveChallengeStream_covers_plusTwo :
    ∀ z, z ∈ properReplayHardFamily .plusTwo →
      ∃ n, positiveChallengeStream n = z := by
  intro z hz
  change 0 ≤ z ∨ z = -2 at hz
  rcases hz with hz | rfl
  · exact exists_positiveChallengeStream_eq_of_nonneg hz
  · exact ⟨2, rfl⟩

/-- Every element of `h₁⁻` occurs in the negative challenge stream. -/
theorem negativeChallengeStream_covers_minusOne :
    ∀ z, z ∈ properReplayHardFamily .minusOne →
      ∃ n, negativeChallengeStream n = z := by
  intro z hz
  change z ≤ 0 ∨ z = 1 at hz
  rcases hz with hz | rfl
  · exact exists_negativeChallengeStream_eq_of_nonpos hz
  · exact ⟨1, rfl⟩

/-- Every element of `h₂⁻` occurs in the negative challenge stream. -/
theorem negativeChallengeStream_covers_minusTwo :
    ∀ z, z ∈ properReplayHardFamily .minusTwo →
      ∃ n, negativeChallengeStream n = z := by
  intro z hz
  change z ≤ 0 ∨ z = 2 at hz
  rcases hz with hz | rfl
  · exact exists_negativeChallengeStream_eq_of_nonpos hz
  · exact ⟨2, rfl⟩

/-- The output after the common first example `0`. -/
def firstProperOutput
    (gen : ProperGenerator HardHypothesis ℤ) : HardHypothesis :=
  gen 1 (fun _ => 0)

theorem properOutput_positiveChallengeStream_one
    (gen : ProperGenerator HardHypothesis ℤ) :
    properOutput gen positiveChallengeStream 1 =
      firstProperOutput gen := by
  apply congrArg (gen 1)
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

theorem properOutput_negativeChallengeStream_one
    (gen : ProperGenerator HardHypothesis ℤ) :
    properOutput gen negativeChallengeStream 1 =
      firstProperOutput gen := by
  apply congrArg (gen 1)
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-- If the first output is a negative-half-line hypothesis, the paper's
positive stream is replay-legal for `h₁⁺`. -/
theorem positiveChallengeStream_replay_plusOne
    (gen : ProperGenerator HardHypothesis ℤ)
    (hfirst :
      firstProperOutput gen = .minusOne ∨
        firstProperOutput gen = .minusTwo) :
    IsProperReplaySequence properReplayHardFamily gen .plusOne
      positiveChallengeStream := by
  intro n
  match n with
  | 0 =>
      exact Or.inl (by simp [positiveChallengeStream,
        properReplayHardFamily])
  | 1 =>
      exact Or.inl (by simp [positiveChallengeStream,
        properReplayHardFamily])
  | 2 =>
      apply Or.inr
      refine ⟨1, by omega, by omega, ?_⟩
      rw [properOutput_positiveChallengeStream_one]
      rcases hfirst with hfirst | hfirst
      · simp [hfirst, positiveChallengeStream, properReplayHardFamily]
      · simp [hfirst, positiveChallengeStream, properReplayHardFamily]
  | n + 3 =>
      exact Or.inl (by simp [positiveChallengeStream,
        properReplayHardFamily]; omega)

/-- If the first output is a negative-half-line hypothesis, the same stream
is replay-legal for `h₂⁺`. -/
theorem positiveChallengeStream_replay_plusTwo
    (gen : ProperGenerator HardHypothesis ℤ)
    (hfirst :
      firstProperOutput gen = .minusOne ∨
        firstProperOutput gen = .minusTwo) :
    IsProperReplaySequence properReplayHardFamily gen .plusTwo
      positiveChallengeStream := by
  intro n
  match n with
  | 0 =>
      exact Or.inl (by simp [positiveChallengeStream,
        properReplayHardFamily])
  | 1 =>
      apply Or.inr
      refine ⟨1, by omega, by omega, ?_⟩
      rw [properOutput_positiveChallengeStream_one]
      rcases hfirst with hfirst | hfirst
      · simp [hfirst, positiveChallengeStream, properReplayHardFamily]
      · simp [hfirst, positiveChallengeStream, properReplayHardFamily]
  | 2 =>
      exact Or.inl (by simp [positiveChallengeStream,
        properReplayHardFamily])
  | n + 3 =>
      exact Or.inl (by simp [positiveChallengeStream,
        properReplayHardFamily]; omega)

/-- If the first output is a positive-half-line hypothesis, the sign-reversed
stream is replay-legal for `h₁⁻`. -/
theorem negativeChallengeStream_replay_minusOne
    (gen : ProperGenerator HardHypothesis ℤ)
    (hfirst :
      firstProperOutput gen = .plusOne ∨
        firstProperOutput gen = .plusTwo) :
    IsProperReplaySequence properReplayHardFamily gen .minusOne
      negativeChallengeStream := by
  intro n
  match n with
  | 0 =>
      exact Or.inl (by simp [negativeChallengeStream,
        properReplayHardFamily])
  | 1 =>
      exact Or.inl (by simp [negativeChallengeStream,
        properReplayHardFamily])
  | 2 =>
      apply Or.inr
      refine ⟨1, by omega, by omega, ?_⟩
      rw [properOutput_negativeChallengeStream_one]
      rcases hfirst with hfirst | hfirst
      · simp [hfirst, negativeChallengeStream, properReplayHardFamily]
      · simp [hfirst, negativeChallengeStream, properReplayHardFamily]
  | n + 3 =>
      apply Or.inl
      change -((n : ℤ) + 1) ≤ 0 ∨ -((n : ℤ) + 1) = 1
      exact Or.inl (by omega)

/-- If the first output is a positive-half-line hypothesis, the sign-reversed
stream is replay-legal for `h₂⁻`. -/
theorem negativeChallengeStream_replay_minusTwo
    (gen : ProperGenerator HardHypothesis ℤ)
    (hfirst :
      firstProperOutput gen = .plusOne ∨
        firstProperOutput gen = .plusTwo) :
    IsProperReplaySequence properReplayHardFamily gen .minusTwo
      negativeChallengeStream := by
  intro n
  match n with
  | 0 =>
      exact Or.inl (by simp [negativeChallengeStream,
        properReplayHardFamily])
  | 1 =>
      apply Or.inr
      refine ⟨1, by omega, by omega, ?_⟩
      rw [properOutput_negativeChallengeStream_one]
      rcases hfirst with hfirst | hfirst
      · simp [hfirst, negativeChallengeStream, properReplayHardFamily]
      · simp [hfirst, negativeChallengeStream, properReplayHardFamily]
  | 2 =>
      exact Or.inl (by simp [negativeChallengeStream,
        properReplayHardFamily])
  | n + 3 =>
      apply Or.inl
      change -((n : ℤ) + 1) ≤ 0 ∨ -((n : ℤ) + 1) = 2
      exact Or.inl (by omega)

/-- The positive challenge is simultaneously an enumeration with replay for
the two positive-half-line targets. -/
theorem positiveChallengeStream_enumeration_plusOne
    (gen : ProperGenerator HardHypothesis ℤ)
    (hfirst :
      firstProperOutput gen = .minusOne ∨
        firstProperOutput gen = .minusTwo) :
    IsProperReplayEnumeration properReplayHardFamily gen .plusOne
      positiveChallengeStream :=
  ⟨positiveChallengeStream_replay_plusOne gen hfirst,
    positiveChallengeStream_covers_plusOne⟩

theorem positiveChallengeStream_enumeration_plusTwo
    (gen : ProperGenerator HardHypothesis ℤ)
    (hfirst :
      firstProperOutput gen = .minusOne ∨
        firstProperOutput gen = .minusTwo) :
    IsProperReplayEnumeration properReplayHardFamily gen .plusTwo
      positiveChallengeStream :=
  ⟨positiveChallengeStream_replay_plusTwo gen hfirst,
    positiveChallengeStream_covers_plusTwo⟩

/-- The negative challenge is simultaneously an enumeration with replay for
the two negative-half-line targets. -/
theorem negativeChallengeStream_enumeration_minusOne
    (gen : ProperGenerator HardHypothesis ℤ)
    (hfirst :
      firstProperOutput gen = .plusOne ∨
        firstProperOutput gen = .plusTwo) :
    IsProperReplayEnumeration properReplayHardFamily gen .minusOne
      negativeChallengeStream :=
  ⟨negativeChallengeStream_replay_minusOne gen hfirst,
    negativeChallengeStream_covers_minusOne⟩

theorem negativeChallengeStream_enumeration_minusTwo
    (gen : ProperGenerator HardHypothesis ℤ)
    (hfirst :
      firstProperOutput gen = .plusOne ∨
        firstProperOutput gen = .plusTwo) :
    IsProperReplayEnumeration properReplayHardFamily gen .minusTwo
      negativeChallengeStream :=
  ⟨negativeChallengeStream_replay_minusTwo gen hfirst,
    negativeChallengeStream_covers_minusTwo⟩

/-- No member of the hard class is contained in both positive-half-line
targets. -/
theorem no_common_hypothesis_for_plus_targets
    (i : HardHypothesis) :
    ¬(properReplayHardFamily i ⊆
        properReplayHardFamily .plusOne ∧
      properReplayHardFamily i ⊆
        properReplayHardFamily .plusTwo) := by
  intro h
  cases i with
  | minusOne =>
      have hbad := h.1 (show (-3 : ℤ) ∈
        properReplayHardFamily .minusOne by
          simp [properReplayHardFamily])
      simp [properReplayHardFamily] at hbad
  | minusTwo =>
      have hbad := h.1 (show (-3 : ℤ) ∈
        properReplayHardFamily .minusTwo by
          simp [properReplayHardFamily])
      simp [properReplayHardFamily] at hbad
  | plusOne =>
      have hbad := h.2 (show (-1 : ℤ) ∈
        properReplayHardFamily .plusOne by
          simp [properReplayHardFamily])
      simp [properReplayHardFamily] at hbad
  | plusTwo =>
      have hbad := h.1 (show (-2 : ℤ) ∈
        properReplayHardFamily .plusTwo by
          simp [properReplayHardFamily])
      simp [properReplayHardFamily] at hbad

/-- No member of the hard class is contained in both negative-half-line
targets. -/
theorem no_common_hypothesis_for_minus_targets
    (i : HardHypothesis) :
    ¬(properReplayHardFamily i ⊆
        properReplayHardFamily .minusOne ∧
      properReplayHardFamily i ⊆
        properReplayHardFamily .minusTwo) := by
  intro h
  cases i with
  | minusOne =>
      have hbad := h.2 (show (1 : ℤ) ∈
        properReplayHardFamily .minusOne by
          simp [properReplayHardFamily])
      simp [properReplayHardFamily] at hbad
  | minusTwo =>
      have hbad := h.1 (show (2 : ℤ) ∈
        properReplayHardFamily .minusTwo by
          simp [properReplayHardFamily])
      simp [properReplayHardFamily] at hbad
  | plusOne =>
      have hbad := h.1 (show (3 : ℤ) ∈
        properReplayHardFamily .plusOne by
          simp [properReplayHardFamily])
      simp [properReplayHardFamily] at hbad
  | plusTwo =>
      have hbad := h.1 (show (3 : ℤ) ∈
        properReplayHardFamily .plusTwo by
          simp [properReplayHardFamily])
      simp [properReplayHardFamily] at hbad

/-- Theorem 7.3: the source's explicit four-language class is not properly
generatable in the limit with replay. -/
theorem theorem_7_3 :
    ¬ProperlyGeneratableInLimitWithReplay
      properReplayHardFamily := by
  rintro ⟨gen, hgen⟩
  generalize hfirstEq : firstProperOutput gen = first
  cases first with
  | minusOne =>
      have hfirst :
          firstProperOutput gen = .minusOne ∨
            firstProperOutput gen = .minusTwo :=
        Or.inl hfirstEq
      exact
        (twoTarget_replay_obstruction gen
          (positiveChallengeStream_enumeration_plusOne gen hfirst)
          (positiveChallengeStream_enumeration_plusTwo gen hfirst)
          no_common_hypothesis_for_plus_targets) hgen
  | minusTwo =>
      have hfirst :
          firstProperOutput gen = .minusOne ∨
            firstProperOutput gen = .minusTwo :=
        Or.inr hfirstEq
      exact
        (twoTarget_replay_obstruction gen
          (positiveChallengeStream_enumeration_plusOne gen hfirst)
          (positiveChallengeStream_enumeration_plusTwo gen hfirst)
          no_common_hypothesis_for_plus_targets) hgen
  | plusOne =>
      have hfirst :
          firstProperOutput gen = .plusOne ∨
            firstProperOutput gen = .plusTwo :=
        Or.inl hfirstEq
      exact
        (twoTarget_replay_obstruction gen
          (negativeChallengeStream_enumeration_minusOne gen hfirst)
          (negativeChallengeStream_enumeration_minusTwo gen hfirst)
          no_common_hypothesis_for_minus_targets) hgen
  | plusTwo =>
      have hfirst :
          firstProperOutput gen = .plusOne ∨
            firstProperOutput gen = .plusTwo :=
        Or.inr hfirstEq
      exact
        (twoTarget_replay_obstruction gen
          (negativeChallengeStream_enumeration_minusOne gen hfirst)
          (negativeChallengeStream_enumeration_minusTwo gen hfirst)
          no_common_hypothesis_for_minus_targets) hgen

/-- Paper-shaped existential wrapper for Theorem 7.3: a four-member UUS
hypothesis family fails proper generation in the limit with replay. -/
theorem theorem_7_3_paper :
    ∃ family : HardHypothesis → Generic.Language ℤ,
      Fintype.card HardHypothesis = 4 ∧
      (∀ i, (family i).Infinite) ∧
      ¬ProperlyGeneratableInLimitWithReplay family :=
  ⟨properReplayHardFamily, properReplayHardFamily_card,
    properReplayHardFamily_infinite, theorem_7_3⟩

end Replay
end GenLimit
