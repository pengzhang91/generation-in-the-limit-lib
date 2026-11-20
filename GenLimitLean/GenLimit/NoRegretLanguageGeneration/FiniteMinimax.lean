import GenLimit.NoRegretLanguageGeneration.Plays

namespace PredictionToGeneration
open Classical

open Classical

/-- Maximum forceable threshold among `0, ..., T`, with default zero. -/
noncomputable def thresholdMax (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => if P (n + 1) then n + 1 else thresholdMax P n

theorem thresholdMax_le (P : Nat → Prop) (n : Nat) : thresholdMax P n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    classical
    simp only [thresholdMax]
    split <;> omega

theorem thresholdMax_spec (P : Nat → Prop) (hzero : P 0) (n : Nat) :
    P (thresholdMax P n) ∧ ∀ m, m ≤ n → P m → m ≤ thresholdMax P n := by
  classical
  induction n with
  | zero => exact ⟨hzero, by intro m hm _; simpa [thresholdMax] using hm⟩
  | succ n ih =>
    simp only [thresholdMax]
    split
    · rename_i h
      exact ⟨h, fun _ hm _ => hm⟩
    · rename_i h
      refine ⟨ih.1, ?_⟩
      intro m hm hp
      have hne : m ≠ n + 1 := fun he => h (he ▸ hp)
      exact ih.2 m (by omega) hp

noncomputable def MF (H : HypothesisClass X) (T : Nat) : Nat :=
  thresholdMax (MFForces H T) T

/-- The signed dimension is nonnegative, although individual regrets need not be. -/
noncomputable def SMF (H : HypothesisClass X) (T : Nat) : Nat :=
  thresholdMax (fun m => SMFForces H T (m : Int)) T

noncomputable def generatorOfUUS (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) : Generator X := by
  classical
  let h := Classical.choose hne
  have hh := Classical.choose_spec hne
  exact ⟨fun xs => Classical.choose (hu h hh xs),
    fun xs => (Classical.choose_spec (hu h hh xs)).1⟩

theorem realizable_zero_forces (H : HypothesisClass X) (hu : UUS H)
    (h : Hypothesis X) (hh : H h) (T : Nat) (τ : Trajectory X)
    (hr : Realizes h τ) : Forces (RealizableBad H 0) T τ := by
  induction T generalizing τ with
  | zero => exact ⟨h, hh, hr, Nat.zero_le _⟩
  | succ T ih =>
    intro z hz
    obtain ⟨x, hx, hp⟩ := fresh_positive H hu h hh τ
    exact ⟨x, hx, ih _ ⟨hp, hr⟩⟩

theorem signed_copy_forces (H : HypothesisClass X) (h : Hypothesis X)
    (hh : H h) (T : Nat) (τ : Trajectory X) :
    Forces (SignedBad H (regret h τ)) T τ := by
  induction T generalizing τ with
  | zero => exact ⟨h, hh, Int.le_refl _⟩
  | succ T ih =>
    intro z hz
    exact ⟨z, hz, by simpa [regret_copy] using ih ((z, z) :: τ)⟩

theorem mf_forces_le_horizon (H : HypothesisClass X) (G : Generator X)
    (T m : Nat) (hf : MFForces H T m) : m ≤ T := by
  obtain ⟨leaf, h, _, _, hl, _, _, hm⟩ := realizable_lower_bound H T m hf (G.strategy T [])
  have := mistakes_le_length h leaf
  omega

theorem smf_forces_le_horizon (H : HypothesisClass X) (G : Generator X)
    (T : Nat) (m : Int) (hf : SMFForces H T m) : m ≤ (T : Int) := by
  obtain ⟨leaf, h, _, _, hl, _, hm⟩ := agnostic_lower_bound H T m hf (G.strategy T [])
  have := (regret_bounds h leaf).2
  omega

theorem mf_spec (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h) (T : Nat) :
    MFForces H T (MF H T) ∧ ∀ m, MFForces H T m → m ≤ MF H T := by
  let h := Classical.choose hne
  have hh := Classical.choose_spec hne
  have hs := thresholdMax_spec (MFForces H T)
    (realizable_zero_forces H hu h hh T [] trivial) T
  exact ⟨hs.1, fun m hf => hs.2 m (mf_forces_le_horizon H (generatorOfUUS H hu ⟨h, hh⟩) T m hf) hf⟩

theorem smf_spec (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h) (T : Nat) :
    SMFForces H T (SMF H T : Int) ∧ ∀ m : Int, SMFForces H T m → m ≤ (SMF H T : Int) := by
  let h := Classical.choose hne
  have hh := Classical.choose_spec hne
  have hz : SMFForces H T 0 := by simpa [regret, mistakes, demonstrationLoss] using signed_copy_forces H h hh T []
  have hs := thresholdMax_spec (fun m => SMFForces H T (m : Int)) hz T
  refine ⟨hs.1, ?_⟩
  intro m hf
  by_cases hm : 0 ≤ m
  · have ht := smf_forces_le_horizon H (generatorOfUUS H hu ⟨h, hh⟩) T m hf
    have hc : (m.toNat : Int) = m := Int.toNat_of_nonneg hm
    have hb := hs.2 m.toNat (by omega) (by simpa [hc] using hf)
    change m ≤ (thresholdMax (fun m => SMFForces H T (m : Int)) T : Int)
    omega
  · omega

theorem mf_le_horizon (H : HypothesisClass X) (T : Nat) : MF H T ≤ T := thresholdMax_le _ _
theorem smf_le_horizon (H : HypothesisClass X) (T : Nat) : SMF H T ≤ T := thresholdMax_le _ _

theorem mf_le_smf (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h) (T : Nat) :
    MF H T ≤ SMF H T := by
  have hf := realizable_forcing_implies_signed H T (MF H T) (mf_spec H hu hne T).1
  have := (smf_spec H hu hne T).2 _ hf
  omega

theorem mf_attained (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h) (T : Nat) :
    ∃ s : Strategy X T [], Guarantees
      (fun τ => ∀ h, H h → Realizes h τ → mistakes h τ ≤ MF H T) s := by
  apply (realizable_finite_characterization H T (MF H T)).mp
  intro hf
  have := (mf_spec H hu hne T).2 _ hf
  omega

theorem smf_attained (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h) (T : Nat) :
    ∃ s : Strategy X T [], Guarantees
      (fun τ => ∀ h, H h → regret h τ ≤ (SMF H T : Int)) s := by
  apply (agnostic_finite_characterization H T (SMF H T : Int)).mp
  intro hf
  have := (smf_spec H hu hne T).2 _ hf
  omega

end PredictionToGeneration



namespace PredictionToGeneration
open Classical

/-- Evaluate a finite strategy on a chronological demonstration continuation.
After the horizon, or after an illegal response, use a total fallback policy. -/
noncomputable def Strategy.outputAfter (fallback : Generator X) :
    {n : Nat} → {τ : Trajectory X} → Strategy X n τ → List X → X
  | 0, τ, .done _, ys => fallback.output (ys.reverse ++ demonstrations τ)
  | _ + 1, _, .step z _ _, [] => z
  | _ + 1, τ, .step _ _ next, x :: ys =>
    if hx : Fresh τ x then Strategy.outputAfter fallback (next x hx) ys
    else fallback.output ((x :: ys).reverse ++ demonstrations τ)

theorem Strategy.outputAfter_fresh (fallback : Generator X) {n : Nat}
    {τ : Trajectory X} (s : Strategy X n τ) (ys : List X) :
    s.outputAfter fallback ys ∉ ys.reverse ++ demonstrations τ := by
  induction s generalizing ys with
  | done τ => exact fallback.fresh _
  | @step n τ z hz next ih =>
    cases ys with
    | nil => simpa [Strategy.outputAfter] using hz
    | cons x ys =>
      simp only [Strategy.outputAfter]
      split
      · rename_i hx
        simpa [List.reverse_cons, List.append_assoc, demonstrations] using ih x hx ys
      · exact fallback.fresh _

noncomputable def Strategy.toGenerator (fallback : Generator X) {n : Nat}
    (s : Strategy X n []) : Generator X where
  output xs := s.outputAfter fallback xs.reverse
  fresh xs := by simpa [demonstrations] using s.outputAfter_fresh fallback xs.reverse

/-- Agreement with a finite tree uses only demonstrations, not comparator labels. -/
def Strategy.Agrees (G : Generator X) :
    {n : Nat} → {τ : Trajectory X} → Strategy X n τ → Prop
  | 0, _, .done _ => True
  | _ + 1, τ, .step z _ next =>
    G.output (demonstrations τ) = z ∧ ∀ x hx, Strategy.Agrees G (next x hx)

theorem Strategy.agrees_of_outputAfter (fallback G : Generator X) {n : Nat}
    {τ : Trajectory X} (s : Strategy X n τ)
    (he : ∀ ys, G.output (ys.reverse ++ demonstrations τ) = s.outputAfter fallback ys) :
    s.Agrees G := by
  induction s with
  | done τ => trivial
  | @step n τ z hz next ih =>
    refine ⟨by simpa [Strategy.outputAfter] using he [], ?_⟩
    intro x hx
    apply ih x hx
    intro ys
    simpa [Strategy.outputAfter, hx, List.reverse_cons, List.append_assoc, demonstrations]
      using he (x :: ys)

theorem Strategy.toGenerator_agrees (fallback : Generator X) {n : Nat}
    (s : Strategy X n []) : s.Agrees (s.toGenerator fallback) := by
  apply s.agrees_of_outputAfter fallback
  intro ys
  simp [Strategy.toGenerator, demonstrations]

theorem Strategy.agrees_guarantees (G : Generator X) (P : Trajectory X → Prop)
    {n : Nat} {τ : Trajectory X} (s : Strategy X n τ) (ha : s.Agrees G)
    (hs : Guarantees P s) : Guarantees P (G.strategy n τ) := by
  induction s with
  | done τ => exact hs
  | @step n τ z hz next ih =>
    obtain ⟨he, hc⟩ := ha
    simp only [Generator.strategy, Guarantees]
    intro x hx
    have hi := ih x hx (hc x hx) (hs x hx)
    rw [he]
    exact hi

/-- Finite strategy trees and total history generators attain the same bounds. -/
theorem strategy_iff_generator (fallback : Generator X) (P : Trajectory X → Prop) (T : Nat) :
    (∃ s : Strategy X T [], Guarantees P s) ↔
      ∃ G : Generator X, Guarantees P (G.strategy T []) := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s.toGenerator fallback,
      s.agrees_guarantees _ P (s.toGenerator_agrees fallback) hs⟩
  · rintro ⟨G, hg⟩
    exact ⟨G.strategy T [], hg⟩

end PredictionToGeneration


namespace PredictionToGeneration

 theorem legal_demonstrations_nodup (τ : Trajectory X) (hl : Legal τ) :
    (demonstrations τ).Nodup := by
  induction τ with
  | nil => exact List.nodup_nil
  | cons p τ ih => exact List.nodup_cons.mpr ⟨hl.2.2, ih hl.1⟩

theorem Generator.continuation_outcome (G : Generator X) (ys : List X)
    (τ : Trajectory X) (hc : G.play (demonstrations τ) = τ)
    (hn : (ys.reverse ++ demonstrations τ).Nodup) :
    Outcome (G.strategy ys.length τ) (G.play (ys.reverse ++ demonstrations τ)) := by
  induction ys generalizing τ with
  | nil => simpa [Generator.strategy, Outcome] using hc
  | cons x ys ih =>
    have hn' : (ys.reverse ++ x :: demonstrations τ).Nodup := by
      simpa [List.reverse_cons, List.append_assoc] using hn
    have hx : Fresh τ x := (List.nodup_cons.mp (List.nodup_append.mp hn').2.1).1
    refine ⟨x, hx, ?_⟩
    have hc' : G.play (demonstrations ((G.output (demonstrations τ), x) :: τ)) =
        (G.output (demonstrations τ), x) :: τ := by
      change (G.output (demonstrations τ), x) :: G.play (demonstrations τ) = _
      rw [hc]
    have hi := ih ((G.output (demonstrations τ), x) :: τ) hc' hn'
    simpa [List.reverse_cons, List.append_assoc, demonstrations] using hi

/-- The finite-tree guarantee is exactly the bound on all legal demonstration histories. -/
theorem Generator.guarantees_iff_histories (G : Generator X) (P : Trajectory X → Prop) (T : Nat) :
    Guarantees P (G.strategy T []) ↔
      ∀ xs, xs.Nodup → xs.length = T → P (G.play xs) := by
  rw [guarantees_iff_outcomes]
  constructor
  · intro hg xs hn hl
    have ho := G.continuation_outcome xs.reverse [] rfl (by simpa [demonstrations] using hn)
    apply hg (G.play xs)
    rw [List.length_reverse, hl] at ho
    simpa [demonstrations] using ho
  · intro hg leaf ho
    have hc := G.strategy_consistent T [] rfl leaf ho
    rw [← hc]
    apply hg
    · exact legal_demonstrations_nodup leaf (outcome_legal (G.strategy T []) trivial leaf ho)
    · simpa [demonstrations] using outcome_length _ leaf ho

theorem mf_generator_attained (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → xs.length = T →
      ∀ h, H h → Realizes h (G.play xs) → mistakes h (G.play xs) ≤ MF H T := by
  obtain ⟨G, hg⟩ := (strategy_iff_generator (generatorOfUUS H hu hne) _ T).mp (mf_attained H hu hne T)
  exact ⟨G, (G.guarantees_iff_histories _ T).mp hg⟩

theorem smf_generator_attained (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → xs.length = T →
      ∀ h, H h → regret h (G.play xs) ≤ (SMF H T : Int) := by
  obtain ⟨G, hg⟩ := (strategy_iff_generator (generatorOfUUS H hu hne) _ T).mp (smf_attained H hu hne T)
  exact ⟨G, (G.guarantees_iff_histories _ T).mp hg⟩

theorem mf_generator_lower_bound (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) (G : Generator X) :
    ∃ xs h, xs.Nodup ∧ xs.length = T ∧ H h ∧ Realizes h (G.play xs) ∧
      MF H T ≤ mistakes h (G.play xs) := by
  obtain ⟨leaf, h, ho, hl, hn, hh, hr, hm⟩ :=
    realizable_lower_bound H T _ (mf_spec H hu hne T).1 (G.strategy T [])
  have hc := G.strategy_consistent T [] rfl leaf ho
  exact ⟨demonstrations leaf, h, legal_demonstrations_nodup leaf hl,
    by simpa [demonstrations] using hn, hh, by simpa [hc] using hr, by simpa [hc] using hm⟩

theorem smf_generator_lower_bound (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) (G : Generator X) :
    ∃ xs h, xs.Nodup ∧ xs.length = T ∧ H h ∧ (SMF H T : Int) ≤ regret h (G.play xs) := by
  obtain ⟨leaf, h, ho, hl, hn, hh, hm⟩ :=
    agnostic_lower_bound H T _ (smf_spec H hu hne T).1 (G.strategy T [])
  have hc := G.strategy_consistent T [] rfl leaf ho
  exact ⟨demonstrations leaf, h, legal_demonstrations_nodup leaf hl,
    by simpa [demonstrations] using hn, hh, by simpa [hc] using hm⟩

end PredictionToGeneration



namespace PredictionToGeneration

theorem mf_le_of_generator_bound (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T B : Nat) (G : Generator X)
    (hb : ∀ xs, xs.Nodup → xs.length = T → ∀ h, H h →
      Realizes h (G.play xs) → mistakes h (G.play xs) ≤ B) : MF H T ≤ B := by
  obtain ⟨xs, h, hn, hl, hh, hr, hm⟩ := mf_generator_lower_bound H hu hne T G
  exact Nat.le_trans hm (hb xs hn hl h hh hr)

theorem smf_le_of_generator_bound (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) (B : Int) (G : Generator X)
    (hb : ∀ xs, xs.Nodup → xs.length = T → ∀ h, H h →
      regret h (G.play xs) ≤ B) : (SMF H T : Int) ≤ B := by
  obtain ⟨xs, h, hn, hl, hh, hm⟩ := smf_generator_lower_bound H hu hne T G
  exact Int.le_trans hm (hb xs hn hl h hh)

theorem mf_mono_succ (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) : MF H T ≤ MF H (T + 1) := by
  obtain ⟨G, hg⟩ := mf_generator_attained H hu hne (T + 1)
  obtain ⟨xs, h, hn, hl, hh, hr, hm⟩ := mf_generator_lower_bound H hu hne T G
  obtain ⟨x, hx, hp⟩ := hu h hh xs
  have hb := hg (x :: xs) (List.nodup_cons.mpr ⟨hx, hn⟩)
    (by simp [hl]) h hh (show Realizes h (G.play (x :: xs)) from ⟨hp, hr⟩)
  simp only [Generator.play, mistakes] at hb
  omega

theorem smf_mono_succ (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) : SMF H T ≤ SMF H (T + 1) := by
  obtain ⟨G, hg⟩ := smf_generator_attained H hu hne (T + 1)
  obtain ⟨xs, h, hn, hl, hh, hm⟩ := smf_generator_lower_bound H hu hne T G
  have hb := hg (G.output xs :: xs) (List.nodup_cons.mpr ⟨G.fresh xs, hn⟩)
    (by simp [hl]) h hh
  simp only [Generator.play, regret_copy] at hb
  omega

theorem mf_succ_le (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) : MF H (T + 1) ≤ MF H T + 1 := by
  obtain ⟨G, hg⟩ := mf_generator_attained H hu hne T
  apply mf_le_of_generator_bound H hu hne (T + 1) (MF H T + 1) G
  intro xs hn hl h hh hr
  cases xs with
  | nil => simp at hl
  | cons x xs =>
    have hb := hg xs (List.nodup_cons.mp hn).2 (by simpa using hl) h hh hr.2
    have ho := loss_le_one h (G.output xs)
    simp only [Generator.play, mistakes]
    omega

theorem smf_succ_le (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) : SMF H (T + 1) ≤ SMF H T + 1 := by
  obtain ⟨G, hg⟩ := smf_generator_attained H hu hne T
  have hb : (SMF H (T + 1) : Int) ≤ (SMF H T : Int) + 1 := by
    apply smf_le_of_generator_bound H hu hne (T + 1) ((SMF H T : Int) + 1) G
    intro xs hn hl h hh
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      have hb := hg xs (List.nodup_cons.mp hn).2 (by simpa using hl) h hh
      have ho := loss_le_one h (G.output xs)
      simp only [Generator.play, regret_cons]
      omega
  omega

/-- Regularity of both exact finite-horizon profiles, including horizon zero. -/
theorem finite_profile_regularity (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (T : Nat) :
    MF H T ≤ MF H (T + 1) ∧ MF H (T + 1) ≤ MF H T + 1 ∧
    SMF H T ≤ SMF H (T + 1) ∧ SMF H (T + 1) ≤ SMF H T + 1 :=
  ⟨mf_mono_succ H hu hne T, mf_succ_le H hu hne T,
    smf_mono_succ H hu hne T, smf_succ_le H hu hne T⟩

end PredictionToGeneration
