import GenLimit.NoRegretLanguageGeneration.FiniteMinimax
import GenLimit.NoRegretLanguageGeneration.EpochScheduling
import GenLimit.NoRegretLanguageGeneration.Sublinear

namespace PredictionToGeneration

/-- Full-horizon realizable guarantees also hold on every shorter prefix. -/
theorem realizable_prefix_bound (H : HypothesisClass X) (hu : UUS H)
    (G : Generator X) (N B : Nat)
    (hb : ∀ xs, xs.Nodup → xs.length = N → ∀ h, H h →
      Realizes h (G.play xs) → mistakes h (G.play xs) ≤ B)
    (xs : List X) (hn : xs.Nodup) (hl : xs.length ≤ N)
    (h : Hypothesis X) (hh : H h) (hr : Realizes h (G.play xs)) :
    mistakes h (G.play xs) ≤ B := by
  have extension : ∀ k : Nat, ∀ ys : List X, ys.Nodup → Realizes h (G.play ys) →
      ys.length + k = N → mistakes h (G.play ys) ≤ B := by
    intro k
    induction k with
    | zero => intro ys hn hr hl; exact hb ys hn (by omega) h hh hr
    | succ k ih =>
      intro ys hn hr hl
      obtain ⟨x, hx, hp⟩ := hu h hh ys
      have ht := ih (x :: ys) (List.nodup_cons.mpr ⟨hx, hn⟩) ⟨hp, hr⟩
        (by simp only [List.length_cons]; omega)
      simp only [Generator.play, mistakes] at ht
      omega
  exact extension (N - xs.length) xs hn hr (by omega)

/-- Every selected finite generator receives the complete demonstration history. -/
def epochGenerator (family : Nat → Generator X) (index : Nat → Nat) : Generator X where
  output xs := (family (index (xs.length + 1))).output xs
  fresh xs := (family (index (xs.length + 1))).fresh xs

/-- The accounting invariant retains the active generator's whole-prefix loss.
This is valid because realizable mistake counts are nonnegative. -/
theorem epoch_mistake_accounting (H : HypothesisClass X) (family : Nat → Generator X)
    (index C : Nat → Nat) (hmono : ∀ t, index t ≤ index (t + 1))
    (hcost : ∀ t xs, xs.Nodup → xs.length = t → ∀ h, H h →
      Realizes h ((family (index t)).play xs) →
      mistakes h ((family (index t)).play xs) ≤ C (index t))
    (xs : List X) (hn : xs.Nodup) (h : Hypothesis X) (hh : H h)
    (hr : ∀ x ∈ xs, h x = true) :
    mistakes h ((epochGenerator family index).play xs) ≤
      epochBudget C (index xs.length) + mistakes h ((family (index xs.length)).play xs) := by
  have realizable : ∀ (G : Generator X) ys, (∀ x ∈ ys, h x = true) → Realizes h (G.play ys) := by
    intro G ys
    induction ys with
    | nil => intro _; trivial
    | cons x ys ih => intro hr; exact ⟨hr x (by simp), ih (fun y hy => hr y (by simp [hy]))⟩
  induction xs with
  | nil => simp [Generator.play, mistakes]
  | cons x xs ih =>
    have hnt := (List.nodup_cons.mp hn).2
    have hrt : ∀ y ∈ xs, h y = true := fun y hy => hr y (by simp [hy])
    have hi := ih hnt hrt
    have hc := hcost xs.length xs hnt rfl h hh (realizable _ xs hrt)
    have hm := hmono xs.length
    simp only [Generator.play, mistakes, epochGenerator, List.length_cons]
    simp only [epochGenerator] at hi
    by_cases he : index xs.length = index (xs.length + 1)
    · rw [he] at hi
      omega
    · have hlt : index xs.length + 1 ≤ index (xs.length + 1) := by omega
      have hb := epochBudget_mono C hlt
      simp only [epochBudget] at hb
      omega

theorem realizes_play_iff (G : Generator X) (h : Hypothesis X) (xs : List X) :
    Realizes h (G.play xs) ↔ ∀ x ∈ xs, h x = true := by
  induction xs with
  | nil => simp [Generator.play, Realizes]
  | cons x xs ih => simp [Generator.play, Realizes, ih]

theorem epoch_mistake_bound (H : HypothesisClass X) (family : Nat → Generator X)
    (index C : Nat → Nat) (hmono : ∀ t, index t ≤ index (t + 1))
    (hcost : ∀ t xs, xs.Nodup → xs.length = t → ∀ h, H h →
      Realizes h ((family (index t)).play xs) →
      mistakes h ((family (index t)).play xs) ≤ C (index t))
    (xs : List X) (hn : xs.Nodup) (h : Hypothesis X) (hh : H h)
    (hr : Realizes h ((epochGenerator family index).play xs)) :
    mistakes h ((epochGenerator family index).play xs) ≤ epochBudget C (index xs.length + 1) := by
  have hp := (realizes_play_iff _ h xs).mp hr
  have ha := epoch_mistake_accounting H family index C hmono hcost xs hn h hh hp
  have hc := hcost xs.length xs hn rfl h hh ((realizes_play_iff _ h xs).mpr hp)
  simp only [epochBudget]
  omega

end PredictionToGeneration





namespace PredictionToGeneration

/-- An arbitrary prescribed divergent rate can control mistakes whenever all
finite-horizon minimax values share a fixed bound. -/
theorem slow_growth_anytime (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (d : Nat) (hd : ∀ T, MF H T ≤ d)
    (r : Nat → Nat) (hmono : ∀ i j, i ≤ j → r i ≤ r j)
    (hunbounded : ∀ b, ∃ t, b < r t) (hpositive : ∀ t, 1 ≤ t → 1 ≤ r t) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → 1 ≤ xs.length →
      ∀ h, H h → Realizes h (G.play xs) → mistakes h (G.play xs) ≤ d * r xs.length := by
  classical
  let cap : Nat → Nat := fun j => Classical.choose (hunbounded (j + 1))
  have hcap : ∀ j, j + 1 < r (cap j) := fun j => Classical.choose_spec (hunbounded (j + 1))
  let family : Nat → Generator X := fun j => Classical.choose (mf_generator_attained H hu hne (cap j))
  have hfamily : ∀ j xs, xs.Nodup → xs.length = cap j → ∀ h, H h →
      Realizes h ((family j).play xs) → mistakes h ((family j).play xs) ≤ d := by
    intro j xs hn hl h hh hr
    exact Nat.le_trans ((Classical.choose_spec (mf_generator_attained H hu hne (cap j))) xs hn hl h hh hr) (hd (cap j))
  let index : Nat → Nat := fun t => r t - 1
  have hi : ∀ t, index t ≤ index (t + 1) := by
    intro t
    have := hmono t (t + 1) (by omega)
    dsimp [index]
    omega
  have hc : ∀ t xs, xs.Nodup → xs.length = t → ∀ h, H h →
      Realizes h ((family (index t)).play xs) →
      mistakes h ((family (index t)).play xs) ≤ d := by
    intro t xs hn hl h hh hr
    apply realizable_prefix_bound H hu (family (index t)) (cap (index t)) d (hfamily _) xs hn _ h hh hr
    have hb := hcap (index t)
    have ht : t ≤ cap (index t) := by
      by_cases he : t ≤ cap (index t)
      · exact he
      · have hm := hmono (cap (index t)) t (by omega)
        dsimp [index] at hb hm
        omega
    omega
  refine ⟨epochGenerator family index, ?_⟩
  intro xs hn hl h hh hr
  have hb := epoch_mistake_bound H family index (fun _ => d) hi hc xs hn h hh hr
  rw [epochBudget_constant] at hb
  have hp := hpositive xs.length hl
  have he : index xs.length + 1 = r xs.length := by dsimp [index]; omega
  simpa [he] using hb

end PredictionToGeneration


namespace PredictionToGeneration
open Classical

noncomputable def dyadicLevel (b : Nat) : Nat :=
  thresholdMax (fun j => j = 0 ∨ 2 ^ j < b) b + 1

theorem dyadicLevel_covers (b : Nat) : b ≤ 2 ^ dyadicLevel b := by
  have hs := thresholdMax_spec (fun j => j = 0 ∨ 2 ^ j < b) (Or.inl rfl) b
  by_cases hc : dyadicLevel b ≤ b
  · by_cases hb : b ≤ 2 ^ dyadicLevel b
    · exact hb
    · have ht := hs.2 (dyadicLevel b) hc (Or.inr (by omega))
      unfold dyadicLevel at ht
      omega
  · have hp : dyadicLevel b < 2 ^ dyadicLevel b := Nat.lt_two_pow_self
    omega

theorem dyadicLevel_cost (b : Nat) (hb : 1 ≤ b) : 2 ^ dyadicLevel b ≤ 2 * b := by
  have hs := (thresholdMax_spec (fun j => j = 0 ∨ 2 ^ j < b) (Or.inl rfl) b).1
  unfold dyadicLevel
  rw [Nat.pow_succ]
  rcases hs with he | he
  · rw [he]; simp; omega
  · omega

theorem dyadicLevel_mono {b c : Nat} (hbc : b ≤ c) : dyadicLevel b ≤ dyadicLevel c := by
  have hb := thresholdMax_spec (fun j => j = 0 ∨ 2 ^ j < b) (Or.inl rfl) b
  have hc := thresholdMax_spec (fun j => j = 0 ∨ 2 ^ j < c) (Or.inl rfl) c
  have ht := hc.2 (thresholdMax (fun j => j = 0 ∨ 2 ^ j < b) b)
    (Nat.le_trans (thresholdMax_le _ b) hbc)
    (by rcases hb.1 with he | he; exact Or.inl he; exact Or.inr (by omega))
  unfold dyadicLevel
  omega

theorem epochBudget_dyadic (j : Nat) : epochBudget (fun k => 2 ^ k) j + 1 = 2 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [epochBudget, Nat.pow_succ]; omega

/-- The quantitative horizon-to-anytime theorem for integer envelopes. -/
theorem horizon_to_anytime_nat (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (b : Nat → Nat)
    (hmono : ∀ i j, i ≤ j → b i ≤ b j)
    (hunbounded : ∀ c, ∃ t, c < b t)
    (hpositive : ∀ t, 1 ≤ t → 1 ≤ b t)
    (hbound : ∀ t, MF H t ≤ b t) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → 1 ≤ xs.length →
      ∀ h, H h → Realizes h (G.play xs) → mistakes h (G.play xs) ≤ 4 * b xs.length := by
  classical
  let cap : Nat → Nat := fun j => Classical.choose (hunbounded (2 ^ j))
  have hcap : ∀ j, 2 ^ j < b (cap j) := fun j => Classical.choose_spec (hunbounded (2 ^ j))
  let N : Nat → Nat := fun j => thresholdMax (fun t => t = 0 ∨ b t ≤ 2 ^ j) (cap j)
  have hNcost : ∀ j, MF H (N j) ≤ 2 ^ j := by
    intro j
    have hs := (thresholdMax_spec (fun t => t = 0 ∨ b t ≤ 2 ^ j) (Or.inl rfl) (cap j)).1
    change N j = 0 ∨ b (N j) ≤ 2 ^ j at hs
    rcases hs with he | he
    · rw [he]
      exact Nat.le_trans (mf_le_horizon H 0) (Nat.zero_le _)
    · exact Nat.le_trans (hbound _) he
  have hNcovers : ∀ t j, b t ≤ 2 ^ j → t ≤ N j := by
    intro t j ht
    have hc : t ≤ cap j := by
      by_cases hh : t ≤ cap j
      · exact hh
      · have hm := hmono (cap j) t (by omega)
        have hb := hcap j
        omega
    exact (thresholdMax_spec (fun t => t = 0 ∨ b t ≤ 2 ^ j) (Or.inl rfl) (cap j)).2 t hc (Or.inr ht)
  let family : Nat → Generator X := fun j => Classical.choose (mf_generator_attained H hu hne (N j))
  have hfamily : ∀ j xs, xs.Nodup → xs.length = N j → ∀ h, H h →
      Realizes h ((family j).play xs) → mistakes h ((family j).play xs) ≤ 2 ^ j := by
    intro j xs hn hl h hh hr
    exact Nat.le_trans ((Classical.choose_spec (mf_generator_attained H hu hne (N j))) xs hn hl h hh hr) (hNcost j)
  let index : Nat → Nat := fun t => dyadicLevel (b t)
  have hi : ∀ t, index t ≤ index (t + 1) := fun t => dyadicLevel_mono (hmono t (t + 1) (by omega))
  have hc : ∀ t xs, xs.Nodup → xs.length = t → ∀ h, H h →
      Realizes h ((family (index t)).play xs) →
      mistakes h ((family (index t)).play xs) ≤ 2 ^ index t := by
    intro t xs hn hl h hh hr
    apply realizable_prefix_bound H hu (family (index t)) (N (index t)) (2 ^ index t) (hfamily _) xs hn _ h hh hr
    rw [hl]
    exact hNcovers t (index t) (dyadicLevel_covers (b t))
  refine ⟨epochGenerator family index, ?_⟩
  intro xs hn hl h hh hr
  have hb := epoch_mistake_bound H family index (fun j => 2 ^ j) hi hc xs hn h hh hr
  have he := epochBudget_dyadic (index xs.length + 1)
  have hd := dyadicLevel_cost (b xs.length) (hpositive _ hl)
  change 2 ^ index xs.length ≤ 2 * b xs.length at hd
  rw [Nat.pow_succ] at he
  omega

end PredictionToGeneration



namespace PredictionToGeneration

/-- One anytime generator with a uniform vanishing mistake fraction. -/
def RealizableNoRegret (H : HypothesisClass X) : Prop :=
  ∃ G : Generator X, ∀ k : Nat, ∃ N : Nat, ∀ xs, xs.Nodup → N ≤ xs.length →
    ∀ h, H h → Realizes h (G.play xs) → k * mistakes h (G.play xs) ≤ xs.length

theorem realizable_no_regret_iff_sublinear (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) : RealizableNoRegret H ↔ NatSublinear (MF H) := by
  constructor
  · rintro ⟨G, hg⟩ k
    obtain ⟨N, hN⟩ := hg k
    refine ⟨N, ?_⟩
    intro t ht
    obtain ⟨xs, h, hn, hl, hh, hr, hm⟩ := mf_generator_lower_bound H hu hne t G
    have hb := hN xs hn (by omega) h hh hr
    have hc := Nat.mul_le_mul_left k hm
    omega
  · intro hf
    let b := sublinearEnvelope (MF H)
    have hmono : ∀ i j, i ≤ j → b i ≤ b j :=
      sublinearEnvelope_mono (nat_mono_of_succ (MF H) (mf_mono_succ H hu hne))
    obtain ⟨G, hg⟩ := horizon_to_anytime_nat H hu hne b hmono
      (sublinearEnvelope_unbounded _) (fun t _ => sublinearEnvelope_positive _ t) (le_sublinearEnvelope _)
    refine ⟨G, ?_⟩
    intro k
    obtain ⟨N, hN⟩ := sublinearEnvelope_sublinear hf (k * 4)
    refine ⟨max 1 N, ?_⟩
    intro xs hn hl h hh hr
    have hp : 1 ≤ xs.length := by omega
    have hb := hg xs hn hp h hh hr
    have hc := Nat.mul_le_mul_left k hb
    have hd := hN xs.length (by omega)
    dsimp [b] at hc
    rw [← Nat.mul_assoc] at hc
    exact Nat.le_trans hc hd

end PredictionToGeneration
