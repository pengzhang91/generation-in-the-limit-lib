import GenLimit.NoRegretLanguageGeneration.Uniform
import GenLimit.NoRegretLanguageGeneration.AnytimeRealizable
import GenLimit.NoRegretLanguageGeneration.CompactnessGap
import GenLimit.NoRegretLanguageGeneration.Cofinite

namespace PredictionToGeneration

/-- The next output is correct after B demonstrations, uniformly over prefixes. -/
def LastMistakeBound (G : Generator X) (h : Hypothesis X) (B : Nat) : Prop :=
  ∀ xs, xs.Nodup → Realizes h (G.play xs) → B ≤ xs.length → h (G.output xs) = true

def UniformGeneration (H : HypothesisClass X) : Prop :=
  ∃ G : Generator X, ∃ B, ∀ h, H h → LastMistakeBound G h B

def NonuniformGeneration (H : HypothesisClass X) : Prop :=
  ∃ G : Generator X, ∀ h, H h → ∃ B, LastMistakeBound G h B

def UniformMistakeBounded (H : HypothesisClass X) : Prop :=
  ∃ G : Generator X, ∃ B, UniformMistakeBound G H B

/-- Positive, distinct demonstrations enumerate every point in the support. -/
def PositiveContinuation.Enumerates {h : Hypothesis X} (C : PositiveContinuation h []) : Prop :=
  ∀ x, h x = true → ∃ n, x ∈ C.history n

def GenerationInLimit (H : HypothesisClass X) : Prop :=
  ∃ G : Generator X, ∀ h, H h → ∀ C : PositiveContinuation h [], C.Enumerates →
    ∃ B, ∀ n, B ≤ n → h (G.output (C.history n)) = true

def ZeroRateGeneration (H : HypothesisClass X) : Prop :=
  ∃ G : Generator X, ∀ h, H h → ∀ C : PositiveContinuation h [], C.Enumerates →
    NatSublinear (fun n => mistakes h (G.play (C.history n)))

theorem PositiveContinuation.length {h : Hypothesis X} {xs : List X}
    (C : PositiveContinuation h xs) (n : Nat) : (C.history n).length = xs.length+n := by
  induction n with
  | zero => simp [C.start]
  | succ n ih =>
    obtain ⟨x, _, _, he⟩ := C.step n
    rw [he]
    simp [ih, Nat.add_assoc]

theorem PositiveContinuation.mistakes_succ {h : Hypothesis X} {xs : List X}
    (C : PositiveContinuation h xs) (G : Generator X) (n : Nat) :
    mistakes h (G.play (C.history (n+1))) =
      loss h (G.output (C.history n)) + mistakes h (G.play (C.history n)) := by
  obtain ⟨x, _, _, he⟩ := C.step n
  rw [he]
  rfl

theorem lastMistake_bound_total (G : Generator X) (h : Hypothesis X) (B : Nat)
    (hb : LastMistakeBound G h B) (xs : List X) (hn : xs.Nodup)
    (hr : Realizes h (G.play xs)) : mistakes h (G.play xs) ≤ B := by
  induction xs with
  | nil => simp [Generator.play, mistakes]
  | cons x xs ih =>
    by_cases ht : B ≤ xs.length
    · have hp := hb xs (List.nodup_cons.mp hn).2 hr.2 ht
      have hi := ih (List.nodup_cons.mp hn).2 hr.2
      simpa [Generator.play, mistakes, loss_of_positive h _ hp] using hi
    · have hm := mistakes_le_length h (G.play (x::xs))
      have hlen : (G.play (x::xs)).length = (x::xs).length := by
        have hd := congrArg List.length (G.demonstrations_play (x::xs))
        simpa [demonstrations] using hd
      simp only [List.length_cons] at hlen
      omega

theorem uniform_implies_nonuniform (H : HypothesisClass X) :
    UniformGeneration H → NonuniformGeneration H := by
  rintro ⟨G, B, hb⟩
  exact ⟨G, fun h hh => ⟨B, hb h hh⟩⟩

theorem uniform_implies_mistake_bounded (H : HypothesisClass X) :
    UniformGeneration H → UniformMistakeBounded H := by
  rintro ⟨G, B, hb⟩
  exact ⟨G, B, fun xs hn h hh hr => lastMistake_bound_total G h B (hb h hh) xs hn hr⟩

theorem mistake_bounded_implies_no_regret (H : HypothesisClass X) :
    UniformMistakeBounded H → RealizableNoRegret H := by
  rintro ⟨G, B, hb⟩
  refine ⟨G, fun k => ⟨k*B, ?_⟩⟩
  intro xs hn hl h hh hr
  exact Nat.le_trans (Nat.mul_le_mul_left k (hb xs hn h hh hr)) hl

theorem nonuniform_implies_limit (H : HypothesisClass X) :
    NonuniformGeneration H → GenerationInLimit H := by
  rintro ⟨G, hg⟩
  refine ⟨G, fun h hh C _ => ?_⟩
  obtain ⟨B, hb⟩ := hg h hh
  refine ⟨B, fun n hn => hb _ (C.nodup (by simp) n) (C.realizes G trivial n) ?_⟩
  simpa [C.length] using hn

/-- A bounded nondecreasing integer loss sequence stabilizes, hence has a last mistake. -/
theorem bounded_play_eventually_correct (G : Generator X) (h : Hypothesis X)
    (C : PositiveContinuation h []) (B : Nat)
    (hb : ∀ n, mistakes h (G.play (C.history n)) ≤ B) :
    ∃ N, ∀ n, N ≤ n → h (G.output (C.history n)) = true := by
  classical
  let f := fun n => mistakes h (G.play (C.history n))
  have hzero : ∃ n, f n = 0 := ⟨0, by simp [f, C.start, Generator.play, mistakes]⟩
  have hs := thresholdMax_spec (fun q => ∃ n, f n = q) hzero B
  obtain ⟨N, hN⟩ := hs.1
  have hmono : ∀ i j, i ≤ j → f i ≤ f j := by
    apply nat_mono_of_succ
    intro n
    have he := C.mistakes_succ G n
    dsimp [f]
    omega
  refine ⟨N, fun n hn => ?_⟩
  have hm := hmono N n hn
  have hmax := hs.2 (f (n+1)) (hb (n+1)) ⟨n+1,rfl⟩
  have hstep := C.mistakes_succ G n
  have hl : loss h (G.output (C.history n)) = 0 := by
    dsimp [f] at hm hmax hN
    omega
  unfold loss at hl
  cases he : h (G.output (C.history n)) <;> simp_all

theorem mistake_bounded_implies_limit (H : HypothesisClass X) :
    UniformMistakeBounded H → GenerationInLimit H := by
  rintro ⟨G, B, hb⟩
  refine ⟨G, fun h hh C _ => bounded_play_eventually_correct G h C B ?_⟩
  exact fun n => hb _ (C.nodup (by simp) n) h hh (C.realizes G trivial n)

theorem no_regret_implies_zero_rate (H : HypothesisClass X) :
    RealizableNoRegret H → ZeroRateGeneration H := by
  rintro ⟨G, hg⟩
  refine ⟨G, fun h hh C _ k => ?_⟩
  obtain ⟨N, hN⟩ := hg k
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN (C.history n) (C.nodup (by simp) n) (by simpa [C.length] using hn)
    h hh (C.realizes G trivial n)
  simpa [C.length] using hb

theorem cutoff_play_bound (G : Generator X) (h : Hypothesis X) (C : PositiveContinuation h [])
    (B : Nat) (hb : ∀ n, B ≤ n → h (G.output (C.history n)) = true) :
    ∀ n, mistakes h (G.play (C.history n)) ≤ B := by
  intro n
  induction n with
  | zero => simp [C.start, Generator.play, mistakes]
  | succ n ih =>
    rw [C.mistakes_succ]
    by_cases ht : B ≤ n
    · simpa [loss_of_positive h _ (hb n ht)] using ih
    · have hm := mistakes_le_length h (G.play (C.history n))
      have hd := congrArg List.length (G.demonstrations_play (C.history n))
      simp only [demonstrations, List.length_map, C.length, List.length_nil, Nat.zero_add] at hd
      have hl := loss_le_one h (G.output (C.history n))
      omega

theorem limit_implies_zero_rate (H : HypothesisClass X) :
    GenerationInLimit H → ZeroRateGeneration H := by
  rintro ⟨G, hg⟩
  refine ⟨G, fun h hh C he k => ?_⟩
  obtain ⟨B, hb⟩ := hg h hh C he
  exact ⟨k*B, fun n hn => Nat.le_trans (Nat.mul_le_mul_left k (cutoff_play_bound G h C B hb n)) hn⟩

private theorem cofinite_realizes_of_avoid (G : Generator X) (R : Finset X)
    (xs : List X) (ha : ∀ x ∈ xs, x ∉ R) : Realizes (Blocks.cofiniteHypothesis R) (G.play xs) := by
  classical
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨?_, ih (fun y hy => ha y (by simp [hy]))⟩
    have hx := ha x (by simp)
    simpa [Blocks.cofiniteHypothesis] using hx

/-- Singleton exclusions allow an adversary to place a mistake after any proposed cutoff. -/
theorem singleton_exclusions_not_uniform (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (hsingle : ∀ z, H (Blocks.cofiniteHypothesis {z})) :
    ¬ UniformGeneration H := by
  classical
  rintro ⟨G, B, hb⟩
  obtain ⟨h, hh⟩ := hne
  let C := positiveContinuation H hu h hh []
  let xs := C.history B
  let z := G.output xs
  have hn : xs.Nodup := C.nodup (by simp) B
  have hr : Realizes (Blocks.cofiniteHypothesis {z}) (G.play xs) := by
    apply cofinite_realizes_of_avoid
    intro x hx
    simp only [Finset.mem_singleton]
    intro he
    subst x
    exact G.fresh xs hx
  have he := hb _ (hsingle z) xs hn hr (by simp [xs, C.length])
  simp [z, Blocks.cofiniteHypothesis] at he

theorem compactness_one_strict_uniform :
    UniformMistakeBounded (Blocks.BoundedClass (fun n => n+1) 1) ∧
      ¬ UniformGeneration (Blocks.BoundedClass (fun n => n+1) 1) := by
  have hs : ∀ n : Nat, 0 < n+1 := by omega
  constructor
  · obtain ⟨G, hg⟩ := Blocks.bounded_uniform_upper (fun n => n+1) hs 1
    exact ⟨G, 1, hg⟩
  · apply singleton_exclusions_not_uniform _ (Blocks.bounded_uus _ hs 1) (Blocks.bounded_nonempty _ 1)
    intro z
    refine ⟨{z}, ?_, by simp, rfl⟩
    apply Blocks.separated_admissible
    intro x hx y hy _
    exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm

theorem compactness_infinite_strict_mistake_bound :
    RealizableNoRegret (Blocks.Class (fun n => n+1) (fun _ => 1)) ∧
      ¬ UniformMistakeBounded (Blocks.Class (fun n => n+1) (fun _ => 1)) := by
  let H := Blocks.Class (fun n => n+1) (fun _ => 1)
  have hu := Blocks.compactness_gap_infinite.2.1
  have hne := Blocks.nonempty_class (fun n => n+1) (fun _ => 1)
  constructor
  · apply (realizable_no_regret_iff_sublinear H hu hne).mpr
    intro k
    refine ⟨max 1 k, fun t ht => ?_⟩
    have he := Blocks.compactness_gap_infinite.2.2.1 t (by omega)
    change k * MF H t ≤ t
    change MF H t = 1 at he
    rw [he]
    omega
  · rintro ⟨G, B, hg⟩
    have hn := (realizable_uniform_characterization H hu hne B).mpr ⟨G, hg⟩
    exact hn (Blocks.compactness_gap_infinite.2.2.2 (B+1))

theorem cofinite_nonuniform_not_no_regret :
    NonuniformGeneration Cofinite.H ∧ ¬ RealizableNoRegret Cofinite.H := by
  constructor
  · refine ⟨Cofinite.generator, fun h hh => ?_⟩
    obtain ⟨B, hb⟩ := Cofinite.nonuniform_generation h hh
    exact ⟨B, fun xs _ _ hl => hb xs hl⟩
  · intro hnr
    have hs := (realizable_no_regret_iff_sublinear Cofinite.H Cofinite.uus
      ⟨Cofinite.hypothesis [], [], rfl⟩).mp hnr
    obtain ⟨N, hN⟩ := hs 2
    have hb := hN (N+1) (by omega)
    rw [(Cofinite.dimensions_eq_horizon (N+1)).1] at hb
    omega

/-- A single class witnesses that both limit and zero-rate generation can hold
without realizable no-regret generation or uniform total-mistake bounds. -/
theorem cofinite_comparison_witness :
    NonuniformGeneration Cofinite.H ∧ GenerationInLimit Cofinite.H ∧
    ZeroRateGeneration Cofinite.H ∧ ¬ RealizableNoRegret Cofinite.H ∧
    ¬ UniformMistakeBounded Cofinite.H ∧ ¬ UniformGeneration Cofinite.H := by
  obtain ⟨hn, hr⟩ := cofinite_nonuniform_not_no_regret
  have hl := nonuniform_implies_limit Cofinite.H hn
  exact ⟨hn, hl, limit_implies_zero_rate Cofinite.H hl, hr,
    fun hm => hr (mistake_bounded_implies_no_regret Cofinite.H hm),
    fun hu => hr (mistake_bounded_implies_no_regret Cofinite.H (uniform_implies_mistake_bounded Cofinite.H hu))⟩

/-- The finite-prefix cutoff definition is equivalent to the manuscript's
cutoff on all infinite realizable plays, by UUS extension of the same target. -/
theorem lastMistakeBound_iff_infinite (H : HypothesisClass X) (hu : UUS H)
    (G : Generator X) (h : Hypothesis X) (hh : H h) (B : Nat) :
    LastMistakeBound G h B ↔
      ∀ C : PositiveContinuation h [], ∀ n, B ≤ n → h (G.output (C.history n)) = true := by
  constructor
  · intro hb C n hn
    exact hb _ (C.nodup (by simp) n) (C.realizes G trivial n) (by simpa [C.length] using hn)
  · intro hb xs hn hr hlen
    let C := positiveContinuation H hu h hh xs
    obtain ⟨D, hd⟩ := C.embed G hn hr
    have he : D.history xs.length = xs := by simpa [C.start] using hd 0
    simpa [he] using hb D xs.length hlen

end PredictionToGeneration
