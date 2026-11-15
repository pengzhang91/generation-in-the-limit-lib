import GenLimit.NoRegretLanguageGeneration.BlockReserve
import GenLimit.NoRegretLanguageGeneration.Nonrepeat
import GenLimit.NoRegretLanguageGeneration.Sublinear

namespace PredictionToGeneration.Blocks
open Classical

/-- The compactness-gap class with at most k invalid points, one per block. -/
noncomputable def BoundedClass (size : Nat → Nat) (k : Nat) : HypothesisClass (Space size) :=
  fun h => ∃ R : Finset (Space size), Admissible (fun _ => 1) R ∧ R.card ≤ k ∧
    h = cofiniteHypothesis R

theorem bounded_subset (size : Nat → Nat) (k : Nat) (h : Hypothesis (Space size))
    (hh : BoundedClass size k h) : Class size (fun _ => 1) h := by
  obtain ⟨R, hR, _, he⟩ := hh
  exact ⟨R, hR, he⟩

theorem bounded_uus (size : Nat → Nat) (hsize : ∀ n, 0 < size n) (k : Nat) :
    UUS (BoundedClass size k) :=
  fun h hh => uus size (fun _ => 1) hsize h (bounded_subset size k h hh)

theorem bounded_nonempty (size : Nat → Nat) (k : Nat) : ∃ h, BoundedClass size k h := by
  refine ⟨cofiniteHypothesis ∅, ∅, ?_, by simp, rfl⟩
  intro n
  simp [inBlock]

theorem bounded_countable (size : Nat → Nat) (k : Nat) : Countable {h // BoundedClass size k h} := by
  letI := countable_class size (fun _ => 1)
  exact Function.Injective.countable (f := fun h : {h // BoundedClass size k h} =>
    (⟨h.val, bounded_subset size k h.val h.property⟩ : {h // Class size (fun _ => 1) h}))
    (by
      intro a b he
      apply Subtype.ext
      exact congrArg (fun x : {h // Class size (fun _ => 1) h} => x.val) he)

theorem bounded_uniform_upper (size : Nat → Nat) (hsize : ∀ n, 0 < size n) (k : Nat) :
    ∃ G : Generator (Space size), UniformMistakeBound G (BoundedClass size k) k := by
  letI := space_infinite size hsize
  refine ⟨nonrepeatGenerator (Space size), ?_⟩
  intro xs hn h ⟨R, hR, hcard, he⟩ hr
  subst h
  exact Nat.le_trans (nonrepeatGenerator_cofinite_bound (Space size) R xs) hcard

theorem bounded_uniform_exact (size : Nat → Nat) (hsize : ∀ n, 0 < size n) (k m : Nat) :
    WellFoundedForces (RealizableBad (BoundedClass size k) m) [] ↔ m ≤ k := by
  letI := space_infinite size hsize
  constructor
  · intro hf
    by_contra hm
    obtain ⟨G, hg⟩ := bounded_uniform_upper size hsize k
    have hn := (realizable_uniform_characterization (BoundedClass size k)
      (bounded_uus size hsize k) (bounded_nonempty size k) k).mpr ⟨G, hg⟩
    apply hn
    apply wellFounded_forces_mono (hf := hf)
    rintro τ ⟨h, hh, hr, hb⟩
    exact ⟨h, hh, hr, by omega⟩
  · intro hm
    apply separated_reserve_forces
    intro R hR hc
    exact ⟨R, separated_admissible R hR, Nat.le_trans hc hm, rfl⟩

/-- Any class containing every singleton exclusion forces one mistake immediately. -/
theorem singleton_mf_lower (size : Nat → Nat) (hsize : ∀ n, 0 < size n)
    (H : HypothesisClass (Space size)) (hu : UUS H) (hne : ∃ h, H h)
    (hsingle : ∀ z, H (cofiniteHypothesis {z})) (T : Nat) (hT : 1 ≤ T) : 1 ≤ MF H T := by
  letI := space_infinite size hsize
  have hf : MFForces H 1 1 := by
    intro z hz
    obtain ⟨x, hx, hp⟩ := cofinite_uus ({z} : Finset (Space size)) []
    refine ⟨x, hx, cofiniteHypothesis {z}, hsingle z, ⟨hp, trivial⟩, ?_⟩
    simp [mistakes, loss, cofiniteHypothesis]
  exact Nat.le_trans ((mf_spec H hu hne 1).2 1 hf)
    (nat_mono_of_succ (MF H) (mf_mono_succ H hu hne) 1 T hT)

theorem bounded_mf_upper (size : Nat → Nat) (hsize : ∀ n, 0 < size n)
    (k n T : Nat) (hlarge : 2*T ≤ size n) : MF (BoundedClass size k) T ≤ 1 := by
  let H := Class size (fun _ => 1)
  obtain ⟨G, hg⟩ := mf_generator_attained H (uus size _ hsize) (nonempty_class size _) T
  apply mf_le_of_generator_bound (BoundedClass size k) (bounded_uus size hsize k)
    (bounded_nonempty size k) T 1 G
  intro xs hn hl h hh hr
  exact Nat.le_trans (hg xs hn hl h (bounded_subset size k h hh) hr)
    (mf_upper size (fun _ => 1) hsize n T hlarge)

theorem bounded_mf_lower (size : Nat → Nat) (hsize : ∀ n, 0 < size n)
    (k T : Nat) (hk : 1 ≤ k) (hT : 1 ≤ T) : 1 ≤ MF (BoundedClass size k) T := by
  apply singleton_mf_lower size hsize (BoundedClass size k) (bounded_uus size hsize k)
    (bounded_nonempty size k) _ T hT
  intro z
  refine ⟨{z}, ?_, by simpa using hk, rfl⟩
  apply separated_admissible
  intro x hx y hy _
  simpa using (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm

/-- The positive-k finite compactness gap, with the uniform value expressed by
its exact forceable thresholds. k=0 is deliberately excluded from MF_T=1. -/
theorem compactness_gap_finite (k : Nat) (hk : 1 ≤ k) :
    Countable {h // BoundedClass (fun n => n+1) k h} ∧
    UUS (BoundedClass (fun n => n+1) k) ∧
    (∀ T, 1 ≤ T → MF (BoundedClass (fun n => n+1) k) T = 1) ∧
    (∀ m, WellFoundedForces (RealizableBad (BoundedClass (fun n => n+1) k) m) [] ↔ m ≤ k) := by
  refine ⟨bounded_countable _ k, bounded_uus _ (by intro n; omega) k, ?_, ?_⟩
  · intro T hT
    apply Nat.le_antisymm
    · exact bounded_mf_upper _ (by intro n; omega) k (2*T) T (by omega)
    · exact bounded_mf_lower _ (by intro n; omega) k T hk hT
  · exact bounded_uniform_exact _ (by intro n; omega) k

/-- Unbounded uniform complexity despite a constant finite-horizon profile. -/
theorem compactness_gap_infinite :
    Countable {h // Class (fun n => n+1) (fun _ => 1) h} ∧
    UUS (Class (fun n => n+1) (fun _ => 1)) ∧
    (∀ T, 1 ≤ T → MF (Class (fun n => n+1) (fun _ => 1)) T = 1) ∧
    (∀ m, WellFoundedForces (RealizableBad (Class (fun n => n+1) (fun _ => 1)) m) []) := by
  have hs : ∀ n : Nat, 0 < n+1 := by omega
  letI := space_infinite (fun n => n+1) hs
  refine ⟨countable_class _ _, uus _ _ hs, ?_, ?_⟩
  · intro T hT
    apply Nat.le_antisymm
    · exact mf_upper _ _ hs (2*T) T (by omega)
    · apply singleton_mf_lower _ hs _ (uus _ _ hs) (nonempty_class _ _) _ T hT
      intro z
      refine ⟨{z}, ?_, rfl⟩
      apply separated_admissible
      intro x hx y hy _
      exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
  · intro m
    apply separated_reserve_forces
    intro R hR _
    exact ⟨R, separated_admissible R hR, rfl⟩

/-- When natural numbers include zero, the zero-reserve class has profile zero,
so the positive-k condition in the gap theorem is necessary. -/
theorem compactness_zero (size : Nat → Nat) (hsize : ∀ n, 0 < size n) (T : Nat) :
    MF (BoundedClass size 0) T = 0 := by
  obtain ⟨G, hg⟩ := bounded_uniform_upper size hsize 0
  apply Nat.eq_zero_of_le_zero
  apply mf_le_of_generator_bound (BoundedClass size 0) (bounded_uus size hsize 0)
    (bounded_nonempty size 0) T 0 G
  intro xs hn _ h hh hr
  exact hg xs hn h hh hr

end PredictionToGeneration.Blocks
