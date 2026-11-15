import GenLimit.NoRegretLanguageGeneration.FiniteMinimax

namespace PredictionToGeneration

/-- Arithmetic epsilon formulation of `f(T) = o(T)` for nonnegative integer
functions. Reciprocal positive integers are cofinal among positive epsilons. -/
def NatSublinear (f : Nat → Nat) : Prop :=
  ∀ k : Nat, ∃ N : Nat, ∀ t : Nat, N ≤ t → k * f t ≤ t

noncomputable def floorRoot (t : Nat) : Nat :=
  thresholdMax (fun m => m * m ≤ t) t

theorem floorRoot_square (t : Nat) : floorRoot t * floorRoot t ≤ t :=
  (thresholdMax_spec (fun m => m * m ≤ t) (by simp) t).1

theorem floorRoot_lower (k t : Nat) (hkt : k ≤ t) (hs : k * k ≤ t) : k ≤ floorRoot t :=
  (thresholdMax_spec (fun m => m * m ≤ t) (by simp) t).2 k hkt hs

theorem floorRoot_mono {s t : Nat} (hst : s ≤ t) : floorRoot s ≤ floorRoot t := by
  apply floorRoot_lower
  · exact Nat.le_trans (thresholdMax_le _ s) hst
  · exact Nat.le_trans (floorRoot_square s) hst

theorem floorRoot_unbounded (k : Nat) : ∃ t, k < floorRoot t := by
  refine ⟨(k + 1) * (k + 1) + (k + 1), ?_⟩
  have ht := floorRoot_lower (k + 1) ((k + 1) * (k + 1) + (k + 1)) (by omega) (by omega)
  omega

theorem floorRoot_sublinear : NatSublinear floorRoot := by
  intro k
  refine ⟨max k (k * k), ?_⟩
  intro t ht
  have hr := floorRoot_lower k t (by omega) (by omega)
  exact Nat.le_trans (Nat.mul_le_mul_right (floorRoot t) hr) (floorRoot_square t)

theorem natSublinear_max {f g : Nat → Nat} (hf : NatSublinear f) (hg : NatSublinear g) :
    NatSublinear (fun t => max (f t) (g t)) := by
  intro k
  obtain ⟨N, hN⟩ := hf k
  obtain ⟨M, hM⟩ := hg k
  refine ⟨max N M, ?_⟩
  intro t ht
  have hn := hN t (by omega)
  have hm := hM t (by omega)
  change k * max (f t) (g t) ≤ t
  by_cases he : f t ≤ g t
  · rw [Nat.max_eq_right he]; exact hm
  · rw [Nat.max_eq_left (by omega)]; exact hn

theorem natSublinear_one : NatSublinear (fun _ => 1) := by
  intro k
  exact ⟨k, by intro t ht; simpa using ht⟩

noncomputable def sublinearEnvelope (f : Nat → Nat) (t : Nat) : Nat :=
  max 1 (max (floorRoot t) (f t))

theorem sublinearEnvelope_sublinear {f : Nat → Nat} (hf : NatSublinear f) :
    NatSublinear (sublinearEnvelope f) :=
  natSublinear_max natSublinear_one (natSublinear_max floorRoot_sublinear hf)

theorem sublinearEnvelope_mono {f : Nat → Nat}
    (hf : ∀ i j, i ≤ j → f i ≤ f j) (i j : Nat) (hij : i ≤ j) :
    sublinearEnvelope f i ≤ sublinearEnvelope f j := by
  have hr := floorRoot_mono hij
  have hm := hf i j hij
  unfold sublinearEnvelope
  omega

theorem sublinearEnvelope_unbounded (f : Nat → Nat) (k : Nat) :
    ∃ t, k < sublinearEnvelope f t := by
  obtain ⟨t, ht⟩ := floorRoot_unbounded k
  refine ⟨t, ?_⟩
  unfold sublinearEnvelope
  omega

theorem sublinearEnvelope_positive (f : Nat → Nat) (t : Nat) : 1 ≤ sublinearEnvelope f t := by
  unfold sublinearEnvelope
  omega

theorem le_sublinearEnvelope (f : Nat → Nat) (t : Nat) : f t ≤ sublinearEnvelope f t := by
  unfold sublinearEnvelope
  omega

theorem nat_mono_of_succ (f : Nat → Nat) (hf : ∀ t, f t ≤ f (t + 1))
    (i j : Nat) (hij : i ≤ j) : f i ≤ f j := by
  induction j with
  | zero =>
    have he : i = 0 := by omega
    rw [he]
    exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · rw [he]
      exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (hf j)

end PredictionToGeneration


