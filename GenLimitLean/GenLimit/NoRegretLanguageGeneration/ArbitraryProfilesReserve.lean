import GenLimit.NoRegretLanguageGeneration.BlockReserve

namespace PredictionToGeneration.Blocks
open Classical

theorem admissible_insert {size : Nat → Nat} (capacity : Nat → Nat)
    (R : Finset (Space size)) (z : Space size) (ha : Admissible capacity R)
    (hz : (inBlock R (block z)).card < capacity (block z)) :
    Admissible capacity (insert z R) := by
  intro n
  by_cases hn : block z = n
  · subst n
    have he : inBlock (insert z R) (block z) = insert z (inBlock R (block z)) := by
      ext x; simp [inBlock]; aesop
    rw [he]
    have hc := Finset.card_insert_le z (inBlock R (block z))
    omega
  · have he : inBlock (insert z R) n = inBlock R n := by
      ext x; simp [inBlock]; aesop
    rw [he]
    exact ha n

noncomputable def smallSeen {size : Nat → Nat} (small : Finset (Space size))
    (τ : Trajectory (Space size)) : Finset (Space size) := (demonstrations τ).toFinset ∩ small

theorem smallSeen_mono {size : Nat → Nat} (small : Finset (Space size))
    (τ : Trajectory (Space size)) (z x : Space size) :
    (smallSeen small τ).card ≤ (smallSeen small ((z,x)::τ)).card := by
  apply Finset.card_le_card
  intro y hy
  simp only [smallSeen, Finset.mem_inter, List.mem_toFinset, demonstrations, List.map_cons,
    List.mem_cons] at hy ⊢
  exact ⟨Or.inr hy.1, hy.2⟩

theorem smallSeen_copy {size : Nat → Nat} (small : Finset (Space size))
    (τ : Trajectory (Space size)) (z : Space size) (hz : Fresh τ z) (hs : z ∈ small) :
    (smallSeen small ((z,z)::τ)).card = (smallSeen small τ).card + 1 := by
  have he : smallSeen small ((z,z)::τ) = insert z (smallSeen small τ) := by
    ext x
    simp [smallSeen, demonstrations]
    aesop
  rw [he, Finset.card_insert_of_notMem]
  intro hh
  exact hz (List.mem_toFinset.mp (Finset.mem_inter.mp hh).1)

theorem reserve_keeps_forcing {size : Nat → Nat} [Infinite (Space size)]
    (capacity : Nat → Nat) (R : Finset (Space size)) (ha : Admissible capacity R)
    (m k : Nat) (τ : Trajectory (Space size))
    (hr : Realizes (cofiniteHypothesis R) τ) (hm : m ≤ mistakes (cofiniteHypothesis R) τ) :
    Forces (RealizableBad (Class size capacity) m) k τ := by
  induction k generalizing τ with
  | zero => exact ⟨cofiniteHypothesis R, ⟨R, ha, rfl⟩, hr, hm⟩
  | succ k ih =>
    intro z hz
    obtain ⟨x, hx, hp⟩ := cofinite_uus R (demonstrations τ)
    refine ⟨x, hx, ih ((z,x)::τ) ⟨hp, hr⟩ ?_⟩
    simp only [mistakes]
    omega

/-- Finite reserve adversary: every uncounted copy consumes a point in the
finite union of blocks whose capacity is smaller than the target budget. -/
theorem reserve_finite_forces {size : Nat → Nat} [Infinite (Space size)]
    (capacity : Nat → Nat) (m T : Nat) (small : Finset (Space size))
    (hsmall : ∀ z : Space size, capacity (block z) < m → z ∈ small)
    (hT : m + small.card ≤ T)
    (k : Nat) (R : Finset (Space size)) (τ : Trajectory (Space size))
    (ha : Admissible capacity R) (hr : Realizes (cofiniteHypothesis R) τ)
    (hcard : R.card ≤ mistakes (cofiniteHypothesis R) τ)
    (hcount : τ.length ≤ mistakes (cofiniteHypothesis R) τ + (smallSeen small τ).card)
    (hl : τ.length + k = T) : Forces (RealizableBad (Class size capacity) m) k τ := by
  induction k generalizing R τ with
  | zero =>
    have hc : (smallSeen small τ).card ≤ small.card := Finset.card_le_card Finset.inter_subset_right
    exact ⟨cofiniteHypothesis R, ⟨R, ha, rfl⟩, hr, by omega⟩
  | succ k ih =>
    by_cases hdone : m ≤ mistakes (cofiniteHypothesis R) τ
    · exact reserve_keeps_forcing capacity R ha m (k + 1) τ hr hdone
    intro z hz
    by_cases hzR : z ∈ R
    · obtain ⟨x, hx, hp⟩ := cofinite_uus R (demonstrations τ)
      have hloss : loss (cofiniteHypothesis R) z = 1 := by simp [loss, cofiniteHypothesis, hzR]
      have hs := smallSeen_mono small τ z x
      refine ⟨x, hx, ih R ((z,x)::τ) ha ⟨hp, hr⟩ ?_ ?_ ?_⟩
      · simp only [mistakes, hloss]; omega
      · simp only [mistakes, hloss, List.length_cons]; omega
      · simp only [List.length_cons]; omega
    · by_cases hcapacity : (inBlock R (block z)).card < capacity (block z)
      · let S := insert z R
        have hS : Admissible capacity S := admissible_insert capacity R z ha hcapacity
        have hrs := cofinite_realizes_insert R τ hr z hz
        obtain ⟨x, hx, hp⟩ := cofinite_uus S (demonstrations τ)
        have hm := cofinite_mistakes_mono (Finset.subset_insert z R) τ
        have hloss : loss (cofiniteHypothesis S) z = 1 := by simp [S, loss, cofiniteHypothesis]
        have hScard : S.card = R.card + 1 := Finset.card_insert_of_notMem hzR
        have hs := smallSeen_mono small τ z x
        refine ⟨x, hx, ih S ((z,x)::τ) hS ⟨hp, hrs⟩ ?_ ?_ ?_⟩
        · simp only [mistakes, hloss]; dsimp [S] at *; omega
        · simp only [mistakes, hloss, List.length_cons]; dsimp [S] at *; omega
        · simp only [List.length_cons]; omega
      · have hc : (inBlock R (block z)).card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
        have hzsmall : z ∈ small := hsmall z (by omega)
        have hs := smallSeen_copy small τ z hz hzsmall
        have hloss : loss (cofiniteHypothesis R) z = 0 := by simp [loss, cofiniteHypothesis, hzR]
        refine ⟨z, hz, ih R ((z,z)::τ) ha ⟨by simp [cofiniteHypothesis, hzR], hr⟩ ?_ ?_ ?_⟩
        · simpa only [mistakes, hloss, Nat.zero_add] using hcard
        · simp only [mistakes, hloss, List.length_cons]; omega
        · simp only [List.length_cons]; omega

theorem mf_lower (size capacity : Nat → Nat) (hpositive : ∀ n, 0 < size n)
    (m T : Nat) (small : Finset (Space size))
    (hsmall : ∀ z : Space size, capacity (block z) < m → z ∈ small)
    (hT : m + small.card ≤ T) : m ≤ MF (Class size capacity) T := by
  letI := space_infinite size hpositive
  have hf : MFForces (Class size capacity) T m :=
    reserve_finite_forces capacity m T small hsmall hT T ∅ []
      (by intro n; simp [inBlock]) trivial (by simp [mistakes]) (by simp) (by simp)
  exact (mf_spec _ (uus size capacity hpositive) (nonempty_class size capacity) T).2 m hf

end PredictionToGeneration.Blocks
