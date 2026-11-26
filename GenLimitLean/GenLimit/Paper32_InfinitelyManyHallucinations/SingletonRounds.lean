import GenLimit.Paper32_InfinitelyManyHallucinations.Certificates

/-! # Counting fresh singleton outputs on exploration and safe rounds -/

namespace GenLimit.InfinitelyManyHallucinations

open Set Filter
open scoped Classical Topology

structure SingletonRounds (g : Exhaustion) where
  word : ℕ → ℕ
  fresh : ∀ t, word t ∉ g.stage t
  step : ∀ t, g.stage (t+1) = insert (word t) (g.stage t)

theorem explorationCount_succ (R : Set ℕ) (n : ℕ) :
    explorationCount R (n+1) = explorationCount R n + if n+1 ∈ R then 1 else 0 := by
  classical
  have h := Finset.insert_Icc_right_eq_Icc_add_one (a := 1) (b := n) (by omega)
  unfold explorationCount
  rw [← h, Finset.filter_insert]
  by_cases hm : n+1 ∈ R <;> simp [hm]

namespace SingletonRounds
variable {g : Exhaustion} (r : SingletonRounds g)
include r

theorem increment (t : ℕ) : g.increment (t+1) = {r.word t} := by
  simp [Exhaustion.increment, r.step, r.fresh]

theorem card (n : ℕ) : (g.stage n).card = n := by
  induction n with
  | zero => simp [g.stage_zero]
  | succ n ih => simp [r.step, r.fresh, ih]

theorem injective : Function.Injective r.word := by
  suffices h : ∀ i j, i < j → r.word i ≠ r.word j by
    intro a b he
    rcases lt_trichotomy a b with hlt|hab|hlt
    · exact (h a b hlt he).elim
    · exact hab
    · exact (h b a hlt he.symm).elim
  intro i j hij he
  apply r.fresh j
  rw [← he]
  exact g.monotone_stage hij (r.step i ▸ Finset.mem_insert_self _ _)

theorem infinite : g.limit.Infinite := (Set.infinite_range_of_injective r.injective).mono (by
  rintro _ ⟨n,rfl⟩
  exact g.stage_subset_limit _ (r.step n ▸ Finset.mem_insert_self _ _))

/-- Scanning for the least unused word on infinitely many rounds recovers
every word which stays eligible. Times are indexed from zero here. -/
theorem covers {R : Set ℕ} (hR : R.Infinite) (x : ℕ)
    (hsmall : x ∉ g.limit → ∀ t ∈ R, r.word t ≤ x) : x ∈ g.limit := by
  by_contra hx
  apply (hR.image r.injective.injOn)
  apply (Set.finite_Iic x).subset
  rintro y ⟨t,ht,rfl⟩
  exact hsmall hx t ht

/-- At most the exploration steps can add a non-novel word. -/
theorem fractional_novelty (A : Exhaustion) (E : ExplorationSet) {γ : ℝ}
    (quota : E.GammaAdmissible γ)
    (safe : ∀ t, t+1 ∉ E.carrier → r.word t ∉ A.stage (t+1)) :
    GammaNovel γ A g := by
  apply gammaNovel_of_nonNovel_le_exploration quota
  intro n
  rw [r.card]
  induction n with
  | zero => simp [g.stage_zero]
  | succ n ih =>
    rw [explorationCount_succ]
    by_cases he : n+1 ∈ E.carrier
    · rw [if_pos he]
      have hsub : g.stage (n+1) \ novelHistory A g (n+1) ⊆
          insert (r.word n) (g.stage n \ novelHistory A g n) := by
        intro x hx
        rw [r.step] at hx
        obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hx
        rcases Finset.mem_insert.mp hm with hx | hx
        · exact Finset.mem_insert.mpr (.inl hx)
        · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
            ⟨hx,fun h => hn (Finset.mem_union_left _ h)⟩)
      exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le ..).trans (by omega))
    · rw [if_neg he, Nat.add_zero]
      apply le_trans (Finset.card_le_card ?_) ih
      intro x hx
      obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hx
      rw [r.step] at hm
      rcases Finset.mem_insert.mp hm with hx | hx
      · subst x
        apply False.elim (hn (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨?_,safe n he⟩)))
        rw [r.increment]
        simp
      · exact Finset.mem_sdiff.mpr ⟨hx,fun h => hn (Finset.mem_union_left _ h)⟩

/-- A finite initial error budget and a sparse set of exploration rounds
suffice for cumulative precision one. -/
theorem precision {L : Language} {R : Set ℕ} {T : ℕ}
    (sparse : Tendsto (fun n : ℕ => (explorationCount R n : ℝ) / n) atTop (𝓝 0))
    (safe : ∀ t ≥ T, t+1 ∉ R → r.word t ∈ L) : lowerMembershipPrecision L g = 1 := by
  classical
  have bound (n : ℕ) : invalidCount L (g.stage n) ≤ min n T + explorationCount R n := by
    induction n with
    | zero => simp [invalidCount_eq_filter_card,g.stage_zero]
    | succ n ih =>
      rw [r.step,explorationCount_succ]
      by_cases hy : r.word n ∈ L
      · simp only [invalidCount_eq_filter_card,Finset.filter_insert,
          if_neg (not_not.mpr hy)]
        rw [← invalidCount_eq_filter_card]
        exact ih.trans (Nat.add_le_add (min_le_min_right T (Nat.le_succ n)) (by omega))
      · have inc : invalidCount L (insert (r.word n) (g.stage n)) ≤ invalidCount L (g.stage n) + 1 := by
          simp only [invalidCount_eq_filter_card, Finset.filter_insert, if_pos hy]
          exact Finset.card_insert_le ..
        apply inc.trans
        by_cases h : T ≤ n
        · have he : n+1 ∈ R := by by_contra hh; exact hy (safe n h hh)
          simp only [if_pos he]
          omega
        · omega
  have lim : Tendsto (fun n : ℕ => (T : ℝ) / n + (explorationCount R n : ℝ) / n)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).add sparse
  refine lowerMembershipPrecision_eq_one_of_error_envelope ?_ ?_ lim
  · filter_upwards [eventually_gt_atTop 0] with n hn
    simp [r.card, hn.ne']
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := invalidFraction_le_of_count_le L (bound n)
    simp only [r.card, if_neg hn.ne'] at h
    rw [← add_div]
    apply h.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.add_le_add_right (min_le_right n T) (explorationCount R n)

end SingletonRounds
end GenLimit.InfinitelyManyHallucinations
