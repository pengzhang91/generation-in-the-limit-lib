import GenLimit.Paper32_InfinitelyManyHallucinations.PodChains
import GenLimit.Paper32_InfinitelyManyHallucinations.ScheduledExploration

/-! # Safe-round indexing for the pods algorithms

At safe time t the source receives every observation since its preceding
safe round. Filtering the original list against the cumulative data gives
exactly the resulting list. No cursor update takes place on an exploration.
-/
namespace GenLimit.InfinitelyManyHallucinations.Pods
open Set Filter
open scoped Classical

def safe (R : Set ℕ) (t : ℕ) : Prop := t+1 ∉ R

theorem safe_infinite (E : ExplorationSet) : (setOf (safe E.carrier)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  intro h
  obtain ⟨n,hn⟩ := h
  by_cases he : n+2 ∈ E.carrier
  · have hnext := E.nonconsecutive _ he
    have := hn (show n+2 ∈ setOf (safe E.carrier) from hnext)
    omega
  · have := hn (show n+1 ∈ setOf (safe E.carrier) from he)
    omega

noncomputable def chains (C : LanguageFamily) (A : Exhaustion) (R : Set ℕ) (u : ℕ) : Chain :=
  chain C (A.stage (Nat.nth (safe R) u + 1) : Set ℕ)

private theorem stableData (C : LanguageFamily) (A : Exhaustion) (z : ℕ) :
    ∃ T, ∀ t ≥ T, ∀ i ≤ z, ((A.stage t : Set ℕ) ⊆ C i ↔ A.limit ⊆ C i) := by
  have each (i : ℕ) : ∃ T, ∀ t ≥ T, ((A.stage t : Set ℕ) ⊆ C i ↔ A.limit ⊆ C i) := by
    by_cases h : A.limit ⊆ C i
    · exact ⟨0,fun _ _ => ⟨fun _ => h,fun _ => (A.stage_subset_limit _).trans h⟩⟩
    · obtain ⟨x,⟨n,hx⟩,outside⟩ := Set.not_subset.mp h
      exact ⟨n,fun t ht => ⟨fun hs => (outside (hs (A.monotone_stage ht hx))).elim,
        fun hh => (h hh).elim⟩⟩
  induction z with
  | zero =>
    obtain ⟨T,hT⟩ := each 0
    exact ⟨T,fun t ht i hi => (Nat.eq_zero_of_le_zero hi) ▸ hT t ht⟩
  | succ z ih =>
    obtain ⟨T,hT⟩ := ih
    obtain ⟨N,hN⟩ := each (z+1)
    refine ⟨max N T,fun t ht i hi => ?_⟩
    rcases Nat.eq_or_lt_of_le hi with rfl|hl
    · exact hN t ((le_max_left ..).trans ht)
    · exact hT t ((le_max_right ..).trans ht) i (by omega)

theorem sets_eventually_valid {C : LanguageFamily} {A : Exhaustion} {z : ℕ} {R : Set ℕ}
    (hsafe : (setOf (safe R)).Infinite) (hi : A.limit.Infinite) (hs : A.limit ⊆ C z) :
    ∃ N, ∀ u ≥ N, proposalSet (chains C A R) u ⊆ C z := by
  obtain ⟨T,hT⟩ := stableData C A z
  let r := rank C A.limit z
  have eq (u : ℕ) (hu : T ≤ u) (j : ℕ) (hj : j ≤ r) :
      chains C A R u j = chain C A.limit j := by
    have time : u ≤ Nat.nth (safe R) u := (Nat.nth_strictMono hsafe).id_le u
    exact chain_prefix (hT _ (by omega)) hs hj
  have valid : chain C A.limit r ⊆ C z := fun _ hx => hx z hs le_rfl
  exact eventually_safe (F := chains C A R) (fun u => descending ..) (r := r) (T := T)
    (fun u hu j hj => (eq u hu j hj).trans (eq T le_rfl j hj).symm)
    (eq T le_rfl r le_rfl ▸ hi.mono (data_subset C A.limit r))
    (eq T le_rfl r le_rfl ▸ valid)

private theorem cursor_congr {F H : ℕ → Chain} {u : ℕ} (h : ∀ i ≤ u, F i = H i) :
    cursor F u = cursor H u := by
  induction u with
  | zero => rfl
  | succ n ih =>
    simp only [cursor, h n (by omega),h (n+1) le_rfl,ih (fun i hi => h i (by omega))]

theorem proposal_congr {F H : ℕ → Chain} {u : ℕ} (h : ∀ i ≤ u, F i = H i) :
    proposalSet F u = proposalSet H u := by
  cases u with
  | zero => exact congrFun (h 0 le_rfl) 0
  | succ n =>
    simp only [proposalSet, h n (by omega), h (n+1) le_rfl,
      cursor_congr h,cursor_congr (fun i (hi : i ≤ n) => h i (by omega))]

theorem proposal_at_safe_time {C : LanguageFamily} {R : Set ℕ} (hR : (setOf (safe R)).Infinite)
    {A B : Exhaustion} {t : ℕ} (ht : safe R t) (h : ∀ i ≤ t+1, A.stage i = B.stage i) :
    proposalSet (chains C A R) (Nat.count (safe R) t) =
      proposalSet (chains C B R) (Nat.count (safe R) t) := by
  apply proposal_congr
  intro i hi
  have bound := (Nat.nth_strictMono hR).monotone hi
  rw [Nat.nth_count ht] at bound
  simp only [chains,h _ (Nat.succ_le_succ bound)]

end GenLimit.InfinitelyManyHallucinations.Pods
