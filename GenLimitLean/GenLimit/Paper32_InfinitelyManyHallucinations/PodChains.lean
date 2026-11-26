import GenLimit.Paper32_InfinitelyManyHallucinations.Definitions
import Mathlib.Data.Nat.Nth

/-! # The compressed consistency chains of Algorithms 3–5
A consistent language has rank equal to the number of earlier consistent
hypotheses. Intersecting all hypotheses of rank at most j implements the
paper's filtered list, including padding a finite list with its last entry.
The cursor and the common-predecessor search use these compressed ranks.
-/
namespace GenLimit.InfinitelyManyHallucinations.Pods

open Set
open scoped Classical

noncomputable def rank (C : LanguageFamily) (D : Language) : ℕ → ℕ :=
  Nat.count (fun i => D ⊆ C i)

def chain (C : LanguageFamily) (D : Language) (j : ℕ) : Language :=
  {x | ∀ i, D ⊆ C i → rank C D i ≤ j → x ∈ C i}

theorem descending (C : LanguageFamily) (D : Language) : Antitone (chain C D) :=
  fun _ _ h _ hx i hi hr => hx i hi (hr.trans h)

theorem data_subset (C : LanguageFamily) (D : Language) (j : ℕ) : D ⊆ chain C D j :=
  fun _ hx _ hi _ => hi hx

theorem first_infinite (C : LanguageFamily) (hi : ∀ i, (C i).Infinite) (D : Language) :
    (chain C D 0).Infinite := by
  by_cases h : ∃ i, D ⊆ C i ∧ rank C D i = 0
  · obtain ⟨i, hfit, hr⟩ := h
    apply (hi i).mono
    intro x hx j hj hjr
    have eq : rank C D i = rank C D j := by omega
    exact Nat.count_injective hfit hj eq ▸ hx
  · apply Set.infinite_univ.mono
    intro x _ i hf hr
    exact (h ⟨i,hf,by omega⟩).elim

private theorem rank_congr {C : LanguageFamily} {D L : Language} {z : ℕ}
    (h : ∀ i ≤ z, D ⊆ C i ↔ L ⊆ C i) {i : ℕ} (hi : i ≤ z) :
    rank C D i = rank C L i := by
  unfold rank
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  exact fun j hj => h j ((Finset.mem_range.mp hj).le.trans hi)

theorem chain_prefix {C : LanguageFamily} {D L : Language} {z j : ℕ}
    (h : ∀ i ≤ z, D ⊆ C i ↔ L ⊆ C i) (hL : L ⊆ C z) (hj : j ≤ rank C L z) :
    chain C D j = chain C L j := by
  have hDz := (h z le_rfl).mpr hL
  have hz := rank_congr h (i := z) le_rfl
  have before {B : Language} (hb : B ⊆ C z) {i : ℕ} (hr : rank C B i ≤ rank C B z) : i ≤ z := by
    by_contra! hlt
    exact (Nat.not_lt_of_ge hr) (Nat.count_strict_mono hb hlt)
  ext x
  constructor
  · intro hx i hi hr
    have b := before hL (hr.trans hj)
    exact hx i ((h i b).mpr hi) ((rank_congr h b).trans_le hr)
  · intro hx i hi hr
    have b := before hDz ((hr.trans hj).trans_eq hz.symm)
    exact hx i ((h i b).mp hi) ((rank_congr h b).symm.trans_le hr)

abbrev Chain := ℕ → Language

/-- At a changed chain, stop at the first differing or finite intersection.
Both an empty common prefix and a prefix of length one select rank zero. -/
private noncomputable def boundary (old new : Chain) (h : old ≠ new) : ℕ :=
  Nat.find (show ∃ j, old j ≠ new j ∨ ¬(old j).Infinite from by
    by_contra! hn
    exact h (funext fun j => (hn j).1))

private theorem before_boundary {old new : Chain} (h : old ≠ new) {j : ℕ}
    (hj : j < boundary old new h) : old j = new j ∧ (old j).Infinite := by
  simpa [not_or] using (Nat.find_min (p := fun j => old j ≠ new j ∨ ¬(old j).Infinite) _ hj)

private theorem after_prefix {old new : Chain} (h : old ≠ new) {r : ℕ}
    (hp : ∀ j ≤ r, old j = new j ∧ (old j).Infinite) : r < boundary old new h := by
  by_contra! hl
  obtain ⟨eq,hi⟩ := hp _ hl
  exact (Nat.find_spec (p := fun j => old j ≠ new j ∨ ¬(old j).Infinite) _).elim
    (fun ne => ne eq) (fun no => no hi)

noncomputable def advance (old new : Chain) (k : ℕ) : ℕ :=
  if h : old = new then if (old (k+1)).Infinite then k+1 else k
  else boundary old new h - 1

/-- A first difference immediately after rank r forces the reset to r,
regardless of the old cursor position. -/
theorem advance_reset_at {old new : Chain} {r : ℕ}
    (shared : ∀ j ≤ r, old j = new j ∧ (old j).Infinite)
    (diff : old (r+1) ≠ new (r+1)) (k : ℕ) : advance old new k = r := by
  have ne : old ≠ new := fun h => diff (congrFun h _)
  have lo := after_prefix ne shared
  have up : boundary old new ne ≤ r+1 := by
    by_contra! hn
    exact diff (before_boundary ne hn).1
  simp only [advance,dif_neg ne]
  omega

noncomputable def cursor (F : ℕ → Chain) : ℕ → ℕ
  | 0 => 0
  | t+1 => advance (F t) (F (t+1)) (cursor F t)

def identified (F : ℕ → Chain) (t : ℕ) := F t (cursor F t)

theorem identified_infinite (F : ℕ → Chain) (h0 : ∀ t, (F t 0).Infinite) (t : ℕ) :
    (identified F t).Infinite := by
  induction t with
  | zero => exact h0 0
  | succ t ih =>
    change (F (t+1) (advance (F t) (F (t+1)) (cursor F t))).Infinite
    unfold advance
    split
    · rename_i eq
      rw [← eq]
      split <;> assumption
    · rename_i ne
      by_cases h : boundary (F t) (F (t+1)) ne = 0
      · simpa [h] using h0 (t+1)
      · obtain ⟨he,hi⟩ := before_boundary ne (j := boundary _ _ ne - 1) (by omega)
        exact he ▸ hi

private noncomputable def common (old new : Chain) (a b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (a+1)).filter fun i => ∃ j ≤ b, old i = new j

/-- Algorithm 5. In incomparable cases the largest common old-chain index
through the old cursor gives an inclusion-minimal common predecessor. -/
noncomputable def aggressive (old new : Chain) (a b : ℕ) : Language :=
  if new b ⊆ old a then old a
  else if old a ⊆ new b then new b
  else if h : (common old new a b).Nonempty then old ((common old new a b).max' h)
  else new b

theorem identified_subset_aggressive (old new : Chain) (down : Antitone new) (a b : ℕ) :
    new b ⊆ aggressive old new a b := by
  unfold aggressive
  split
  · assumption
  split
  · exact Subset.rfl
  split
  · rename_i h
    have hm := Finset.max'_mem (common old new a b) h
    obtain ⟨j,hj,eq⟩ := (Finset.mem_filter.mp hm).2
    rw [eq]
    exact down hj
  · exact Subset.rfl

noncomputable def proposalSet (F : ℕ → Chain) : ℕ → Language
  | 0 => identified F 0
  | t+1 => aggressive (F t) (F (t+1)) (cursor F t) (cursor F (t+1))

theorem proposal_infinite (F : ℕ → Chain) (down : ∀ t, Antitone (F t))
    (h0 : ∀ t, (F t 0).Infinite) (t : ℕ) : (proposalSet F t).Infinite := by
  cases t with
  | zero => exact identified_infinite F h0 0
  | succ t =>
    exact (identified_infinite F h0 (t+1)).mono
      (identified_subset_aggressive _ _ (down _) _ _)

/-- After the finite prefix through the target stabilizes, the cursor
advances to its rank in at most that many safe steps and stays below its
intersection thereafter. Consecutive selected sets are then comparable. -/
theorem eventually_safe {F : ℕ → Chain} (down : ∀ t, Antitone (F t))
    {r T : ℕ} {L : Language} (stable : ∀ t ≥ T, ∀ j ≤ r, F t j = F T j)
    (inf : (F T r).Infinite) (valid : F T r ⊆ L) :
    ∃ N, ∀ t ≥ N, proposalSet F t ⊆ L := by
  have shared (t : ℕ) (ht : T ≤ t) (j : ℕ) (hj : j ≤ r) :
      F t j = F (t+1) j ∧ (F t j).Infinite := by
    rw [stable t ht j hj,stable (t+1) (by omega) j hj]
    exact ⟨rfl,inf.mono (down T hj)⟩
  have grow (t : ℕ) (ht : T ≤ t) :
      min (cursor F t + 1) r ≤ cursor F (t+1) := by
    simp only [cursor,advance]
    split
    · split
      · exact min_le_left _ _
      · rename_i h
        have b : r < cursor F t+1 := by
          by_contra! hb
          exact h (shared t ht _ hb).2
        omega
    · rename_i ne
      have := after_prefix ne (shared t ht)
      omega
  have reaches (d : ℕ) : min d r ≤ cursor F (T+d) := by
    induction d with
    | zero => simp
    | succ d ih =>
      have := grow (T+d) (by omega)
      change min (d+1) r ≤ cursor F ((T+d)+1)
      omega
  have good (t : ℕ) (ht : T+r ≤ t) : identified F t ⊆ L := by
    have h := reaches (t-T)
    have eq : T+(t-T) = t := by omega
    rw [eq] at h
    have depth : r ≤ cursor F t := by omega
    exact (down t depth).trans ((stable t (by omega) r le_rfl).symm ▸ valid)
  refine ⟨T+r+1, ?_⟩
  rintro (_|t) ht
  · omega
  have old := good t (by omega)
  have new := good (t+1) (by omega)
  have comp : identified F (t+1) ⊆ identified F t ∨ identified F t ⊆ identified F (t+1) := by
    have compare (a b : ℕ) : F t a ⊆ F t b ∨ F t b ⊆ F t a :=
      (le_total b a).elim (fun h => Or.inl (down t h)) (fun h => Or.inr (down t h))
    by_cases he : F t = F (t+1)
    · unfold identified
      rw [← he]
      exact compare _ _
    · have hb := after_prefix he (shared t (by omega))
      have eq := (before_boundary he (j := boundary _ _ he - 1) (by omega)).1
      change F (t+1) (advance ..) ⊆ _ ∨ _ ⊆ F (t+1) (advance ..)
      simp only [advance,dif_neg he,← eq]
      exact compare _ _
  change aggressive _ _ _ _ ⊆ L
  unfold identified at comp old new
  rcases comp with h | h
  · simpa only [aggressive,if_pos h] using old
  · by_cases h' : F (t+1) (cursor F (t+1)) ⊆ F t (cursor F t)
    · simpa only [aggressive,if_pos h'] using old
    · simpa only [aggressive,if_neg h',if_pos h] using new

end GenLimit.InfinitelyManyHallucinations.Pods
