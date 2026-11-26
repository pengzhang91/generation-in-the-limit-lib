import GenLimit.Paper32_InfinitelyManyHallucinations.SingletonRounds

/-! # Scheduling replacements without losing ordered density

At the next exploration (number j ≥ 1) we may replace a virtual output only
after time j², and only if it avoids the first j² ranks of each of the first j
target orders. An eventually injective virtual stream always provides such
opportunities. Replacements have zero relative density in each target,
including when the observed examples arrive very slowly.
-/

namespace GenLimit.InfinitelyManyHallucinations
namespace SparseReplacement

open Set Filter KleinbergWei
open scoped Classical Topology

def Allowed (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) (t c : ℕ) : Prop :=
  (c+1)^2 ≤ t+1 ∧ ∀ z ≤ c, ∀ j < (c+1)^2, w t ≠ (O z).enumeration j

noncomputable def count (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => let c := count O w n; if Allowed O w n c then c+1 else c

def Marked (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) (t : ℕ) : Prop :=
  Allowed O w t (count O w t)

theorem count_succ (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) (t : ℕ) :
    count O w (t+1) = count O w t + if Marked O w t then 1 else 0 := by
  unfold Marked
  simp only [count]
  split <;> simp_all

theorem count_prefix (O : ℕ → OrderedLanguage) {u v : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, u i = v i) : count O u n = count O v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hc := ih (fun i hi => h i (by omega))
    simp only [count, Allowed, hc, h n (by omega : n < n+1)]
    split <;> rfl

theorem marked_prefix (O : ℕ → OrderedLanguage) {u v : ℕ → ℕ} {n : ℕ}
    (h : ∀ i ≤ n, u i = v i) : Marked O u n ↔ Marked O v n := by
  simp only [Marked, Allowed, count_prefix O (fun i (hi : i < n) => h i hi.le), h n le_rfl]

theorem count_mono (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) : Monotone (count O w) :=
  monotone_nat_of_le_succ fun n => by rw [count_succ]; omega

theorem count_injOn (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) :
    Set.InjOn (count O w) {t | Marked O w t} := by
  have lt {a b : ℕ} (hab : a < b) (ha : Marked O w a) : count O w a < count O w b := by
    have hm := count_mono O w (show a+1 ≤ b from hab)
    rw [count_succ, if_pos ha] at hm
    exact hm
  intro a ha b hb h
  rcases lt_trichotomy a b with hl|he|hl
  · exact ((lt hl ha).ne h).elim
  · exact he
  · exact ((lt hl hb).ne h.symm).elim

theorem count_le_sqrt (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) (n : ℕ) :
    count O w n ≤ n.sqrt := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    rw [count_succ]
    by_cases hm : Marked O w n
    · rw [if_pos hm]
      exact Nat.le_sqrt.mpr (by simpa [pow_two] using hm.1)
    · simpa [hm] using ih.trans (Nat.sqrt_le_sqrt (Nat.le_succ n))

def rounds (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) : Set ℕ :=
  {n | ∃ t, n = t+1 ∧ Marked O w t}

@[simp] theorem mem_round (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) (t : ℕ) :
    t+1 ∈ rounds O w ↔ Marked O w t := by simp [rounds]

theorem exploration_eq_count (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) (n : ℕ) :
    explorationCount (rounds O w) n = count O w n := by
  induction n with
  | zero => simp [explorationCount, count]
  | succ n ih => simp only [explorationCount_succ, ih, count_succ, mem_round]

theorem sparse_time (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) :
    Tendsto (fun n : ℕ => (explorationCount (rounds O w) n : ℝ) / n) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => by positivity) _ tendsto_natSqrt_div_self_zero
  intro n
  rw [exploration_eq_count]
  exact div_le_div_of_nonneg_right (by exact_mod_cast count_le_sqrt O w n) (by positivity)

theorem marked_infinite (O : ℕ → OrderedLanguage) (w : ℕ → ℕ)
    (avoid : ∀ F : Finset ℕ, ∀ᶠ t in atTop, w t ∉ F) : {t | Marked O w t}.Infinite := by
  intro hf
  obtain ⟨B,hB⟩ := hf.bddAbove
  have none (t : ℕ) (ht : B < t) : ¬Marked O w t := fun hm => ht.not_ge (hB hm)
  let c := count O w (B+1)
  have stable (t : ℕ) (ht : B+1 ≤ t) : count O w t = c := by
    induction t,ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [count_succ, if_neg (none t ht), Nat.add_zero, ih]
  let F := (Finset.range (c+1)).biUnion fun z =>
    (Finset.range ((c+1)^2)).image (O z).enumeration
  obtain ⟨t,ht,hs,hf⟩ := ((eventually_ge_atTop (B+1)).and
    ((eventually_ge_atTop ((c+1)^2)).and (avoid F))).exists
  apply none t ht
  unfold Marked
  rw [stable t ht]
  refine ⟨by omega, ?_⟩
  intro z hz j hj he
  apply hf
  exact Finset.mem_biUnion.mpr ⟨z,Finset.mem_range.mpr (by omega),
    Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,he.symm⟩⟩

def discarded (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) : Language :=
  w '' {t | Marked O w t}

/-- A target prefix sees at most its index plus sqrt(n) replaced words. -/
theorem prefix_discarded (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) (z n : ℕ) :
    (O z).prefixCount (discarded O w) n ≤ z + n.sqrt + 1 := by
  classical
  let S := (Finset.range n).filter (fun j => (O z).enumeration j ∈ discarded O w)
  have hit (j : ℕ) (hj : j ∈ S) : ∃ t, Marked O w t ∧ w t = (O z).enumeration j :=
    (Finset.mem_filter.mp hj).2
  let time (j : ℕ) := if h : j ∈ S then (hit j h).choose else 0
  have spec (j : ℕ) (hj : j ∈ S) : Marked O w (time j) ∧ w (time j) = (O z).enumeration j := by
    simpa only [time,dif_pos hj] using (hit j hj).choose_spec
  let slot j := count O w (time j)
  have small (j : ℕ) (hj : j ∈ S) : slot j ∈ Finset.range (z+n.sqrt+1) := by
    apply Finset.mem_range.mpr
    obtain ⟨hm,he⟩ := spec j hj
    have hjn := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    by_cases hz : z ≤ slot j
    · have hbound : (slot j+1)^2 ≤ j := le_of_not_gt (fun h => hm.2 z hz j h he)
      have hrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hbound.trans hjn.le)
      omega
    · omega
  have inject : Set.InjOn slot (↑S : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨hma,hea⟩ := spec a ha
    obtain ⟨hmb,heb⟩ := spec b hb
    exact (O z).enumeration_injective (hea.symm.trans
      ((congrArg w (count_injOn O w hma hmb hab)).trans heb))
  simpa [S, OrderedLanguage.prefixCount] using Finset.card_le_card_of_injOn slot small inject

theorem sparse_ranks (O : ℕ → OrderedLanguage) (w : ℕ → ℕ) (z : ℕ) :
    Tendsto ((O z).prefixRatio (discarded O w)) atTop (𝓝 0) := by
  have lim : Tendsto (fun n : ℕ => (z+1 : ℕ)/ (n : ℝ) + (n.sqrt : ℝ)/n) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat ((z+1 : ℕ) : ℝ)).add tendsto_natSqrt_div_self_zero
  apply squeeze_zero ((O z).prefixRatio_nonneg _) _ lim
  intro n
  by_cases hn : n = 0
  · simp [hn]
  rw [OrderedLanguage.prefixRatio, if_neg hn, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (by have := prefix_discarded O w z n; omega :
    (O z).prefixCount (discarded O w) n ≤ z+1+n.sqrt)

end SparseReplacement
end GenLimit.InfinitelyManyHallucinations
