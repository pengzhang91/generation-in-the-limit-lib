import GenLimit.Paper32_InfinitelyManyHallucinations.PodGenerator

/-! # The algorithm's exact reset on the single-deletion family
The target is the whole universe. Each later candidate omits one word, in
increasing order of that word. When a batch arrives, the largest common
prefix ends just before the candidate omitting the least newly seen word.
-/
namespace GenLimit.InfinitelyManyHallucinations.Pods.Counterexample
open Set
open scoped Classical

def family : LanguageFamily
  | 0 => univ
  | x+1 => {x}ᶜ

theorem family_infinite (i : ℕ) : (family i).Infinite := by
  cases i with
  | zero => exact Set.infinite_univ
  | succ x => exact (Set.finite_singleton x).infinite_compl

private theorem fits (D : Finset ℕ) (i : ℕ) : ((D : Set ℕ) ⊆ family (i+1)) ↔ i ∉ D := by
  change _ ⊆ ({i} : Set ℕ)ᶜ ↔ _
  simp [Set.subset_def]

private def gap (D : Finset ℕ) := Nat.count (fun y => y ∉ D)

private theorem rank_delete (D : Finset ℕ) (x : ℕ) : rank family D (x+1) = gap D x + 1 := by
  induction x with
  | zero =>
    simp [rank,gap,Nat.count_succ,family,Set.subset_univ]
  | succ x ih =>
    change Nat.count _ (x+1+1) = Nat.count _ (x+1) + 1
    rw [Nat.count_succ (fun i => (D : Set ℕ) ⊆ family i) (x+1), Nat.count_succ (fun i => i ∉ D) x]
    change rank family D (x+1) + _ = gap D x + _ + 1
    rw [ih,if_congr (fits D x) rfl rfl]
    omega

private theorem mem_chain (D : Finset ℕ) (j x : ℕ) :
    x ∈ chain family D j ↔ x ∈ D ∨ j ≤ gap D x := by
  constructor
  · intro hx
    by_cases hm : x ∈ D
    · exact Or.inl hm
    · right
      by_contra! h
      have bad := hx (x+1) ((fits D x).mpr hm) ((rank_delete D x).trans_le (by omega))
      exact bad rfl
  · intro h
    rcases h with hd|hr
    · exact data_subset family D j hd
    · rintro (_|i) hi hpos
      · trivial
      · intro e
        change x = i at e
        subst i
        rw [rank_delete] at hpos
        omega

private theorem chain_infinite (D : Finset ℕ) (j : ℕ) : (chain family D j).Infinite := by
  have inf : (setOf fun x => x ∉ D).Infinite := D.finite_toSet.infinite_compl
  let a := Nat.nth (fun x => x ∉ D) j
  have hab : (Ici a).Infinite := Set.infinite_of_forall_exists_gt (fun x => ⟨max x a + 1, by change a ≤ _; omega, by omega⟩)
  apply hab.mono
  intro x hx
  apply (mem_chain D j x).mpr ∘ Or.inr
  have h := Nat.count_monotone (fun x => x ∉ D) (show a ≤ x from hx)
  simpa only [a,Nat.count_nth_of_infinite inf] using h

private theorem gap_congr {D V : Finset ℕ} {a : ℕ}
    (same : ∀ i < a, i ∈ D ↔ i ∈ V) {x : ℕ} (hx : x ≤ a) : gap D x = gap V x := by
  simp only [gap,Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  exact fun j hj => not_congr (same j ((Finset.mem_range.mp hj).trans_le hx))

/-- The set returned by Algorithm 4 for this family after a genuine input
change. The bound a is the least newly revealed word. -/
theorem identified_at_change {D V : Finset ℕ} {a : ℕ}
    (same : ∀ i < a, i ∈ D ↔ i ∈ V) (fresh : a ∉ D) (now : a ∈ V) (k : ℕ) :
    chain family V (advance (chain family D) (chain family V) k) = (V : Set ℕ) ∪ Ici a := by
  let q := gap D a
  have changeRank : gap D a = gap V a := gap_congr same le_rfl
  have shared (j : ℕ) (hj : j ≤ q) : chain family D j = chain family V j ∧
      (chain family D j).Infinite := by
    refine ⟨?_,chain_infinite D j⟩
    ext x
    rw [mem_chain,mem_chain]
    by_cases hx : x < a
    · rw [same x hx,gap_congr same hx.le]
    · have hdx : q ≤ gap D x := Nat.count_monotone _ (by omega : a ≤ x)
      have hvx : q ≤ gap V x := changeRank.trans_le (Nat.count_monotone _ (by omega : a ≤ x))
      simp [hj.trans hdx,hj.trans hvx]
  have diff : chain family D (q+1) ≠ chain family V (q+1) := by
    intro eq
    have ha := data_subset family (V : Set ℕ) (q+1) now
    rw [← eq, mem_chain] at ha
    rcases ha with h|h
    · exact fresh h
    · omega
  rw [advance_reset_at shared diff]
  ext x
  rw [mem_chain]
  change (x ∈ V ∨ q ≤ gap V x) ↔ x ∈ V ∨ a ≤ x
  by_cases hv : x ∈ V
  · simp [hv]
  · simp only [hv,false_or]
    constructor
    · intro h
      by_contra! hh
      have := Nat.count_strict_mono (p := fun x => x ∉ V) hv hh
      change gap V x < gap V a at this
      omega
    · intro h
      exact changeRank.trans_le (Nat.count_monotone _ h)

end GenLimit.InfinitelyManyHallucinations.Pods.Counterexample
