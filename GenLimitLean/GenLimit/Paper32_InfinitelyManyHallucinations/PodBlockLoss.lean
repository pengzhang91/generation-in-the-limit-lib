import GenLimit.Paper32_InfinitelyManyHallucinations.DeletionChain
import GenLimit.Paper32_InfinitelyManyHallucinations.DescendingBlocks

/-! # Why no new pod can capture the interior of a descending input block -/
namespace GenLimit.InfinitelyManyHallucinations.Pods.Counterexample
open Set
open scoped Classical

private theorem reset_in_block {n s t : ℕ} (hs : border n ≤ s) (hst : s < t)
    (ht : t < border (n+1)) (k : ℕ) :
    let old := chain family (input.stage (s+1))
    let new := chain family (input.stage (t+1))
    new (advance old new k) = Iio (border n) ∪ Ici (word t) := by
  let a := word t
  have hs' := word_at hs (hst.trans ht)
  have ht' := word_at (hs.trans hst.le) ht
  have lower : border n ≤ a := by dsimp [a]; omega
  have below : a < word s := by dsimp [a]; omega
  have upper : a < border (n+1) := by dsimp [a]; omega
  have same (x : ℕ) (hx : x < a) : x ∈ input.stage (s+1) ↔ x ∈ input.stage (t+1) := by
    rw [block_stage hs (hst.trans ht),block_stage (hs.trans hst.le) ht]
    change x < _ ∨ _ ≤ _ ∧ _ ↔ x < _ ∨ a ≤ _ ∧ _
    omega
  have no : a ∉ input.stage (s+1) := by rw [block_stage hs (hst.trans ht)]; omega
  have yes : a ∈ input.stage (t+1) := (block_stage (hs.trans hst.le) ht a).mpr (Or.inr ⟨le_rfl,upper⟩)
  dsimp only
  rw [identified_at_change same no yes]
  ext x
  change (x ∈ input.stage (t+1) ∨ word t ≤ x) ↔ x < border n ∨ word t ≤ x
  rw [block_stage (hs.trans hst.le) ht]
  tauto

private noncomputable abbrev tick (R : Set ℕ) := Nat.nth (safe R)

private theorem tick_gap {R : Set ℕ} (near : ∀ t, safe R t ∨ safe R (t+1))
    (inf : (setOf (safe R)).Infinite) (u : ℕ) : tick R (u+1) ≤ tick R u + 2 := by
  let v := tick R u
  have hbase : Nat.count (safe R) v = u := Nat.count_nth_of_infinite inf _
  have hv : safe R v := Nat.nth_mem_of_infinite inf _
  have next {m : ℕ} (hvm : v < m) (hm : safe R m) : tick R (u+1) ≤ m := by
    have c := Nat.count_strict_mono hv hvm
    have h := (Nat.nth_strictMono inf).monotone (show u+1 ≤ Nat.count (safe R) m by omega)
    simpa only [Nat.nth_count hm] using h
  rcases near (v+1) with h|h
  · exact (next (by omega : v < v+1) h).trans (by omega)
  · exact next (by omega) h

private theorem tick_start {R : Set ℕ} (near : ∀ t, safe R t ∨ safe R (t+1))
    (inf : (setOf (safe R)).Infinite) : tick R 0 ≤ 1 := by
  have lower {m : ℕ} (hm : safe R m) : tick R 0 ≤ m := by
    have h := (Nat.nth_strictMono inf).monotone (Nat.zero_le (Nat.count (safe R) m))
    simpa only [Nat.nth_count hm] using h
  rcases near 0 with h|h
  · exact (lower h).trans (by decide)
  · exact lower h

theorem late_pod_outside {R : Set ℕ} (near : ∀ t, safe R t ∨ safe R (t+1))
    (inf : (setOf (safe R)).Infinite) {n t : ℕ} (lo : border n+6 ≤ t) (hi : t < border (n+1))
    (safe_t : safe R t) {x : ℕ} (small : x < border (n+1))
    (mem : x ∈ proposalSet (chains family input R) (Nat.count (safe R) t)) :
    x ∈ input.stage (t+1) := by
  let F := chains family input R
  let u := Nat.count (safe R) t
  have here : tick R u = t := Nat.nth_count safe_t
  have two : 2 ≤ u := by
    by_contra! h
    have mono := (Nat.nth_strictMono inf).monotone (show u ≤ 1 by omega)
    change tick R u ≤ tick R 1 at mono
    have g : tick R 1 ≤ tick R 0 + 2 := tick_gap near inf 0
    have := tick_start near inf
    omega
  obtain ⟨v,hv⟩ : ∃ v, u = v+2 := ⟨u-2,by omega⟩
  have e : tick R (v+2) = t := hv ▸ here
  have g1 := tick_gap near inf v
  have g2 : tick R (v+2) ≤ tick R (v+1)+2 := tick_gap near inf (v+1)
  have s1 : tick R v < tick R (v+1) := Nat.nth_strictMono inf (by omega)
  have s2 : tick R (v+1) < tick R (v+2) := Nat.nth_strictMono inf (by omega)
  have lo1 : border n ≤ tick R v := by omega
  have lo2 := lo1.trans s1.le
  have old : identified F (v+1) = Iio (border n) ∪ Ici (word (tick R (v+1))) :=
    reset_in_block lo1 s1 (s2.trans (e.trans_lt hi)) _
  have new : identified F (v+2) = Iio (border n) ∪ Ici (word t) := by
    simpa only [← e] using reset_in_block lo2 s2 (e.trans_lt hi) (cursor F (v+1))
  have decreasing : word t ≤ word (tick R (v+1)) := by
    rw [word_at (by omega : border n ≤ t) hi,word_at lo2 (s2.trans (e.trans_lt hi))]
    omega
  have sub : identified F (v+1) ⊆ identified F (v+2) := by
    rw [old,new]
    exact Set.union_subset_union_right _ (Set.Ici_subset_Ici.mpr decreasing)
  change x ∈ proposalSet F u at mem
  rw [hv] at mem
  change x ∈ aggressive _ _ _ _ at mem
  unfold aggressive at mem
  have hmem : x ∈ identified F (v+2) := by
    split at mem
    · exact sub mem
    · simpa only [if_pos (show F (v+1) (cursor F (v+1)) ⊆ F (v+2) (cursor F (v+2)) from sub)] using mem
  rw [new] at hmem
  rw [block_stage (by omega : border n ≤ t) hi]
  exact hmem.elim Or.inl (fun h => Or.inr ⟨h,small⟩)

end GenLimit.InfinitelyManyHallucinations.Pods.Counterexample
