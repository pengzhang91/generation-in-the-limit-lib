import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.VanishingBreadth

/-! # The unordered-sample interpretation of Section 2

On the language consisting of all squares and the numbers below `n`, any
eventual property of a function of the observed set has a finite locking
sample. Before introducing `n` the adversary can preload every other member
of the next lock. Thus one presentation of the whole universe eventually
satisfies the same property at *every* intermediate round.
-/
namespace GenLimit.KleinbergWei.DensityMeasures.SetDriven
open Filter SquareTower

private theorem lock {Q : Finset ℕ → Prop} {L : Language} (hne : L.Nonempty)
    (stable : ∀ s, Presents s L → ∀ᶠ t in atTop, Q (sample s t)) :
    ∃ F : Finset ℕ, (F : Set ℕ) ⊆ L ∧
      ∀ S : Finset ℕ, F ⊆ S → (S : Set ℕ) ⊆ L → Q S := by
  classical
  by_contra! noLock
  obtain ⟨s,hs,hbad⟩ := diagonal_presentation (Support.exactPresentation_presents L hne)
    (fun _ xs ↦ ¬ Q xs.toFinset) (by
      intro _ xs hxs
      obtain ⟨S,he,hL,hbad⟩ := noLock xs.toFinset (fun x hx ↦ hxs x (by simpa using hx))
      refine ⟨xs ++ S.toList,List.prefix_append ..,Angluin.listWithin_append hxs
        (fun x hx ↦ hL (by simpa using hx)),?_⟩
      simpa [Finset.union_eq_right.mpr he] using hbad)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (stable s hs)
  obtain ⟨t,ht,hb⟩ := hbad T
  exact hb (by simpa only [textPrefix_toFinset] using hT t ht)

private theorem layer_mono (n : ℕ) : layer n ⊆ layer (n+1) :=
  Set.union_subset_union_right _ (by intro x hx; exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hx)))

private theorem layer_previous {n x : ℕ} (h : x ∈ layer (n+1)) (hne : x ≠ n) : x ∈ layer n := by
  rcases h with h | h
  · exact Or.inl h
  · have := Finset.mem_range.mp h
    exact Or.inr (Finset.mem_range.mpr (by omega))

/-- Every intermediate observation stays inside one locked interval of sets.
The following statement is uniform in the predicate on finite samples. -/
theorem diagonal {Q : Finset ℕ → Prop}
    (stable : ∀ n s, Presents s (layer n) → ∀ᶠ t in atTop, Q (sample s t)) :
    ∃ s : ℕ → ℕ, Presents s Set.univ ∧ ∀ᶠ t in atTop, Q (sample s t) := by
  classical
  choose F hF hlock using fun n ↦ lock
    (squares_infinite.nonempty.mono (Set.subset_union_left (t := (Finset.range n : Set ℕ)))) (stable n)
  let preload (n : ℕ) := ((F (n+1)).erase n).toList
  have hp {n x} (hx : x ∈ preload n) : x ∈ layer n := by
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp (Finset.mem_toList.mp hx)
    exact layer_previous (hF _ hm) hne
  let H : ℕ → List ℕ := Nat.rec (F 0).toList (fun n xs ↦ (xs ++ preload n) ++ [n])
  have grows n : H n <+: H (n+1) := (List.prefix_append _ _).trans (List.prefix_append _ [n])
  have length n : n ≤ (H n).length := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      change n+1 ≤ ((H n ++ preload n) ++ [n]).length
      simp only [List.length_append,List.length_singleton]
      omega
  let chain : Support.HistoryChain ℕ := ⟨⟨H,grows⟩,length⟩
  have lock_mem n : F n ⊆ (H n).toFinset := by
    intro x hx
    cases n with
    | zero => simpa [H] using hx
    | succ n =>
      change x ∈ ((H n ++ preload n) ++ [n]).toFinset
      by_cases he : x = n
      · simp [he]
      · have hm : x ∈ preload n := Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨he,hx⟩)
        simp [hm]
  have inside (n : ℕ) : Angluin.ListWithin (H n) (layer n) := by
    induction n with
    | zero => exact fun x hx ↦ hF 0 (Finset.mem_toList.mp hx)
    | succ n ih =>
      apply Angluin.listWithin_append (Angluin.listWithin_append
        (fun x hx ↦ layer_mono n (ih x hx)) (fun _ hx ↦ layer_mono n (hp hx)))
      exact Angluin.singletonWithin (Or.inr (Finset.mem_range.mpr (Nat.lt_succ_self n)))
  refine ⟨chain.stream,Set.eq_univ_iff_forall.mpr (fun n ↦ ?_),eventually_atTop.mpr ⟨(H 0).length,fun t ht ↦ ?_⟩⟩
  · apply chain.history_toFinset_subset_stream_range (n+1)
    change n ∈ ((H n ++ preload n) ++ [n]).toFinset
    simp
  · have ex : ∃ j, t < (H j).length := ⟨t+1,by have := length (t+1); omega⟩
    let j := Nat.find ex
    have hj : t < (H j).length := Nat.find_spec ex
    have hj0 : j ≠ 0 := fun he ↦ (Nat.not_lt_of_ge ht) (he ▸ hj)
    obtain ⟨n,he⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have prev : (H n).length ≤ t := Nat.le_of_not_gt (Nat.find_min ex (by change n < j; omega))
    have upper : t ≤ (H n ++ preload n).length := by
      rw [he] at hj
      change t < ((H n ++ preload n) ++ [n]).length at hj
      simp only [List.length_append,List.length_singleton] at hj ⊢
      omega
    have start : sample chain.stream (H n).length = (H n).toFinset := by
      rw [← textPrefix_toFinset,chain.textPrefix_stream n]
    have pre : (H n ++ preload n) <+: chain.history (n+1) := List.prefix_append _ [n]
    have stop : sample chain.stream (H n ++ preload n).length = (H n ++ preload n).toFinset := by
      rw [← textPrefix_toFinset,chain.textPrefix_stream_of_prefix pre]
    apply hlock n _ ((lock_mem n).trans (start ▸ sample_mono (stream := chain.stream) prev))
    intro x hx
    have hm := sample_mono upper hx
    rw [stop] at hm
    exact (List.mem_append.mp (List.mem_toFinset.mp hm)).elim (inside n x) hp

end GenLimit.KleinbergWei.DensityMeasures.SetDriven
