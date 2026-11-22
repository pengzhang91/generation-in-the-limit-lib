import GenLimit.Paper05_HallucinationsBreadthAndStability.StableApproximate
import GenLimit.Support.PredicateLock
import GenLimit.Support.HistoryChainText

/-! # One enumeration with distinct sublanguage witnesses (Corollary 6.1) -/

namespace GenLimit.BreadthCharacterizations

private structure WitnessExtension (F : Generic.LanguageFamily α) (G : SupportAlgorithm α)
    (z : ℕ) (xs ys : List α) (j : ℕ) (w : α) : Prop where
  extendsHistory : xs <+: ys
  withinWitness : Angluin.ListWithin ys (F j)
  proper : F j ⊂ F z
  valid : G ys ⊆ F j
  finiteOmissions : (F j \ G ys).Finite
  markerInTarget : w ∈ F z
  markerOutsideWitness : w ∉ F j

/-- Extend any target history until the generator works for a proper
sublanguage containing the entire extension. Keep one omitted target word
to distinguish this language from every witness chosen at a later stage. -/
private theorem extend_for_approximate [Countable α] {F : Generic.LanguageFamily α}
    (hi : ∀ i, (F i).Infinite) {G : SupportAlgorithm α} (hg : IsApproximateBreadthGenerator G F)
    {z : ℕ} (hz : ¬ ∃ T, Angluin.IsTellTale F z T)
    (xs : List α) (hx : Angluin.ListWithin xs (F z)) :
    ∃ (ys : List α) (j : ℕ) (w : α), WitnessExtension F G z xs ys j w := by
  classical
  have hsub : (xs.toFinset : Set α) ⊆ F z := fun _ h ↦ hx _ (List.mem_toFinset.mp h)
  have bad : ¬ ∀ j, (xs.toFinset : Set α) ⊆ F j → F j ⊆ F z → F z ⊆ F j :=
    fun h ↦ hz ⟨_, hsub, h⟩
  push_neg at bad
  obtain ⟨j,hxj,hj,hproper⟩ := bad
  obtain ⟨w,hw,hn⟩ := Set.not_subset.mp hproper
  have start : Angluin.ListWithin xs (F j) := fun x h ↦ hxj (List.mem_toFinset.mpr h)
  let base := Support.exactPresentation (F j) (hi j).nonempty
  have hb : Generic.Presents base (F j) := Support.exactPresentation_presents _ _
  obtain ⟨T,hT⟩ := hg j _ (Angluin.prependStream_presents start hb)
  have good := hT (xs.length + T) (Nat.le_add_left ..)
  simp only [ApproximateBreadthCorrectAt, supportAt, Angluin.streamPrefix_prependStream] at good
  refine ⟨_,j,w,⟨List.prefix_append ..,Angluin.listWithin_append start
    (Angluin.streamPrefix_listWithin (Generic.streamIn_of_presents hb) T),
    ?_,good.1,good.2,hw,hn⟩⟩
  exact Set.ssubset_iff_subset_ne.mpr ⟨hj,fun e ↦ hn (e ▸ hw)⟩

/-- Corollary 6.1. One exact presentation of one target witnesses
approximate correctness for infinitely many distinct proper sublanguages
at strictly increasing times. The witnesses are pairwise distinct as sets of words. -/
theorem corollary_6_1 [Countable α] {F : Generic.LanguageFamily α}
    (hi : ∀ i, (F i).Infinite) (hnot : ¬ Angluin.SemanticallyInferrable F)
    {G : SupportAlgorithm α} (hg : IsApproximateBreadthGenerator G F) :
    ∃ (z : ℕ) (s : ℕ → α) (j t : ℕ → ℕ), Generic.Presents s (F z) ∧ Function.Injective (fun n : ℕ ↦ F (j n)) ∧
      StrictMono t ∧ ∀ n, F (j n) ⊂ F z ∧ ApproximateBreadthCorrectAt G (F (j n)) s (t n) := by
  classical
  have hbad : ¬ Angluin.ConditionTwo F := fun h ↦ hnot (Angluin.semanticallyInferrable_of_conditionTwo F h)
  unfold Angluin.ConditionTwo at hbad
  obtain ⟨z,hz⟩ := Classical.not_forall.mp hbad
  let base := Support.exactPresentation (F z) (hi z).nonempty
  have hp : Generic.Presents base (F z) := Support.exactPresentation_presents _ _
  let H := {xs : List α // Angluin.ListWithin xs (F z)}
  choose ys j w spec using fun xs : H ↦ extend_for_approximate hi hg hz xs.val xs.property
  have next (n : ℕ) (xs : H) : Angluin.ListWithin (ys xs ++ [w xs,base n]) (F z) := by
    apply Angluin.listWithin_append
    · exact fun x hx ↦ (spec xs).proper.subset ((spec xs).withinWitness x hx)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (spec xs).markerInTarget
      · exact hp ▸ Set.mem_range_self n
  let a : ℕ → H := Nat.rec ⟨[], by simp [Angluin.ListWithin]⟩
    (fun n xs ↦ ⟨_,next n xs⟩)
  have step (n : ℕ) : (a (n+1)).val = ys (a n) ++ [w (a n),base n] := rfl
  have pre (n : ℕ) : ys (a n) <+: (a (n+1)).val := step n ▸ List.prefix_append ..
  have growth (n : ℕ) : (a n).val.length < (a (n+1)).val.length := by
    rw [step]; simp only [List.length_append,List.length_cons,List.length_nil]
    have := (spec (a n)).extendsHistory.length_le
    omega
  let chain : Support.HistoryChain α :=
    ⟨⟨fun n ↦ (a n).val,fun n ↦ (spec (a n)).extendsHistory.trans (pre n)⟩,
      fun n ↦ (strictMono_nat_of_lt_succ growth).id_le n⟩
  have occurs (n : ℕ) (x : α) (hx : x ∈ (a n).val) : x ∈ Set.range chain.stream :=
    chain.history_toFinset_subset_stream_range n (List.mem_toFinset.mpr hx)
  have presents : Generic.Presents chain.stream (F z) := by
    apply Set.Subset.antisymm
    · rintro x ⟨n,rfl⟩
      exact (a (n+1)).property _ (List.get_mem ..)
    · intro x hx
      obtain ⟨n,rfl⟩ := (show x ∈ Set.range base from hp.symm ▸ hx)
      exact occurs (n+1) _ (by rw [step]; simp)
  have diff {m n : ℕ} (hmn : m < n) : F (j (a m)) ≠ F (j (a n)) := by
    have member : w (a m) ∈ (a (m+1)).val := by rw [step]; simp
    have incl : (a (m+1)).val <+: (a n).val := chain.toPrefixChain.prefix_of_le hmn
    have later := (spec (a n)).withinWitness _ ((spec (a n)).extendsHistory.subset (incl.subset member))
    exact fun e ↦ (spec (a m)).markerOutsideWitness (e.symm ▸ later)
  refine ⟨z, chain.stream, fun n ↦ j (a n), fun n ↦ (ys (a n)).length, presents,
    fun {m n} he ↦ le_antisymm (le_of_not_gt (fun h ↦ diff h he.symm)) (le_of_not_gt (fun h ↦ diff h he)),
    strictMono_nat_of_lt_succ (fun n ↦ ?_), fun n ↦ ⟨(spec (a n)).proper, ?_⟩⟩
  · have h := (spec (a (n+1))).extendsHistory.length_le
    rw [step] at h
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  · simp only [ApproximateBreadthCorrectAt, supportAt, chain.textPrefix_stream_of_prefix (n := n+1) (pre n)]
    exact ⟨(spec (a n)).valid,(spec (a n)).finiteOmissions⟩

end GenLimit.BreadthCharacterizations
