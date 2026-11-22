import GenLimit.Support.Locking

/-! # Locking an eventual property of finite histories -/

namespace GenLimit.Support

/-- If every presentation of a target eventually satisfies a prefix property,
one finite positive history forces it on every continuation in the target. -/
theorem exists_locking_prefix {α : Type*} {K : Set α} {base : ℕ → α}
    (hbase : Generic.Presents base K) (P : List α → Prop)
    (hP : ∀ s, Generic.Presents s K → ∃ T, ∀ t ≥ T, P (textPrefix s t)) :
    ∃ xs, Angluin.ListWithin xs K ∧ ∀ tail, Angluin.ListWithin tail K → P (xs ++ tail) := by
  obtain ⟨xs, j, hx, hlock⟩ := Angluin.exists_lockingSequence_of_converges_with_base
    (M := P) hbase (fun s hs => by
      obtain ⟨T, hT⟩ := hP s hs
      exact ⟨True, T, fun t ht => propext (iff_true_intro (hT t ht))⟩)
  obtain ⟨T, hT⟩ := hP _ (Angluin.prependStream_presents hx hbase)
  have hg := hT (xs.length + T) (Nat.le_add_left ..)
  rw [Angluin.streamPrefix_prependStream] at hg
  have ht := hlock (textPrefix base T)
    (Angluin.streamPrefix_listWithin (Generic.streamIn_of_presents hbase) T)
  exact ⟨xs, hx, fun tail htail => (hlock tail htail).symm ▸ (ht ▸ hg : j)⟩

/-- A lock on the larger target can be followed by any enumeration of a
smaller one containing its content. Both target properties then hold at a
single common history. -/
theorem finite_witness_compatible [Countable α] (C : Set (Set α))
    (hne : ∀ K ∈ C, K.Nonempty) (P : List α → Set α → Prop)
    (learns : ∀ K ∈ C, ∀ s, Generic.Presents s K → ∃ T, ∀ t ≥ T, P (textPrefix s t) K)
    {K : Set α} (hK : K ∈ C) :
    ∃ T : Finset α, (T : Set α) ⊆ K ∧ ∀ L ∈ C, (T : Set α) ⊆ L → L ⊆ K →
      ∃ xs, Angluin.ListWithin xs L ∧ P xs K ∧ P xs L := by
  classical
  obtain ⟨xs, hxs, hlock⟩ := exists_locking_prefix
    (exactPresentation_presents K (hne K hK)) (P · K) (learns K hK)
  refine ⟨xs.toFinset, fun x hx => hxs _ (List.mem_toFinset.mp hx), ?_⟩
  intro L hL hcontain hsub
  have hxsL : Angluin.ListWithin xs L := fun x hx => hcontain (List.mem_toFinset.mpr hx)
  let s := exactPresentation L (hne L hL)
  have hp : Generic.Presents s L := exactPresentation_presents _ _
  obtain ⟨t, ht⟩ := learns L hL _ (Angluin.prependStream_presents hxsL hp)
  have hgood := ht (xs.length+t) (Nat.le_add_left ..)
  rw [Angluin.streamPrefix_prependStream] at hgood
  have htail := Angluin.streamPrefix_listWithin (Generic.streamIn_of_presents hp) t
  exact ⟨_, Angluin.listWithin_append hxsL htail, hlock _ (fun x hx => hsub (htail x hx)), hgood⟩

end GenLimit.Support
