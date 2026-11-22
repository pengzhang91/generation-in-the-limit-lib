import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.TruthIndex
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Accurate
import GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse
import GenLimit.Support.Locking
import GenLimit.Core.Text
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The optimal index breadth on a fixed ordered target -/
namespace GenLimit.KleinbergWei.DensityMeasures

open TowerTopology Filter
open scoped Topology

/-- A bound is realized by a tower exactly when every finite sample fits a
proper sublanguage of that density. The converse constructs a perfect tower
inside the subspace of thin approximants and the terminal point. -/
theorem towerBound_iff_finite_extensions {X : Set Language} {K : Point X}
    (O : OrderedLanguage) (hc : O.carrier = K.val)
    {s : ℕ → ℕ} (hs : Presents s K.val) (b : ℝ) :
    HasPerfectTowerBound X K O b ↔
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ K.val →
      ∃ L ∈ X, L ⊂ K.val ∧ (F : Set ℕ) ⊆ L ∧ O.upperDensity L ≤ b := by
  constructor
  · rintro ⟨_,tower,ht,hd⟩ F hF
    obtain ⟨n,hn⟩ := finite_eventually_contained ht.toConvergentProperTower F hF
    exact ⟨_, (tower n).property, ht.proper n, hn n le_rfl, hd n⟩
  · intro h
    let Y : Set Language := {L | L = K.val ∨ L ∈ X ∧ O.upperDensity L ≤ b}
    let k : Point Y := ⟨K.val, Or.inl rfl⟩
    have hy : BasisLimitPoint k := by
      intro F hF
      obtain ⟨L,hL,hproper,hcontains,hd⟩ := h F hF
      exact ⟨⟨L, Or.inr ⟨hL,hd⟩⟩, fun he ↦ hproper.ne (congrArg Subtype.val he),
        hcontains, hproper.le⟩
    let t := adaptiveTower k hy s hs
    have ht : PerfectTower Y t k := perfectTower_of_basisLimitPoint hy s hs
    have good (n : ℕ) : (t n).val ∈ X ∧ O.upperDensity (t n).val ≤ b :=
      (show (t n).val = K.val ∨ _ from (t n).property).resolve_left (ht.proper n).ne
    refine ⟨hc, fun n ↦ ⟨(t n).val, (good n).1⟩,
      ⟨ht.proper, ht.stage_fixes, ht.complete⟩, fun n ↦ (good n).2⟩

/-- All index rules receive a finite ordered history. Validity is required
on all targets, including every proper sublanguage used by an adversary. -/
def ValidIndexRule (C : LanguageFamily) (A : List ℕ → ℕ) : Prop :=
  ∀ z s, Presents s (C z) → ∀ᶠ t in atTop, C (A (textPrefix s t)) ⊆ C z

noncomputable def indexBreadth (C : LanguageFamily) (O : OrderedLanguage)
    (A : List ℕ → ℕ) (s : ℕ → ℕ) : ℝ :=
  liminf (fun t ↦ O.upperDensity (C (A (textPrefix s t)))) atTop

/-- The last scoped strictly critical language, computed from the prefix. -/
noncomputable def breadthSelector (C : LanguageFamily) (xs : List ℕ) : ℕ :=
  scopedFocus C (Generic.historyThenFallback xs 0) xs.length

private theorem breadthSelector_prefix (C : LanguageFamily) (s : ℕ → ℕ) (t : ℕ) :
    breadthSelector C (textPrefix s t) = scopedFocus C s t := by
  have he : sample (Generic.historyThenFallback (textPrefix s t) 0) t = sample s t := by
    apply sample_eq_of_eq_on_prefix
    intro k hk
    simp [Generic.historyThenFallback, hk, textPrefix_eq_ofFn]
  rw [breadthSelector, textPrefix_length]
  have hcrit : StrictCritical C (Generic.historyThenFallback (textPrefix s t) 0) t =
      StrictCritical C s t := by
    funext i
    simp [StrictCritical, Consistent, he]
  unfold scopedFocus scopedStrictCriticalIndices
  rw [hcrit]

private theorem selector_eventual (C : LanguageFamily) (z : ℕ) (s : ℕ → ℕ)
    (hs : Presents s (C z)) : ∀ᶠ t in atTop,
    (↑(sample s t) : Set ℕ) ⊆ C (breadthSelector C (textPrefix s t)) ∧
      C (breadthSelector C (textPrefix s t)) ⊆ C z := by
  classical
  obtain ⟨j,hf,hj⟩ := exists_first_occurrence C z
  have hp : Presents s (C j) := hj.symm ▸ hs
  obtain ⟨T,hT⟩ := lemma_3_3 hp hf
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop j] with t ht hjt
  rw [breadthSelector_prefix]
  obtain ⟨_,hcrit,hle⟩ := scopedFocus_spec hjt (hT t ht)
  refine ⟨hcrit.1, ?_⟩
  rw [← hj]
  rcases hle.eq_or_lt with he | hlt
  · rw [he]
  · exact (strictCritical_ssubset_of_lt hlt (hT t ht) hcrit).le

theorem breadthSelector_valid (C : LanguageFamily) : ValidIndexRule C (breadthSelector C) :=
  fun z s hs ↦ (selector_eventual C z s hs).mono fun _ h ↦ h.2

private theorem truthIndex_le_bound {X : Set Language} {K : Point X} {O : OrderedLanguage}
    {τ b : ℝ} (hτ : IsTruthIndex X K O τ) (hb : HasPerfectTowerBound X K O b) : τ ≤ b := by
  obtain ⟨hc,t,ht,hd⟩ := hb
  exact (hτ.2.2.1 ⟨t,ht⟩).2 b (fun ε hε ↦ ⟨hc,t,ht,fun n ↦ (hd n).trans (by linarith)⟩)

/-- A consistent guess eventually contained in the target attains the
truth-index lower bound. This applies to both ways of encoding a sample. -/
theorem index_breadth_lower_of_eventual (C : LanguageFamily) (z : ℕ) (O : OrderedLanguage)
    (hc : O.carrier = C z) {τ : ℝ} (hτ : IsTruthIndex (Set.range C) ⟨C z,z,rfl⟩ O τ)
    {s : ℕ → ℕ} (hs : Presents s (C z)) (A : List ℕ → ℕ)
    (eventual : ∀ᶠ t in atTop, (sample s t : Set ℕ) ⊆ C (A (textPrefix s t)) ∧
      C (A (textPrefix s t)) ⊆ C z) :
    τ ≤ indexBreadth C O A s := by
  apply le_of_forall_lt_imp_le_of_dense
  intro b hb
  have hnot : ¬ HasPerfectTowerBound (Set.range C) ⟨C z, z, rfl⟩ O b :=
    fun h ↦ hb.not_ge (truthIndex_le_bound hτ h)
  rw [towerBound_iff_finite_extensions O hc hs] at hnot
  push_neg at hnot
  obtain ⟨F,hF,hthin⟩ := hnot
  have hobs : ∀ᶠ t in atTop, (F : Set ℕ) ⊆ (sample s t : Set ℕ) := by
    have hpoint (x : ℕ) (hx : x ∈ F) : ∀ᶠ t : ℕ in atTop, x ∈ sample s t := by
      obtain ⟨n,hn⟩ := (show x ∈ Set.range s from hs.symm ▸ hF hx)
      filter_upwards [eventually_gt_atTop n] with t ht
      exact mem_sample_iff.mpr ⟨n,ht,hn⟩
    exact (Filter.eventually_all_finset F).mpr hpoint
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun _ ↦ O.upperDensity_le_one _))
  filter_upwards [hobs, eventual] with t ht hsel
  let L := C (A (textPrefix s t))
  change b ≤ O.upperDensity L
  by_cases he : L = C z
  · rw [he, ← hc, O.upperDensity_carrier]
    exact hb.le.trans hτ.2.1
  · exact (hthin L ⟨_,rfl⟩ (Set.ssubset_iff_subset_ne.mpr ⟨hsel.2,he⟩)
      (ht.trans hsel.1)).le

/-- The lower half of Theorem 4.9. The same rule works simultaneously for
every target and every ordering of the target. -/
theorem theorem_4_9_achievability (C : LanguageFamily) (z : ℕ) (O : OrderedLanguage)
    (hc : O.carrier = C z) {τ : ℝ}
    (hτ : IsTruthIndex (Set.range C) ⟨C z, z, rfl⟩ O τ)
    {s : ℕ → ℕ} (hs : Presents s (C z)) :
    τ ≤ indexBreadth C O (breadthSelector C) s := by
  exact index_breadth_lower_of_eventual C z O hc hτ hs _ (selector_eventual C z s hs)

/-- A single presentation can meet a different dense prefix requirement at
each successive stage, while enumerating every element of the target. -/
theorem diagonal_presentation {K : Language} {s₀ : ℕ → ℕ}
    (hs₀ : Presents s₀ K) (Q : ℕ → List ℕ → Prop)
    (extend : ∀ n xs, Angluin.ListWithin xs K →
      ∃ ys, xs <+: ys ∧ Angluin.ListWithin ys K ∧ Q n ys) :
    ∃ s, Presents s K ∧ ∀ n, ∃ t ≥ n, Q n (textPrefix s t) := by
  classical
  let H := {xs : List ℕ // Angluin.ListWithin xs K}
  have step (n : ℕ) (xs : H) := extend n (xs.val ++ [s₀ n])
    (Angluin.listWithin_append xs.property
      (Angluin.singletonWithin (show s₀ n ∈ K from hs₀ ▸ Set.mem_range_self n)))
  let a : ℕ → H := Nat.rec ⟨[], by simp [Angluin.ListWithin]⟩
    (fun n xs ↦ ⟨(step n xs).choose, (step n xs).choose_spec.2.1⟩)
  have hstep (n : ℕ) : (a n).val ++ [s₀ n] <+: (a (n+1)).val ∧ Q n (a (n+1)).val :=
    ⟨(step n (a n)).choose_spec.1,(step n (a n)).choose_spec.2.2⟩
  have hlen (n : ℕ) : n ≤ (a n).val.length := by
    induction n with
    | zero => omega
    | succ n ih =>
      have h := (hstep n).1.length_le
      simp only [List.length_append, List.length_singleton] at h
      omega
  let chain : Support.HistoryChain ℕ :=
    ⟨⟨fun n ↦ (a n).val, fun n ↦ (List.prefix_append ..).trans (hstep n).1⟩, hlen⟩
  refine ⟨chain.stream, Set.Subset.antisymm ?_ ?_, ?_⟩
  · rintro x ⟨k,rfl⟩
    exact (a (k+1)).property _ (List.get_mem _ _)
  · intro x hx
    obtain ⟨n,rfl⟩ := (show x ∈ Set.range s₀ from hs₀.symm ▸ hx)
    apply chain.history_toFinset_subset_stream_range (n+1)
    exact List.mem_toFinset.mpr ((hstep n).1.subset (by simp))
  · intro n
    refine ⟨_, (Nat.le_succ n).trans (hlen _), ?_⟩
    rw [chain.textPrefix_stream (n+1)]
    exact (hstep n).2

/-- The adversarial half of Theorem 4.9. At stage n the adversary presents
a thin proper sublanguage until validity forces a low-density guess, then
retains the entire prefix and incorporates another element of the target. -/
theorem theorem_4_9_adversary (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (z : ℕ) (O : OrderedLanguage) (hc : O.carrier = C z) {τ : ℝ}
    (hτ : IsTruthIndex (Set.range C) ⟨C z, z, rfl⟩ O τ)
    (A : List ℕ → ℕ) (hA : ValidIndexRule C A) :
    ∃ s, Presents s (C z) ∧ indexBreadth C O A s ≤ τ := by
  classical
  let K : Point (Set.range C) := ⟨C z, z, rfl⟩
  let s₀ := Support.exactPresentation (C z) (hi z).nonempty
  have hs₀ : Presents s₀ (C z) := Support.exactPresentation_presents _ _
  by_cases ht : HasAnyPerfectTower (Set.range C) K
  · let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have extn (n : ℕ) (xs : List ℕ) (hx : Angluin.ListWithin xs (C z)) :
        ∃ ys, xs <+: ys ∧ Angluin.ListWithin ys (C z) ∧ O.upperDensity (C (A ys)) ≤ τ + δ n := by
      have hb := (hτ.2.2.1 ht).1 (δ n) (by dsimp [δ]; positivity)
      obtain ⟨L,⟨j,rfl⟩,hj,hcontain,hd⟩ :=
        (towerBound_iff_finite_extensions O hc hs₀ _).1 hb xs.toFinset
          (fun x hx' ↦ hx x (List.mem_toFinset.mp hx'))
      let base := Support.exactPresentation (C j) (hi j).nonempty
      have hp : Generic.Presents base (C j) := Support.exactPresentation_presents _ _
      have hxs : Angluin.ListWithin xs (C j) := fun x h ↦ hcontain (List.mem_toFinset.mpr h)
      obtain ⟨T,hT⟩ := eventually_atTop.1 (hA j _ (Angluin.prependStream_presents hxs hp))
      have hv := hT (xs.length + T) (Nat.le_add_left ..)
      rw [Angluin.streamPrefix_prependStream] at hv
      refine ⟨_,List.prefix_append .., Angluin.listWithin_append hx ?_,
        (O.upperDensity_mono hv).trans hd⟩
      exact fun x h ↦ hj.le (Angluin.streamPrefix_listWithin (Generic.streamIn_of_presents hp) T x h)
    obtain ⟨s,hs,hbad⟩ := diagonal_presentation hs₀ _ extn
    refine ⟨s,hs,le_of_forall_gt_imp_ge_of_dense ?_⟩
    intro b hb
    have he : ∀ᶠ n in atTop, δ n < b - τ :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const (sub_pos.mpr hb)
    apply liminf_le_of_frequently_le
    · apply frequently_atTop.2
      intro N
      obtain ⟨n,hn,hδ⟩ := (he.and (eventually_ge_atTop N)).exists
      obtain ⟨t,ht,hq⟩ := hbad n
      exact ⟨t,hδ.trans ht,hq.trans (by linarith)⟩
    · exact isBoundedUnder_of ⟨0,fun _ ↦ O.upperDensity_nonneg _⟩
  · rw [hτ.2.2.2 ht]
    refine ⟨s₀,hs₀,liminf_le_of_frequently_le ?_ ?_⟩
    · exact (Eventually.of_forall (fun _ ↦ O.upperDensity_le_one _)).frequently
    · exact isBoundedUnder_of ⟨0,fun _ ↦ O.upperDensity_nonneg _⟩

end GenLimit.KleinbergWei.DensityMeasures
