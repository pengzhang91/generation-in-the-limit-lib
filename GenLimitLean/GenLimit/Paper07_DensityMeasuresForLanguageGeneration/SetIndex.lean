import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.VanishingBreadth

/-! # The truth-index characterization for functions of the unordered sample

Use the number of *distinct* observations as the search scope. The optimal
index rule therefore depends only on the finite set supplied in Section 2.1.
-/
namespace GenLimit.KleinbergWei.DensityMeasures.SetDriven
open Filter

def ValidIndex (C : LanguageFamily) (A : Finset ℕ → ℕ) : Prop :=
  ∀ z s, Presents s (C z) → ∀ᶠ t in atTop, C (A (sample s t)) ⊆ C z

def asHistory (A : Finset ℕ → ℕ) (xs : List ℕ) := A xs.toFinset

private theorem valid_iff (C : LanguageFamily) (A : Finset ℕ → ℕ) :
    ValidIndexRule C (asHistory A) ↔ ValidIndex C A := by
  simp only [ValidIndexRule,ValidIndex,asHistory,textPrefix_toFinset]

noncomputable def selector (C : LanguageFamily) (S : Finset ℕ) : ℕ :=
  breadthSelector C S.toList

private theorem selector_eventual (C : LanguageFamily) (z : ℕ) (hi : (C z).Infinite)
    {s : ℕ → ℕ} (hs : Presents s (C z)) : ∀ᶠ t in atTop,
      (sample s t : Set ℕ) ⊆ C (selector C (sample s t)) ∧
        C (selector C (sample s t)) ⊆ C z := by
  classical
  obtain ⟨j,hfirst,hj⟩ := exists_first_occurrence C z
  obtain ⟨T,hT⟩ := lemma_3_3 (hj.symm ▸ hs) hfirst
  obtain ⟨F,hF,hcard⟩ := hi.exists_subset_card_eq j
  have seen : ∀ᶠ t in atTop, F ⊆ sample s t :=
    eventually_atTop.mpr (TowerTopology.finite_eventually_subset_sample hs F hF)
  filter_upwards [eventually_ge_atTop T,seen] with t ht hseen
  let S := sample s t
  let d := Generic.historyThenFallback S.toList 0
  have obs : sample d S.toList.length = S := by
    ext x
    have h := Generic.sample_historyThenFallback_length S.toList 0
    have eq : x ∈ Generic.sample d S.toList.length ↔ x ∈ S := by rw [h]; simp
    simpa only [GenLimit.mem_sample_iff,Generic.mem_sample_iff] using eq
  have visible : j ≤ S.toList.length := by simpa [hcard,S] using Finset.card_le_card hseen
  have hcrit : StrictCritical C d S.toList.length j := by
    simpa only [StrictCritical,Consistent,obs,S] using hT t ht
  obtain ⟨_,hguess,hle⟩ := scopedFocus_spec visible hcrit
  change (S : Set ℕ) ⊆ C (scopedFocus C d S.toList.length) ∧ _
  have consistent := hguess.1
  unfold Consistent at consistent
  rw [obs] at consistent
  refine ⟨consistent,?_⟩
  change C (scopedFocus C d S.toList.length) ⊆ C z
  rw [← hj]
  rcases hle.eq_or_lt with he | hl
  · rw [← he]
  · exact (strictCritical_ssubset_of_lt hl hcrit hguess).le

def Vanishing (C : LanguageFamily) (z : ℕ) (O : OrderedLanguage) : Prop :=
  ∀ A, ValidIndex C A → ∃ s, Presents s (C z) ∧ indexBreadth C O (asHistory A) s = 0

/-- Both minimax inequalities hold in the smaller class of set-driven rules. -/
theorem minimax (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (z : ℕ) (O : OrderedLanguage) (hc : O.carrier = C z) :
    ∃ τ, IsTruthIndex (Set.range C) ⟨C z,z,rfl⟩ O τ ∧
      (∀ A, ValidIndex C A → ∃ s, Presents s (C z) ∧ indexBreadth C O (asHistory A) s ≤ τ) ∧
      ValidIndex C (selector C) ∧
      ∀ s, Presents s (C z) → τ ≤ indexBreadth C O (asHistory (selector C)) s := by
  obtain ⟨τ,hτ⟩ := exists_truthIndex (X := Set.range C) ⟨C z,z,rfl⟩ O hc
  refine ⟨τ,hτ,fun A hv ↦ theorem_4_9_adversary C hi z O hc hτ _ ((valid_iff C A).mpr hv),
    fun j s hs ↦ (selector_eventual C j (hi j) hs).mono (fun _ h ↦ h.2),fun s hs ↦ ?_⟩
  apply index_breadth_lower_of_eventual C z O hc hτ hs
  simpa only [asHistory,textPrefix_toFinset] using selector_eventual C z (hi z) hs

theorem vanishing_iff (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (z : ℕ) (O : OrderedLanguage) (hc : O.carrier = C z) :
    Vanishing C z O ↔ ∀ ε : ℝ, 0 < ε →
      HasPerfectTowerBound (Set.range C) ⟨C z,z,rfl⟩ O ε := by
  constructor
  · intro h
    obtain ⟨τ,hτ,_,hv,hl⟩ := minimax C hi z O hc
    obtain ⟨s,hs,he⟩ := h _ hv
    have hz : τ = 0 := le_antisymm ((hl _ hs).trans he.le) hτ.1
    have ht : HasAnyPerfectTower (Set.range C) ⟨C z,z,rfl⟩ := by
      by_contra hn
      linarith [hτ.2.2.2 hn]
    simpa [hz] using (hτ.2.2.1 ht).1
  · intro ht A hv
    exact (theorem_4_1 C hi z O hc).mpr ht _ ((valid_iff C A).mpr hv)

theorem exists_vanishing :
    ∃ (C : LanguageFamily) (z : ℕ) (O : OrderedLanguage), (∀ i, (C i).Infinite) ∧
      O.carrier = C z ∧ Vanishing C z O := by
  obtain ⟨C,z,O,hi,hc,h⟩ := theorem_2_3
  exact ⟨C,z,O,hi,hc,fun A hv ↦ h _ ((valid_iff C A).mpr hv)⟩

end GenLimit.KleinbergWei.DensityMeasures.SetDriven
