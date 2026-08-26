import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.StrictCritical
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

/-!
# #07 Density Measures: the accurate selector

The semantic, noncomputable Section 3 construction. Paper round t+1 uses
strict criticality at stage t and the newly revealed value at position t.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- Strictly critical indices in the visible scope n ≤ t. -/
noncomputable def scopedStrictCriticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t + 1)).filter (StrictCritical C stream t)

@[simp] theorem mem_scopedStrictCriticalIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ} :
    n ∈ scopedStrictCriticalIndices C stream t ↔
      n ≤ t ∧ StrictCritical C stream t n := by
  classical
  simp [scopedStrictCriticalIndices, Nat.lt_succ_iff]

/-- The last visible strictly critical index, with default zero. -/
noncomputable def scopedFocus
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ := by
  classical
  let S := scopedStrictCriticalIndices C stream t
  exact if h : S.Nonempty then S.max' h else 0

theorem scopedFocus_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z : ℕ}
    (hzt : z ≤ t)
    (hz : StrictCritical C stream t z) :
    scopedFocus C stream t ≤ t ∧
      StrictCritical C stream t (scopedFocus C stream t) ∧
      z ≤ scopedFocus C stream t := by
  classical
  let S := scopedStrictCriticalIndices C stream t
  have hzS : z ∈ S := by
    simpa [S] using mem_scopedStrictCriticalIndices.mpr ⟨hzt, hz⟩
  have hne : S.Nonempty := ⟨z, hzS⟩
  have hmaxS : S.max' hne ∈ S := Finset.max'_mem S hne
  have hfocus : scopedFocus C stream t = S.max' hne := by
    simp [scopedFocus, S, hne]
  rw [hfocus]
  have hparts :
      S.max' hne ≤ t ∧ StrictCritical C stream t (S.max' hne) := by
    simpa [S] using mem_scopedStrictCriticalIndices.mp hmaxS
  exact ⟨hparts.1, hparts.2, Finset.le_max' S z hzS⟩

/-- A strict-critical language falsified by the new observation. -/
def BadStrictCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t w n : ℕ) : Prop :=
  StrictCritical C stream t n ∧ w ∉ C n

/-- The first falsified strict-critical index, with an irrelevant default. -/
noncomputable def firstBadStrictCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t w : ℕ) : ℕ := by
  classical
  exact if hbad : ∃ n, BadStrictCritical C stream t w n then
    Nat.find hbad
  else 0

theorem firstBadStrictCritical_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w : ℕ}
    (hbad : ∃ n, BadStrictCritical C stream t w n) :
    BadStrictCritical C stream t w (firstBadStrictCritical C stream t w) := by
  classical
  simp only [firstBadStrictCritical, dif_pos hbad]
  exact Nat.find_spec hbad

theorem firstBadStrictCritical_min
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w n : ℕ}
    (hbad : ∃ n, BadStrictCritical C stream t w n)
    (hn : BadStrictCritical C stream t w n) :
    firstBadStrictCritical C stream t w ≤ n := by
  classical
  simp only [firstBadStrictCritical, dif_pos hbad]
  exact Nat.find_min' hbad hn

/-- Strict-critical indices before the first falsified one that contain the
new observation. -/
noncomputable def boundaryCandidates
    (C : LanguageFamily) (stream : ℕ → ℕ) (t w : ℕ) : Finset ℕ := by
  classical
  let b := firstBadStrictCritical C stream t w
  exact (Finset.range b).filter fun n =>
    StrictCritical C stream t n ∧ w ∈ C n

@[simp] theorem mem_boundaryCandidates
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w n : ℕ} :
    n ∈ boundaryCandidates C stream t w ↔
      n < firstBadStrictCritical C stream t w ∧
        StrictCritical C stream t n ∧ w ∈ C n := by
  classical
  simp [boundaryCandidates]

/-- The two cases of the paper's selector at previous stage t. -/
noncomputable def selectIndex
    (C : LanguageFamily) (stream : ℕ → ℕ) (t w : ℕ) : ℕ := by
  classical
  if hall : ∀ n, StrictCritical C stream t n → w ∈ C n then
    exact scopedFocus C stream t
  else
    have hbad : ∃ n, BadStrictCritical C stream t w n := by
      simpa [BadStrictCritical] using hall
    let S := boundaryCandidates C stream t w
    exact if hS : S.Nonempty then S.max' hS
      else scopedFocus C stream t

/-- In the stable-target regime, the selected language is strictly critical,
no earlier than the target, and contained in the target. -/
theorem selectIndex_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w z : ℕ}
    (hzt : z ≤ t)
    (hz : StrictCritical C stream t z)
    (hw : w ∈ C z) :
    StrictCritical C stream t (selectIndex C stream t w) ∧
      z ≤ selectIndex C stream t w ∧
      C (selectIndex C stream t w) ⊆ C z := by
  classical
  by_cases hall : ∀ n, StrictCritical C stream t n → w ∈ C n
  · have hf := scopedFocus_spec hzt hz
    have hsel : selectIndex C stream t w = scopedFocus C stream t := by
      rw [selectIndex]
      simp only [dif_pos hall]
    rw [hsel]
    refine ⟨hf.2.1, hf.2.2, ?_⟩
    rcases eq_or_lt_of_le hf.2.2 with heq | hlt
    · simp [heq]
    · exact (strictCritical_ssubset_of_lt hlt hz hf.2.1).le
  · have hbad : ∃ n, BadStrictCritical C stream t w n := by
      simpa [BadStrictCritical] using hall
    let b := firstBadStrictCritical C stream t w
    have hb := firstBadStrictCritical_spec hbad
    have hzb : z < b := by
      have hle : z ≤ b := by
        by_contra hnot
        have hbz : b < z := Nat.lt_of_not_ge hnot
        have hsub : C z ⊆ C b :=
          (strictCritical_ssubset_of_lt hbz hb.1 hz).le
        exact hb.2 (hsub hw)
      exact lt_of_le_of_ne hle (fun heq => hb.2 (by simpa [heq] using hw))
    let S := boundaryCandidates C stream t w
    have hzS : z ∈ S := by
      simpa [S, b] using mem_boundaryCandidates.mpr ⟨hzb, hz, hw⟩
    have hne : S.Nonempty := ⟨z, hzS⟩
    have hsel : selectIndex C stream t w = S.max' hne := by
      rw [selectIndex]
      simp only [dif_neg hall]
      simp [S, hne]
    have hmS : S.max' hne ∈ S := Finset.max'_mem S hne
    have hmParts :
        StrictCritical C stream t (S.max' hne) ∧ w ∈ C (S.max' hne) := by
      exact (mem_boundaryCandidates.mp (by simpa [S] using hmS)).2
    have hzm : z ≤ S.max' hne := Finset.le_max' S z hzS
    rw [hsel]
    refine ⟨hmParts.1, hzm, ?_⟩
    rcases eq_or_lt_of_le hzm with heq | hlt
    · simp [heq]
    · exact (strictCritical_ssubset_of_lt hlt hz hmParts.1).le

/-- Round t+1 uses stage t and the new value stream t. -/
noncomputable def guessIndex
    (C : LanguageFamily) (stream : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => selectIndex C stream t (stream t)

/-- Eventual index validity of the guessed languages. -/
def IndexValidInLimit
    (C : LanguageFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t → C (guessIndex C stream t) ⊆ C z

/-- Proposition 3.4: the selector is eventually index-valid. -/
theorem proposition_3_4
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z := by
  obtain ⟨T, hT⟩ := lemma_3_3 hP hfirst
  refine ⟨max (T + 1) (z + 1), ?_⟩
  intro r hr
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have htT : T ≤ t := by omega
  have hzt : z ≤ t := by omega
  have hz := hT t htT
  have hw : stream t ∈ C z := by
    rw [← hP]
    exact ⟨t, rfl⟩
  exact (selectIndex_spec hzt hz hw).2.2

end GenLimit.KleinbergWei.DensityMeasures
