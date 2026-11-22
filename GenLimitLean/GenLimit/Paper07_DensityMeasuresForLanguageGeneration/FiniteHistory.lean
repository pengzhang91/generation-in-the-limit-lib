import GenLimit.Bridges.Paper39ToPaper07
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.IndexLimsup
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.IndexMinimax

/-! # Finite observations and the output set of Section 2

At round `t` the generator receives the observations through `t`, including
the current input. The same function of finite histories serves every target
and presentation. Density is measured on the generated words in the target.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- The Section 3 index selector, evaluated on a finite chronological history. -/
noncomputable def indexHistoryRule (C : LanguageFamily) (xs : List ℕ) :=
  guessIndex C (Generic.historyThenFallback xs 0) xs.length

theorem indexHistoryRule_prefix (C : LanguageFamily) (s : ℕ → ℕ) (t : ℕ) :
    indexHistoryRule C (textPrefix s t) = guessIndex C s t := by
  simp only [indexHistoryRule,textPrefix_length]
  cases t with
  | zero => rfl
  | succ t =>
    let d := Generic.historyThenFallback (textPrefix s (t+1)) 0
    have agree (k : ℕ) (hk : k ≤ t) : d k = s k := by
      have h : k < t+1 := by omega
      simp [d,Generic.historyThenFallback,textPrefix,h]
    have seen : sample d t = sample s t :=
      sample_eq_of_eq_on_prefix (fun k hk ↦ agree k (Nat.le_of_lt hk))
    change selectIndex C d t (d t) = selectIndex C s t (s t)
    have crit : StrictCritical C d t = StrictCritical C s t := by
      funext i
      simp only [StrictCritical,Consistent,seen]
    classical
    rw [agree t le_rfl]
    let w := s t
    have focus : scopedFocus C d t = scopedFocus C s t := by
      unfold scopedFocus scopedStrictCriticalIndices
      rw [crit]
    have bad : BadStrictCritical C d t w = BadStrictCritical C s t w := by
      funext i
      simp only [BadStrictCritical,crit]
    let least (P : ℕ → Prop) := if h : ∃ i, P i then Nat.find h else 0
    have first : firstBadStrictCritical C d t w = firstBadStrictCritical C s t w :=
      congrArg least bad
    have candidates : boundaryCandidates C d t w = boundaryCandidates C s t w := by
      ext i
      simp only [mem_boundaryCandidates,first,crit]
    by_cases good : ∀ i, StrictCritical C s t i → w ∈ C i
    · have good' := crit.symm ▸ good
      simp only [selectIndex,show s t = w from rfl,dif_pos good,dif_pos good',focus]
    · have bad' : ¬ ∀ i, StrictCritical C d t i → w ∈ C i := by rw [crit]; exact good
      let pick (S : Finset ℕ) (fallback : ℕ) := if h : S.Nonempty then S.max' h else fallback
      simp only [selectIndex,show s t = w from rfl,dif_neg good,dif_neg bad']
      exact congrArg₂ pick candidates focus

namespace OrderedFocus

/-- Execute an element rule on the chronological prefix available at each round. -/
def play (A : List ℕ → ℕ) (s : ℕ → ℕ) (t : ℕ) := A (textPrefix s (t + 1))

/-- The paper's output set relative to a particular target. -/
def generatedIn (A : List ℕ → ℕ) (s : ℕ → ℕ) (K : Language) : Language :=
  Set.range (play A s) ∩ K

/-- Evaluate the generator on a finite observation history, using its last
round. The value on the empty history is immaterial to an actual play. -/
noncomputable def historyRule (O : ℕ → OrderedLanguage) (xs : List ℕ) :=
  generate O (Generic.historyThenFallback xs 0) (xs.length - 1)

theorem play_historyRule (O : ℕ → OrderedLanguage) (s : ℕ → ℕ) :
    play (historyRule O) s = generate O s := by
  funext t
  simp only [play,historyRule,textPrefix_length,Nat.add_sub_cancel]
  apply generate_prefix
  intro k hk
  have h : k < t+1 := by omega
  simp [Generic.historyThenFallback,textPrefix,h]

/-- One finite-history rule yields the half-density bound on every target of
the collection. Trimming outputs outside the target preserves relative density. -/
theorem historyRule_density (O : ℕ → OrderedLanguage) (compat : Compatible O)
    {z : ℕ} {s : ℕ → ℕ} (hs : Presents s (O z).carrier) :
    ElementValid s (play (historyRule O) s) (O z).carrier ∧
      (1 / 2 : ℝ) ≤ (O z).lowerDensity (generatedIn (historyRule O) s (O z).carrier) := by
  simpa only [generatedIn,play_historyRule,OrderedLanguage.lowerDensity_inter_carrier]
    using generation_and_lowerDensity O compat hs

theorem historyRule_upper (O : ℕ → OrderedLanguage) (compat : Compatible O)
    {z : ℕ} {s : ℕ → ℕ} (hs : Presents s (O z).carrier) :
    ElementValid s (play (historyRule O) s) (O z).carrier ∧
      (1 / 2 : ℝ) ≤ (O z).upperDensity (generatedIn (historyRule O) s (O z).carrier) := by
  obtain ⟨hv,hd⟩ := historyRule_density O compat hs
  exact ⟨hv,hd.trans (Filter.liminf_le_limsup
    (Filter.isBoundedUnder_of ⟨1,(O z).prefixRatio_le_one _⟩)
    (Filter.isBoundedUnder_of ⟨0,(O z).prefixRatio_nonneg _⟩))⟩

end OrderedFocus
end GenLimit.KleinbergWei.DensityMeasures
