import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Accurate

/-!
# #07 Density Measures: accuracy infinitely often

Proposition 3.5 and Theorem 3.1 (Overview Theorem 2.1). The proof formalizes
the paper's changepoint argument for the least strict-critical index after the
target.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- The least strictly critical index after z, with an irrelevant default. -/
noncomputable def nextStrictCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t z : ℕ) : ℕ := by
  classical
  exact if h : ∃ n, z < n ∧ StrictCritical C stream t n then
    Nat.find h
  else 0

theorem nextStrictCritical_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z : ℕ}
    (h : ∃ n, z < n ∧ StrictCritical C stream t n) :
    z < nextStrictCritical C stream t z ∧
      StrictCritical C stream t (nextStrictCritical C stream t z) := by
  classical
  simp only [nextStrictCritical, dif_pos h]
  exact Nat.find_spec h

theorem nextStrictCritical_min
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z n : ℕ}
    (h : ∃ n, z < n ∧ StrictCritical C stream t n)
    (hn : z < n ∧ StrictCritical C stream t n) :
    nextStrictCritical C stream t z ≤ n := by
  classical
  simp only [nextStrictCritical, dif_pos h]
  exact Nat.find_min' h hn

/-- A natural-number sequence that is eventually nonincreasing eventually
stabilizes. -/
theorem eventually_constant_of_succ_le
    (a : ℕ → ℕ) (N : ℕ)
    (hstep : ∀ s, N ≤ s → a (s + 1) ≤ a s) :
    ∃ S, N ≤ S ∧ ∀ r, S ≤ r → a r = a S := by
  classical
  have hanti : AntitoneOn a (Set.Ici N) :=
    antitoneOn_nat_Ici_of_succ_le hstep
  have hreach : ∃ v, ∃ s, N ≤ s ∧ a s = v :=
    ⟨a N, N, le_rfl, rfl⟩
  let v := Nat.find hreach
  obtain ⟨S, hNS, haS⟩ := Nat.find_spec hreach
  refine ⟨S, hNS, ?_⟩
  intro r hSr
  have hNr : N ≤ r := le_trans hNS hSr
  have har_le : a r ≤ a S := hanti hNS hNr hSr
  have hv_le : v ≤ a r :=
    Nat.find_min' hreach ⟨r, hNr, rfl⟩
  have haS_le : a S ≤ a r := haS.trans_le hv_le
  exact le_antisymm har_le haS_le

theorem exists_increase_of_not_eventually_constant
    (a : ℕ → ℕ) (N : ℕ)
    (hnot : ¬∃ S, N ≤ S ∧ ∀ r, S ≤ r → a r = a S) :
    ∃ s, N ≤ s ∧ a s < a (s + 1) := by
  by_contra hinc
  have hstep : ∀ s, N ≤ s → a (s + 1) ≤ a s := by
    intro s hs
    have hnlt : ¬a s < a (s + 1) := by
      intro hlt
      exact hinc ⟨s, hs, hlt⟩
    omega
  exact hnot (eventually_constant_of_succ_le a N hstep)

/-- Accuracy means equality of guessed and target languages, not necessarily
equality of their family indices. -/
def AccurateAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (z r : ℕ) : Prop :=
  C (guessIndex C stream r) = C z

/-- Proposition 3.5: after every round there is a later accurate round. -/
theorem proposition_3_5
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r := by
  obtain ⟨T, hT⟩ := lemma_3_3 hP hfirst
  intro t₀
  by_contra hfuture
  push_neg at hfuture
  let N := max T (max z t₀)
  have hTN : T ≤ N := le_trans (Nat.le_max_left _ _) le_rfl
  have hzN : z ≤ N :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have htN : t₀ ≤ N :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hExists :
      ∀ s, N ≤ s → ∃ n, z < n ∧ StrictCritical C stream s n := by
    intro s hs
    have hsT : T ≤ s := le_trans hTN hs
    have hzs : z ≤ s := le_trans hzN hs
    have hzcrit := hT s hsT
    have hw : stream s ∈ C z := by
      rw [← hP]
      exact ⟨s, rfl⟩
    let n := selectIndex C stream s (stream s)
    have hn := selectIndex_spec hzs hzcrit hw
    have hn_ne : n ≠ z := by
      intro hnz
      have hacc : AccurateAt C stream z (s + 1) := by
        simp [AccurateAt, guessIndex, n, hnz]
      exact hfuture (s + 1) (le_trans htN (by omega)) hacc
    exact ⟨n, lt_of_le_of_ne hn.2.1 hn_ne.symm, hn.1⟩
  let a : ℕ → ℕ := fun s => nextStrictCritical C stream s z
  have hnotconst :
      ¬∃ S, N ≤ S ∧ ∀ r, S ≤ r → a r = a S := by
    rintro ⟨S, hNS, hconst⟩
    have hES := hExists S hNS
    have haS := nextStrictCritical_spec hES
    have hzS : StrictCritical C stream S z :=
      hT S (le_trans hTN hNS)
    have hproper : C (a S) ⊂ C z :=
      strictCritical_ssubset_of_lt haS.1 hzS haS.2
    obtain ⟨u, huz, hua⟩ := Set.exists_of_ssubset hproper
    obtain ⟨U, hU⟩ := eventually_mem_sample_of_presents hP huz
    let r := max S U
    have hSr : S ≤ r := Nat.le_max_left _ _
    have hNr : N ≤ r := le_trans hNS hSr
    have hEr := hExists r hNr
    have har := nextStrictCritical_spec hEr
    have hEq : a r = a S := hconst r hSr
    have huSample : u ∈ sample stream r :=
      hU r (Nat.le_max_right _ _)
    have huAr : u ∈ C (a r) := har.2.1 huSample
    exact hua (by simpa [hEq] using huAr)
  obtain ⟨s, hNs, hincrease⟩ :=
    exists_increase_of_not_eventually_constant a N hnotconst
  have hEs := hExists s hNs
  have hEs1 := hExists (s + 1) (by omega)
  have ha := nextStrictCritical_spec hEs
  have hzcrit : StrictCritical C stream s z :=
    hT s (le_trans hTN hNs)
  have hwz : stream s ∈ C z := by
    rw [← hP]
    exact ⟨s, rfl⟩
  have ha_not_next : ¬StrictCritical C stream (s + 1) (a s) := by
    intro haNext
    have hmin := nextStrictCritical_min hEs1 ⟨ha.1, haNext⟩
    exact not_lt_of_ge hmin hincrease
  have ha_inconsistent : ¬Consistent C stream (s + 1) (a s) := by
    intro hcon
    exact ha_not_next (claim_3_2 (by omega) ha.2 hcon)
  have hwa : stream s ∉ C (a s) := by
    intro hmem
    apply ha_inconsistent
    intro u hu
    have hu' : u ∈ sample stream (s + 1) := by simpa using hu
    rw [mem_sample_iff] at hu'
    obtain ⟨q, hq, rfl⟩ := hu'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hqs | rfl
    · exact ha.2.1 (value_mem_sample hqs)
    · exact hmem
  have haBad : BadStrictCritical C stream s (stream s) (a s) :=
    ⟨ha.2, hwa⟩
  have hbad : ∃ n, BadStrictCritical C stream s (stream s) n :=
    ⟨a s, haBad⟩
  have hnoBadBefore :
      ∀ n, n < a s → ¬BadStrictCritical C stream s (stream s) n := by
    intro n hna hnBad
    by_cases hnz : n < z
    · have hsub : C z ⊆ C n :=
        (strictCritical_ssubset_of_lt hnz hnBad.1 hzcrit).le
      exact hnBad.2 (hsub hwz)
    · have hzn : z ≤ n := Nat.le_of_not_gt hnz
      rcases eq_or_lt_of_le hzn with rfl | hzn'
      · exact hnBad.2 hwz
      · have hmin := nextStrictCritical_min hEs ⟨hzn', hnBad.1⟩
        exact not_lt_of_ge hmin hna
  have hfirstBad :
      firstBadStrictCritical C stream s (stream s) = a s := by
    apply le_antisymm
    · exact firstBadStrictCritical_min hbad haBad
    · by_contra hnot
      have hlt : firstBadStrictCritical C stream s (stream s) < a s := by
        omega
      exact hnoBadBefore _ hlt (firstBadStrictCritical_spec hbad)
  let B := boundaryCandidates C stream s (stream s)
  have hzB : z ∈ B := by
    apply mem_boundaryCandidates.mpr
    exact ⟨by simpa [hfirstBad] using ha.1, hzcrit, hwz⟩
  have hBne : B.Nonempty := ⟨z, hzB⟩
  have hBmax : B.max' hBne = z := by
    apply le_antisymm
    · apply Finset.max'_le
      intro n hnB
      have hnParts := mem_boundaryCandidates.mp (by simpa [B] using hnB)
      by_contra hnle
      have hzn : z < n := Nat.lt_of_not_ge hnle
      have hmin := nextStrictCritical_min hEs ⟨hzn, hnParts.2.1⟩
      have hna : n < a s := by simpa [hfirstBad] using hnParts.1
      exact not_lt_of_ge hmin hna
    · exact Finset.le_max' B z hzB
  have hallFalse :
      ¬∀ n, StrictCritical C stream s n → stream s ∈ C n := by
    intro hall
    exact hwa (hall (a s) ha.2)
  have hselect : selectIndex C stream s (stream s) = z := by
    rw [selectIndex]
    simp only [dif_neg hallFalse]
    simp [B, hBne, hBmax]
  have hacc : AccurateAt C stream z (s + 1) := by
    simp [AccurateAt, guessIndex, hselect]
  exact hfuture (s + 1) (le_trans htN (by omega)) hacc

/-- Theorem 3.1: one selector is eventually index-valid and accurate at
arbitrarily late rounds. -/
theorem theorem_3_1
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z ∧
      ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r :=
  ⟨proposition_3_4 hP hfirst, proposition_3_5 hP hfirst⟩

/-- Overview Theorem 2.1. -/
theorem theorem_2_1
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z ∧
      ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r :=
  theorem_3_1 hP hfirst

end GenLimit.KleinbergWei.DensityMeasures
