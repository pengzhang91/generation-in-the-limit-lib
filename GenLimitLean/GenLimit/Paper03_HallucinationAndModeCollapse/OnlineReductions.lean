import GenLimit.Paper03_HallucinationAndModeCollapse.Definitions
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import Mathlib.Data.Finset.Max

/-!
# Online identification reductions

This file checks the deterministic reductions behind Theorems 3.5, 3.7, and
3.9.  The identifiers are semantic Lean functions.  `SupportGenerator`
nevertheless carries the exact Boolean support-membership interface used by
the paper; this development does not promote that interface to a theorem about
Turing-machine codes.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic
open scoped symmDiff

noncomputable section

noncomputable local instance onlineReductionsPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## Finite uniformization -/

/-- Finitely many eventual pointwise facts have one common threshold. -/
theorem finite_uniform_threshold
    (P : ℕ → ℕ → Prop) :
    ∀ z, (∀ i, i < z → ∃ T, ∀ t, T ≤ t → P i t) →
      ∃ T, ∀ i, i < z → ∀ t, T ≤ t → P i t := by
  intro z h
  obtain ⟨T, hT⟩ := GenLimit.Angluin.eventually_all_lt (k := z) h
  exact ⟨T, fun i hi t ht => hT t ht i hi⟩

/-! ## Exact-support labels: Theorem 3.5's negative reduction -/

/-- Candidate `i` agrees with a proposed target set on the first `t` domain
points.  The domain enumeration is the identity enumeration of `ℕ`. -/
def MatchesInitialSegment
    (C : Generic.LanguageFamily ℕ) (S : Set ℕ) (t i : ℕ) : Prop :=
  ∀ x, x < t → (x ∈ C i ↔ x ∈ S)

/-- The least language matching all currently inspected labels, with an
arbitrary default when no language matches. -/
noncomputable def leastMatchingIndex
    (C : Generic.LanguageFamily ℕ) (S : Set ℕ) (t : ℕ) : ℕ :=
  if h : ∃ i, MatchesInitialSegment C S t i then Nat.find h else 0

theorem leastMatchingIndex_eq
    {C : Generic.LanguageFamily ℕ} {S : Set ℕ} {t z : ℕ}
    (hz : MatchesInitialSegment C S t z)
    (hearlier : ∀ i, i < z → ¬MatchesInitialSegment C S t i) :
    leastMatchingIndex C S t = z := by
  let hex : ∃ i, MatchesInitialSegment C S t i := ⟨z, hz⟩
  rw [leastMatchingIndex, dif_pos hex]
  have hle : Nat.find hex ≤ z := Nat.find_min' hex hz
  have hnotlt : ¬Nat.find hex < z := by
    intro hlt
    exact hearlier (Nat.find hex) hlt (Nat.find_spec hex)
  omega

/-- The paper's finite-label identifier, with the fresh positive sample added
back to the support. -/
noncomputable def completedSupportIdentifier
    (C : Generic.LanguageFamily ℕ) (G : SupportGenerator) :
    GenLimit.Angluin.SemanticIdentifier ℕ :=
  GenLimit.learnerOfFiniteHistory fun t xs =>
    leastMatchingIndex C
      (G.support t xs ∪ ↑(Generic.sequenceSample xs)) t

theorem completedSupportIdentifier_output
    (C : Generic.LanguageFamily ℕ) (G : SupportGenerator)
    (stream : Stream ℕ) (t : ℕ) :
    completedSupportIdentifier C G (GenLimit.textPrefix stream t) =
      leastMatchingIndex C (completedSupport G stream t) t := by
  simp only [completedSupportIdentifier,
    GenLimit.learnerOfFiniteHistory_textPrefix, completedSupport, supportAt]
  rw [sequenceSample_prefix]

theorem eventually_leastMatching_of_target
    {C : Generic.LanguageFamily ℕ} {z : ℕ}
    (hzleast : IsLeastTargetIndex C z) :
    ∃ T, ∀ t, T ≤ t →
      ∀ i, i < z →
        ¬MatchesInitialSegment C (C z) t i := by
  obtain ⟨T, hT⟩ := finite_uniform_threshold
    (fun i t => ¬MatchesInitialSegment C (C z) t i) z (by
      intro i hiz
      have hne := hzleast i hiz
      have hdiff : ∃ x, (x ∈ C i) ≠ (x ∈ C z) := by
        by_contra hdiff
        push_neg at hdiff
        apply hne
        ext x
        exact Iff.of_eq (hdiff x)
      obtain ⟨x, hx⟩ := hdiff
      refine ⟨x + 1, ?_⟩
      intro t ht hmatch
      exact hx (propext
        (hmatch x (lt_of_lt_of_le (Nat.lt_succ_self x) ht))))
  exact ⟨T, fun t ht i hi => hT i hi t ht⟩

/-- If completed supports eventually equal every target, the family is
positively identifiable.  This is the exact finite-label reduction used in the
negative direction of Theorem 3.5. -/
theorem identifiable_of_completedSupport
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    (hcomplete : ∀ z stream, Generic.Presents stream (C z) →
      ∃ T, ∀ t, T ≤ t → completedSupport G stream t = C z) :
    IdentifiableInLimit C := by
  refine ⟨completedSupportIdentifier C G, ?_⟩
  intro z stream hP
  let hex : ∃ i, C i = C z := ⟨z, rfl⟩
  let z₀ := Nat.find hex
  have hz₀ : C z₀ = C z := Nat.find_spec hex
  have hz₀least : IsLeastTargetIndex C z₀ := by
    intro i hi hieq
    exact Nat.find_min hex hi (hieq.trans hz₀)
  obtain ⟨Tc, hTc⟩ := hcomplete z stream hP
  obtain ⟨Td, hTd⟩ := eventually_leastMatching_of_target hz₀least
  refine ⟨z₀, hz₀, max Tc Td, ?_⟩
  intro t ht
  change completedSupportIdentifier C G (GenLimit.textPrefix stream t) = z₀
  rw [completedSupportIdentifier_output]
  have hct : completedSupport G stream t = C z := by
    exact hTc t (le_trans (Nat.le_max_left _ _) ht)
  have htarget : MatchesInitialSegment C (completedSupport G stream t) t z₀ := by
    intro x _hx
    rw [hct, hz₀]
  apply leastMatchingIndex_eq htarget
  intro i hi
  rw [hct, ← hz₀]
  exact hTd t (le_trans (Nat.le_max_right _ _) ht) i hi

/-- The fresh-output version of the negative direction of Theorem 3.5.  The
sample must be reunited with the support before it is used as target labels. -/
theorem theorem_3_5_fresh_negative_core
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    (h : FreshBreadthInLimit G C) :
    IdentifiableInLimit C := by
  apply identifiable_of_completedSupport
  intro z stream hP
  obtain ⟨T, hT⟩ := h z stream hP
  exact ⟨T, fun t ht =>
    completedSupport_of_freshBreadth hP (hT t ht)⟩

/-- The repetition-allowing convention used literally in the printed proof of
Theorem 3.5 also yields identification. -/
theorem theorem_3_5_repeating_negative_core
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    (h : RepeatingBreadthInLimit G C) :
    IdentifiableInLimit C := by
  apply identifiable_of_completedSupport
  intro z stream hP
  obtain ⟨T, hT⟩ := h z stream hP
  exact ⟨T, fun t ht =>
    completedSupport_of_repeatingBreadth hP (hT t ht)⟩

/-! ## Approximate breadth: Theorem 3.9 -/

theorem stable_approximate_completedSupport
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    (hstable : Stable G C)
    (happrox : ApproximateBreadthInLimit G C) :
    ∀ z stream, Generic.Presents stream (C z) →
      ∃ T, ∀ t, T ≤ t → completedSupport G stream t = C z := by
  intro z stream hP
  obtain ⟨Ts, hTs⟩ := hstable z stream hP
  obtain ⟨Ta, hTa⟩ := happrox z stream hP
  let T₀ := max Ts Ta
  let S := supportAt G stream T₀
  have hSapprox : ApproximateBreadthAt S (C z) := by
    exact hTa T₀ (Nat.le_max_right _ _)
  have hmissing : (C z \ S).Finite := hSapprox.2
  obtain ⟨Tc, hTc⟩ :=
    finset_eventually_subset_sample hP hmissing.toFinset (by
      intro x hx
      have hx' : x ∈ C z \ S :=
        (Set.Finite.mem_toFinset hmissing).mp hx
      exact hx'.1)
  refine ⟨max T₀ Tc, ?_⟩
  intro t ht
  have htT₀ : T₀ ≤ t := le_trans (Nat.le_max_left _ _) ht
  have htTs : Ts ≤ t :=
    le_trans (Nat.le_max_left _ _) htT₀
  have hstable_t : supportAt G stream t = S := by
    exact hTs t T₀ htTs (Nat.le_max_left _ _)
  have hsample : hmissing.toFinset ⊆ Generic.sample stream t := by
    intro x hx
    exact Generic.sample_mono
      (le_trans (Nat.le_max_right _ _) ht) (hTc hx)
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | hx
    · rw [hstable_t] at hx
      exact hSapprox.1 hx
    · exact Generic.mem_language_of_mem_sample_of_presents hP hx
  · intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inl (by simpa only [hstable_t] using hxS)
    · exact Or.inr
        (hsample ((Set.Finite.mem_toFinset hmissing).mpr ⟨hx, hxS⟩))

/-- Theorem 3.9 at the exact online semantic level: a stable approximate-
breadth generator would yield a positive-data identifier. -/
theorem theorem_3_9
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    (hstable : Stable G C)
    (happrox : ApproximateBreadthInLimit G C) :
    IdentifiableInLimit C :=
  identifiable_of_completedSupport
    (stable_approximate_completedSupport hstable happrox)

/-- Contrapositive form matching the impossibility wording of Theorem 3.9. -/
theorem theorem_3_9_impossibility
    {C : Generic.LanguageFamily ℕ}
    (hnot : ¬IdentifiableInLimit C) :
    ¬∃ G : SupportGenerator,
      Stable G C ∧ ApproximateBreadthInLimit G C := by
  rintro ⟨G, hstable, happrox⟩
  exact hnot (theorem_3_9 hstable happrox)

/-! ## Unambiguous generation: Theorem 3.7 -/

/-- Candidate condition used by the proof of Theorem 3.7.  A candidate must
contain the positive sample and its first `t` domain points must be covered by
the generator support together with that sample. -/
def Eligible
    (C : Generic.LanguageFamily ℕ) (S : Set ℕ)
    (observed : Finset ℕ) (t i : ℕ) : Prop :=
  (↑observed : Set ℕ) ⊆ C i ∧
    ∀ x, x < t → x ∈ C i → x ∈ S ∪ ↑observed

noncomputable def leastEligibleIndex
    (C : Generic.LanguageFamily ℕ) (S : Set ℕ)
    (observed : Finset ℕ) (t : ℕ) : ℕ :=
  if h : ∃ i, Eligible C S observed t i then Nat.find h else 0

theorem leastEligibleIndex_eq
    {C : Generic.LanguageFamily ℕ} {S : Set ℕ}
    {observed : Finset ℕ} {t z : ℕ}
    (hz : Eligible C S observed t z)
    (hearlier : ∀ i, i < z → ¬Eligible C S observed t i) :
    leastEligibleIndex C S observed t = z := by
  let hex : ∃ i, Eligible C S observed t i := ⟨z, hz⟩
  rw [leastEligibleIndex, dif_pos hex]
  have hle : Nat.find hex ≤ z := Nat.find_min' hex hz
  have hnotlt : ¬Nat.find hex < z := by
    intro hlt
    exact hearlier (Nat.find hex) hlt (Nat.find_spec hex)
  omega

noncomputable def unambiguousIdentifier
    (C : Generic.LanguageFamily ℕ) (G : SupportGenerator) :
    GenLimit.Angluin.SemanticIdentifier ℕ :=
  GenLimit.learnerOfFiniteHistory fun t xs =>
    leastEligibleIndex C (G.support t xs) (Generic.sequenceSample xs) t

theorem unambiguousIdentifier_output
    (C : Generic.LanguageFamily ℕ) (G : SupportGenerator)
    (stream : Stream ℕ) (t : ℕ) :
    unambiguousIdentifier C G (GenLimit.textPrefix stream t) =
      leastEligibleIndex C (supportAt G stream t)
        (Generic.sample stream t) t := by
  simp only [unambiguousIdentifier,
    GenLimit.learnerOfFiniteHistory_textPrefix, supportAt]
  rw [sequenceSample_prefix]

theorem exists_distinct_from_target
    {C : Generic.LanguageFamily ℕ} (hC : HasDistinctLanguages C) (z : ℕ) :
    ∃ j, C j ≠ C z := by
  obtain ⟨i, j, hij⟩ := hC
  by_cases hi : C i = C z
  · exact ⟨j, fun hj => hij (hi.trans hj.symm)⟩
  · exact ⟨i, hi⟩

theorem symmDiff_target_finite
    {C : Generic.LanguageFamily ℕ} {z : ℕ} {S : Set ℕ}
    (hC : HasDistinctLanguages C)
    (hU : UnambiguousAt C z S) :
    (S ∆ C z).Finite := by
  obtain ⟨j, hj⟩ := exists_distinct_from_target hC z
  rw [← Set.encard_lt_top_iff]
  exact lt_of_lt_of_le (hU j hj) (le_top : (S ∆ C j).encard ≤ ⊤)

theorem missing_target_finite_of_unambiguous
    {C : Generic.LanguageFamily ℕ} {z : ℕ} {S : Set ℕ}
    (hC : HasDistinctLanguages C)
    (hU : UnambiguousAt C z S) :
    (C z \ S).Finite := by
  apply (symmDiff_target_finite hC hU).subset
  intro x hx
  exact Or.inr hx

/-- The set-theoretic cancellation step in the proof of Theorem 3.7: if
`K ⊂ L` and `S` is strictly closer to `K`, some point of `L` is outside both
`K` and `S`. -/
theorem strictSuperset_has_uncovered
    {S K L : Set ℕ}
    (hKL : K ⊆ L)
    (hclose : (S ∆ K).encard < (S ∆ L).encard) :
    ∃ x, x ∈ L ∧ x ∉ K ∧ x ∉ S := by
  by_contra h
  push_neg at h
  have hLsub : L ⊆ K ∪ S := by
    intro x hxL
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr (h x hxL hxK)
  have hsd : S ∆ L ⊆ S ∆ K := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hx.1, fun hxK => hx.2 (hKL hxK)⟩
    · rcases hLsub hx.1 with hxK | hxS
      · exact Or.inr ⟨hxK, hx.2⟩
      · exact False.elim (hx.2 hxS)
  exact (not_lt_of_ge (Set.encard_mono hsd)) hclose

theorem eventually_target_eligible
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    {z : ℕ} {stream : Stream ℕ}
    (hP : Generic.Presents stream (C z))
    (hC : HasDistinctLanguages C)
    (hstable : Stable G C)
    (hunamb : UnambiguousInLimit G C) :
    ∃ T, ∀ t, T ≤ t →
      Eligible C (supportAt G stream t) (Generic.sample stream t) t z := by
  obtain ⟨Ts, hTs⟩ := hstable z stream hP
  obtain ⟨Tu, hTu⟩ := hunamb z stream hP
  let T₀ := max Ts Tu
  let S := supportAt G stream T₀
  have hU : UnambiguousAt C z S :=
    hTu T₀ (Nat.le_max_right _ _)
  have hmissing : (C z \ S).Finite :=
    missing_target_finite_of_unambiguous hC hU
  obtain ⟨Tc, hTc⟩ :=
    finset_eventually_subset_sample hP hmissing.toFinset (by
      intro x hx
      have hx' : x ∈ C z \ S :=
        (Set.Finite.mem_toFinset hmissing).mp hx
      exact hx'.1)
  refine ⟨max T₀ Tc, ?_⟩
  intro t ht
  have htT₀ : T₀ ≤ t := le_trans (Nat.le_max_left _ _) ht
  have hsupport : supportAt G stream t = S := by
    exact hTs t T₀
      (le_trans (Nat.le_max_left _ _) htT₀)
      (Nat.le_max_left _ _)
  have hsample : hmissing.toFinset ⊆ Generic.sample stream t :=
    fun x hx => Generic.sample_mono
      (le_trans (Nat.le_max_right _ _) ht) (hTc hx)
  constructor
  · intro x hx
    exact Generic.mem_language_of_mem_sample_of_presents hP hx
  · intro x _hxt hxK
    by_cases hxS : x ∈ S
    · exact Or.inl (by simpa only [hsupport] using hxS)
    · exact Or.inr
        (hsample ((Set.Finite.mem_toFinset hmissing).mpr ⟨hxK, hxS⟩))

theorem eventually_earlier_not_eligible
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    {z : ℕ} {stream : Stream ℕ}
    (hP : Generic.Presents stream (C z))
    (hzleast : IsLeastTargetIndex C z)
    (hstable : Stable G C)
    (hunamb : UnambiguousInLimit G C) :
    ∃ T, ∀ i, i < z → ∀ t, T ≤ t →
      ¬Eligible C (supportAt G stream t) (Generic.sample stream t) t i := by
  obtain ⟨Ts, hTs⟩ := hstable z stream hP
  obtain ⟨Tu, hTu⟩ := hunamb z stream hP
  let T₀ := max Ts Tu
  let S := supportAt G stream T₀
  have hU : UnambiguousAt C z S :=
    hTu T₀ (Nat.le_max_right _ _)
  apply finite_uniform_threshold
  intro i hiz
  have hne : C i ≠ C z := hzleast i hiz
  by_cases hsub : C z ⊆ C i
  · obtain ⟨x, hxi, hxz, hxS⟩ :=
      strictSuperset_has_uncovered hsub (hU i hne)
    refine ⟨max T₀ (x + 1), ?_⟩
    intro t ht helig
    have htT₀ : T₀ ≤ t := le_trans (Nat.le_max_left _ _) ht
    have hsupport : supportAt G stream t = S := by
      exact hTs t T₀
        (le_trans (Nat.le_max_left _ _) htT₀)
        (Nat.le_max_left _ _)
    have hcovered :=
      helig.2 x (lt_of_lt_of_le (Nat.lt_succ_self x)
        (le_trans (Nat.le_max_right _ _) ht)) hxi
    rcases hcovered with hxout | hxsample
    · exact hxS (by simpa only [hsupport] using hxout)
    · exact hxz
        (Generic.mem_language_of_mem_sample_of_presents hP hxsample)
  · obtain ⟨x, hxz, hxi⟩ := Set.not_subset.mp hsub
    obtain ⟨Tx, hTx⟩ :=
      Generic.eventually_mem_sample_of_presents hP hxz
    refine ⟨Tx, ?_⟩
    intro t ht helig
    exact hxi (helig.1 (hTx t ht))

/-- Theorem 3.7 at the exact online semantic level.  It proves the reduction
asserted by the source: stable unambiguous generation yields positive-data
identification. -/
theorem theorem_3_7
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    (hC : HasDistinctLanguages C)
    (hstable : Stable G C)
    (hunamb : UnambiguousInLimit G C) :
    IdentifiableInLimit C := by
  refine ⟨unambiguousIdentifier C G, ?_⟩
  intro z stream hP
  let hex : ∃ i, C i = C z := ⟨z, rfl⟩
  let z₀ := Nat.find hex
  have hz₀ : C z₀ = C z := Nat.find_spec hex
  have hz₀least : IsLeastTargetIndex C z₀ := by
    intro i hi hieq
    exact Nat.find_min hex hi (hieq.trans hz₀)
  have hP₀ : Generic.Presents stream (C z₀) := by
    simpa only [hz₀] using hP
  obtain ⟨Tz, hTz⟩ :=
    eventually_target_eligible hP₀ hC hstable hunamb
  obtain ⟨Te, hTe⟩ :=
    eventually_earlier_not_eligible hP₀ hz₀least hstable hunamb
  refine ⟨z₀, hz₀, max Tz Te, ?_⟩
  intro t ht
  change unambiguousIdentifier C G (GenLimit.textPrefix stream t) = z₀
  rw [unambiguousIdentifier_output]
  apply leastEligibleIndex_eq
  · exact hTz t (le_trans (Nat.le_max_left _ _) ht)
  · intro i hi
    exact hTe i hi t (le_trans (Nat.le_max_right _ _) ht)

theorem identifiable_of_no_distinctLanguages
    {C : Generic.LanguageFamily ℕ}
    (hC : ¬HasDistinctLanguages C) :
    IdentifiableInLimit C := by
  let M : GenLimit.Angluin.SemanticIdentifier ℕ := fun _history => 0
  refine ⟨M, ?_⟩
  intro z stream _hP
  have hz : C 0 = C z := by
    by_contra hne
    exact hC ⟨0, z, hne⟩
  refine ⟨0, hz, 0, ?_⟩
  intro t _ht
  rfl

theorem hasDistinctLanguages_of_not_identifiable
    {C : Generic.LanguageFamily ℕ}
    (hnot : ¬IdentifiableInLimit C) :
    HasDistinctLanguages C := by
  by_contra hC
  exact hnot (identifiable_of_no_distinctLanguages hC)

/-- Contrapositive form matching the impossibility wording of Theorem 3.7. -/
theorem theorem_3_7_impossibility
    {C : Generic.LanguageFamily ℕ}
    (hnot : ¬IdentifiableInLimit C) :
    ¬∃ G : SupportGenerator,
      Stable G C ∧ UnambiguousInLimit G C := by
  rintro ⟨G, hstable, hunamb⟩
  exact hnot
    (theorem_3_7 (hasDistinctLanguages_of_not_identifiable hnot)
      hstable hunamb)

end

end GenLimit.HallucinationModeCollapse
