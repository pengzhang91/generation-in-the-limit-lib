import GenLimit.Paper09_RepresentativeLanguageGeneration.LimitFoundations
import GenLimit.Paper09_RepresentativeLanguageGeneration.FiniteSupport
import GenLimit.Support.Fresh
import Mathlib.Data.Finset.CastCard

/-!
# Exact group profiles and finite-support feasibility

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Definition 4.1, Lemma 4.8, and Theorem 4.4.

The intersection over groups containing a point in published Definition 4.1
records only its positive group memberships.  For overlapping groups this is
not equivalent to the full membership vector used in the proof of Lemma 4.8;
`TailCounterexample.lean` gives a concrete counterexample to that printed
condition.  This module states the repaired condition using exact membership
cells.  Under that condition, the proof's finite-exception argument is valid.
-/

namespace GenLimit.RepresentativeGeneration

/-! ## The repaired finite-support condition -/

/-- The points with exactly the same membership vector as `x` across all
groups.  Both positive and negative coordinates are recorded. -/
def exactGroupCell (groups : ℕ → Set α) (x : α) : Set α :=
  {y | ∀ i, y ∈ groups i ↔ x ∈ groups i}

@[simp]
theorem mem_exactGroupCell_iff
    {groups : ℕ → Set α} {x y : α} :
    y ∈ exactGroupCell groups x ↔
      ∀ i, y ∈ groups i ↔ x ∈ groups i :=
  Iff.rfl

theorem self_mem_exactGroupCell
    (groups : ℕ → Set α) (x : α) :
    x ∈ exactGroupCell groups x := by
  intro i
  rfl

theorem exactGroupCell_membership
    {groups : ℕ → Set α} {x y : α}
    (hy : y ∈ exactGroupCell groups x) (i : ℕ) :
    y ∈ groups i ↔ x ∈ groups i :=
  hy i

/-- Points of `L` whose exact group-profile cell inside `L` is finite. -/
def finiteExactProfilePoints
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) : Set α :=
  {x | x ∈ L ∧ (L ∩ exactGroupCell groups x).Finite}

/-- Repaired published Definition 4.1: every language has only finitely many points
whose exact membership-profile cell is finite. -/
def HasFiniteExactProfileSupport
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) : Prop :=
  ∀ L, L ∈ H → (finiteExactProfilePoints L groups).Finite

/-- A point of the target outside the repaired finite exceptional set has an
infinite exact-profile cell in the target. -/
theorem exactProfileCell_infinite_of_not_mem_finitePoints
    {L : GenLimit.Generic.Language α}
    {groups : ℕ → Set α} {x : α}
    (hxL : x ∈ L)
    (hx : x ∉ finiteExactProfilePoints L groups) :
    (L ∩ exactGroupCell groups x).Infinite := by
  intro hfinite
  exact hx ⟨hxL, hfinite⟩

/-! ## Moving empirical mass to fresh exact-profile representatives -/

/-- Move a point to an unseen target point.  If its target profile cell is
infinite, the chosen point has exactly the same profile; otherwise an
arbitrary unseen target point is used. -/
noncomputable def exactProfileFreshRepresentative
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (S : Finset α)
    (hL : L.Infinite) (x : α) : α := by
  classical
  if hcell : (L ∩ exactGroupCell groups x).Infinite then
    exact GenLimit.Support.freshFromInfinite
      (L ∩ exactGroupCell groups x) hcell S
  else
    exact GenLimit.Support.freshFromInfinite L hL S

theorem exactProfileFreshRepresentative_mem_target
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (S : Finset α)
    (hL : L.Infinite) (x : α) :
    exactProfileFreshRepresentative L groups S hL x ∈ L := by
  classical
  by_cases hcell : (L ∩ exactGroupCell groups x).Infinite
  · simp only [exactProfileFreshRepresentative, dif_pos hcell]
    exact (GenLimit.Support.freshFromInfinite_mem
      (L ∩ exactGroupCell groups x) hcell S).1
  · simp only [exactProfileFreshRepresentative, dif_neg hcell]
    exact GenLimit.Support.freshFromInfinite_mem L hL S

theorem exactProfileFreshRepresentative_not_mem_sample
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (S : Finset α)
    (hL : L.Infinite) (x : α) :
    exactProfileFreshRepresentative L groups S hL x ∉ S := by
  classical
  by_cases hcell : (L ∩ exactGroupCell groups x).Infinite
  · simp only [exactProfileFreshRepresentative, dif_pos hcell]
    exact GenLimit.Support.freshFromInfinite_not_mem
      (L ∩ exactGroupCell groups x) hcell S
  · simp only [exactProfileFreshRepresentative, dif_neg hcell]
    exact GenLimit.Support.freshFromInfinite_not_mem L hL S

theorem exactProfileFreshRepresentative_preserves_profile
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (S : Finset α)
    (hL : L.Infinite) {x : α}
    (hcell : (L ∩ exactGroupCell groups x).Infinite)
    (i : ℕ) :
    exactProfileFreshRepresentative L groups S hL x ∈ groups i ↔
      x ∈ groups i := by
  classical
  have hmem :
      exactProfileFreshRepresentative L groups S hL x ∈
        L ∩ exactGroupCell groups x := by
    simp only [exactProfileFreshRepresentative, dif_pos hcell]
    exact (Classical.choose_spec
      (hcell.exists_notMem_finset S)).1
  exact hmem.2 i

/-- The empirical PMF pushed to fresh target representatives. -/
noncomputable def exactProfileFreshDistribution
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (S : Finset α)
    (hL : L.Infinite) (hS : S.Nonempty) :
    DiscreteDistribution α :=
  DiscreteDistribution.ofPMF
    ((empiricalPointPMF S hS).map
      (exactProfileFreshRepresentative L groups S hL))

theorem exactProfileFreshDistribution_supportedOn
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (S : Finset α)
    (hL : L.Infinite) (hS : S.Nonempty) :
    SupportedOn
      (exactProfileFreshDistribution L groups S hL hS)
      (L \ (↑S : Set α)) := by
  classical
  intro y hy
  let p := empiricalPointPMF S hS
  let f := exactProfileFreshRepresentative L groups S hL
  have hyPMF : (p.map f) y ≠ 0 := by
    intro hzero
    apply hy
    unfold exactProfileFreshDistribution
    change ((p.map f) y).toReal = 0
    rw [hzero]
    simp
  obtain ⟨x, _hx, hxy⟩ :=
    (PMF.mem_support_map_iff f p y).mp hyPMF
  rw [← hxy]
  exact
    ⟨exactProfileFreshRepresentative_mem_target
        L groups S hL x,
      exactProfileFreshRepresentative_not_mem_sample
        L groups S hL x⟩

/-- A mapped empirical PMF measures a set by the empirical frequency of its
preimage. -/
theorem mappedEmpiricalDistribution_groupMass
    (S : Finset α) (hS : S.Nonempty)
    (f : α → β) (A : Set β) :
    groupMass
        (DiscreteDistribution.ofPMF
          ((empiricalPointPMF S hS).map f))
        A =
      empiricalGroupProbability S (fun _ => f ⁻¹' A) 0 := by
  classical
  rw [groupMass_ofPMF, PMF.toOuterMeasure_map_apply]
  have h :=
    empiricalPointDistribution_groupProbability
      S hS (fun _ : ℕ => f ⁻¹' A) 0
  simpa only [inducedGroupProbability,
    empiricalPointDistribution, groupMass_ofPMF] using h

/-! ## A finite-exception perturbation bound -/

/-- If a map preserves membership in `A` outside `B`, pushing the uniform
empirical distribution through it changes the `A` coordinate by at most the
empirical fraction of `B`. -/
theorem mappedEmpirical_groupMass_error_le
    (S B : Finset α) (hS : S.Nonempty)
    (f : α → β) (A : Set β) (originalA : Set α)
    (hpreserve :
      ∀ x, x ∈ S → x ∉ B →
        (f x ∈ A ↔ x ∈ originalA)) :
    |groupMass
          (DiscreteDistribution.ofPMF
            ((empiricalPointPMF S hS).map f))
          A -
        empiricalGroupProbability S (fun _ => originalA) 0| ≤
      (B.card : ℝ) / S.card := by
  classical
  let mapped := S.filter (fun x => f x ∈ A)
  let original := S.filter (fun x => x ∈ originalA)
  have hmappedSubset : mapped ⊆ original ∪ B := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_right original hxB
    · exact Finset.mem_union_left B
        (Finset.mem_filter.mpr
          ⟨hx'.1, (hpreserve x hx'.1 hxB).mp hx'.2⟩)
  have horiginalSubset : original ⊆ mapped ∪ B := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_right mapped hxB
    · exact Finset.mem_union_left B
        (Finset.mem_filter.mpr
          ⟨hx'.1, (hpreserve x hx'.1 hxB).mpr hx'.2⟩)
  have hmappedCard :
      mapped.card ≤ original.card + B.card := by
    exact (Finset.card_le_card hmappedSubset).trans
      (Finset.card_union_le original B)
  have horiginalCard :
      original.card ≤ mapped.card + B.card := by
    exact (Finset.card_le_card horiginalSubset).trans
      (Finset.card_union_le mapped B)
  have habs :
      |(mapped.card : ℝ) - original.card| ≤ B.card := by
    rw [abs_le]
    have hmappedCardReal :
        (mapped.card : ℝ) ≤ original.card + B.card := by
      exact_mod_cast hmappedCard
    have horiginalCardReal :
        (original.card : ℝ) ≤ mapped.card + B.card := by
      exact_mod_cast horiginalCard
    constructor <;> linarith
  have hcardPos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  rw [mappedEmpiricalDistribution_groupMass]
  simp only [empiricalGroupProbability, if_pos hS]
  change
    |(mapped.card : ℝ) / S.card -
        (original.card : ℝ) / S.card| ≤
      (B.card : ℝ) / S.card
  rw [← sub_div, abs_div, abs_of_pos hcardPos]
  exact div_le_div_of_nonneg_right habs hcardPos.le

theorem exactProfileFreshDistribution_coordinate_error_le
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (S : Finset α)
    (hL : L.Infinite) (hS : S.Nonempty)
    (hSL : (↑S : Set α) ⊆ L)
    (hbad : (finiteExactProfilePoints L groups).Finite)
    (i : ℕ) :
    ENNReal.ofReal
        |inducedGroupProbability
              (exactProfileFreshDistribution
                L groups S hL hS)
              groups i -
            empiricalGroupProbability S groups i| ≤
      (hbad.toFinset.card : ENNReal) /
        (S.card : ENNReal) := by
  classical
  let B := hbad.toFinset
  let f := exactProfileFreshRepresentative L groups S hL
  have hpreserve :
      ∀ x, x ∈ S → x ∉ B →
        (f x ∈ groups i ↔ x ∈ groups i) := by
    intro x hxS hxB
    have hxNotBad :
        x ∉ finiteExactProfilePoints L groups := by
      simpa only [B, Set.Finite.mem_toFinset] using hxB
    exact exactProfileFreshRepresentative_preserves_profile
      L groups S hL
      (exactProfileCell_infinite_of_not_mem_finitePoints
        (hSL hxS) hxNotBad) i
  have hreal :=
    mappedEmpirical_groupMass_error_le
      S B hS f (groups i) (groups i) hpreserve
  have hcardPos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  change
    ENNReal.ofReal
        |groupMass
              (DiscreteDistribution.ofPMF
                ((empiricalPointPMF S hS).map f))
              (groups i) -
            empiricalGroupProbability S groups i| ≤
      (B.card : ENNReal) / (S.card : ENNReal)
  calc
    _ ≤ ENNReal.ofReal
        ((B.card : ℝ) / (S.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal (by
        simpa only [f, B] using hreal)
    _ = (B.card : ENNReal) / (S.card : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos hcardPos,
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

theorem exactProfileFreshDistribution_distance_le_badFraction
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (S : Finset α)
    (hL : L.Infinite) (hS : S.Nonempty)
    (hSL : (↑S : Set α) ⊆ L)
    (hbad : (finiteExactProfilePoints L groups).Finite) :
    groupSupDistance
        (exactProfileFreshDistribution L groups S hL hS)
        S groups ≤
      (hbad.toFinset.card : ENNReal) /
        (S.card : ENNReal) := by
  unfold groupSupDistance
  apply iSup_le
  intro i
  exact exactProfileFreshDistribution_coordinate_error_le
    L groups S hL hS hSL hbad i

/-! ## Corrected published Lemma 4.8 -/

/-- Corrected published Lemma 4.8.  Under repaired finite exact-profile support, every
presentation of every UUS target is eventually feasible at every positive
tolerance.

The witness pushes the uniform empirical PMF to unseen target points.  It
preserves every coordinate for observations outside the finite exceptional
set, so its error is at most that set's vanishing empirical fraction. -/
theorem eventually_isAlphaFeasibleAt_of_finiteExactProfileSupport
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (hUUS : GenLimit.Generic.UUS H)
    (hsupport : HasFiniteExactProfileSupport H groups)
    {L : GenLimit.Generic.Language α} (hLH : L ∈ H)
    {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream L)
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ T, ∀ t, T ≤ t →
      IsAlphaFeasibleAt L groups alpha stream t := by
  classical
  let badFinite := hsupport L hLH
  let B := badFinite.toFinset
  let cap : ENNReal := ENNReal.ofReal alpha
  have hcap : cap ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr halpha
  obtain ⟨n, hnpos, hn⟩ :=
    ENNReal.exists_nat_pos_mul_gt hcap
      (show (B.card : ENNReal) ≠ ⊤ by simp)
  have hLInfinite : L.Infinite := hUUS L hLH
  obtain ⟨T, hTcard⟩ :=
    GenLimit.Generic.exists_sample_card_ge_of_presents_infinite
      hP hLInfinite n
  refine ⟨T, ?_⟩
  intro t hTt
  let S := GenLimit.Generic.sample stream t
  have hTsubset : GenLimit.Generic.sample stream T ⊆ S :=
    GenLimit.Generic.sample_mono hTt
  have hnCard : n ≤ S.card :=
    hTcard.trans (Finset.card_le_card hTsubset)
  have hS : S.Nonempty := by
    exact Finset.card_pos.mp (hnpos.trans_le hnCard)
  have hSL : (↑S : Set α) ⊆ L := by
    intro x hx
    exact GenLimit.Generic.mem_language_of_mem_sample_of_presents
      hP hx
  have hScardNeZero : (S.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have hScardNeTop : (S.card : ENNReal) ≠ ⊤ := by
    simp
  have hratio :
      (B.card : ENNReal) / (S.card : ENNReal) <
        cap := by
    apply (ENNReal.div_lt_iff
      (Or.inl hScardNeZero) (Or.inl hScardNeTop)).2
    calc
      (B.card : ENNReal) < (n : ENNReal) * cap := hn
      _ ≤ (S.card : ENNReal) * cap := by
        exact mul_le_mul_right'
          (by exact_mod_cast hnCard) cap
      _ = cap * (S.card : ENNReal) := mul_comm _ _
  refine
    ⟨exactProfileFreshDistribution
        L groups S hLInfinite hS,
      ?_, ?_⟩
  · simpa only [S] using
      exactProfileFreshDistribution_supportedOn
        L groups S hLInfinite hS
  · exact
      (exactProfileFreshDistribution_distance_le_badFraction
        L groups S hLInfinite hS hSL badFinite).trans
        hratio.le

/-- Target-local form of corrected published Lemma 4.8. -/
theorem corrected_lemma_4_8_core
    {L : GenLimit.Generic.Language α}
    {groups : ℕ → Set α}
    {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream L)
    (hL : L.Infinite)
    (hsupport :
      (finiteExactProfilePoints L groups).Finite)
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ T, ∀ t, T ≤ t →
      IsAlphaFeasibleAt L groups alpha stream t := by
  let H : GenLimit.Generic.LanguageClass α := {L}
  have hUUS : GenLimit.Generic.UUS H := by
    intro K hK
    simpa only [H, Set.mem_singleton_iff] using hK ▸ hL
  have hfinite :
      HasFiniteExactProfileSupport H groups := by
    intro K hK
    simpa only [H, Set.mem_singleton_iff] using
      hK ▸ hsupport
  exact
    eventually_isAlphaFeasibleAt_of_finiteExactProfileSupport
      hUUS hfinite (show L ∈ H by simp [H]) hP halpha

/-- Class-facing corrected form of published Lemma 4.8. -/
theorem corrected_lemma_4_8
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (hUUS : GenLimit.Generic.UUS H)
    (hsupport : HasFiniteExactProfileSupport H groups)
    {L : GenLimit.Generic.Language α} (hLH : L ∈ H)
    {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream L)
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ T, ∀ t, T ≤ t →
      IsAlphaFeasibleAt L groups alpha stream t :=
  eventually_isAlphaFeasibleAt_of_finiteExactProfileSupport
    hUUS hsupport hLH hP halpha

/-! ## The critical-and-feasible limit generator -/

/-- Sample form of consistency, used because a generator receives a finite
history rather than an ambient infinite stream. -/
def LanguageConsistentOnSample
    (L : GenLimit.Generic.Language α) (S : Finset α) : Prop :=
  (↑S : Set α) ⊆ L

/-- Sample form of published Definition 4.5. -/
def IsCriticalOnSample
    (family : GenLimit.Generic.LanguageFamily α)
    (S : Finset α) (t n : ℕ) : Prop :=
  n < t ∧
    LanguageConsistentOnSample (family n) S ∧
    ∀ i, i < n →
      LanguageConsistentOnSample (family i) S →
      family n ⊆ family i

/-- Sample form of published Definition 4.7. -/
def IsAlphaFeasibleOnSample
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (S : Finset α) : Prop :=
  ∃ μ : DiscreteDistribution α,
    SupportedOn μ (L \ (↑S : Set α)) ∧
    groupSupDistance μ S groups ≤ ENNReal.ofReal alpha

theorem isCriticalOnSample_sample_iff
    (family : GenLimit.Generic.LanguageFamily α)
    (stream : GenLimit.Generic.Stream α) (t n : ℕ) :
    IsCriticalOnSample family
        (GenLimit.Generic.sample stream t) t n ↔
      IsCriticalAt family stream t n :=
  Iff.rfl

theorem isAlphaFeasibleOnSample_sample_iff
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    IsAlphaFeasibleOnSample L groups alpha
        (GenLimit.Generic.sample stream t) ↔
      IsAlphaFeasibleAt L groups alpha stream t :=
  Iff.rfl

/-- Candidate indices considered by the source's limit generator. -/
noncomputable def alphaFeasibleCriticalIndices
    (family : GenLimit.Generic.LanguageFamily α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (S : Finset α) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter (fun n =>
    IsCriticalOnSample family S t n ∧
      IsAlphaFeasibleOnSample (family n) groups alpha S)

theorem mem_alphaFeasibleCriticalIndices_iff
    {family : GenLimit.Generic.LanguageFamily α}
    {groups : ℕ → Set α} {alpha : ℝ}
    {S : Finset α} {t n : ℕ} :
    n ∈ alphaFeasibleCriticalIndices
        family groups alpha S t ↔
      IsCriticalOnSample family S t n ∧
        IsAlphaFeasibleOnSample
          (family n) groups alpha S := by
  classical
  simp only [alphaFeasibleCriticalIndices,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h.1.1, h⟩

/-- At a finite sample, choose a feasibility witness for the largest
critical feasible hypothesis.  If there is no such hypothesis, use the
exactly representative empirical distribution.  The last branch only
totalizes the empty history. -/
noncomputable def criticalFeasibleSampleDistribution
    [Nonempty α]
    (family : GenLimit.Generic.LanguageFamily α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (S : Finset α) (t : ℕ) :
    DiscreteDistribution α := by
  classical
  let candidates :=
    alphaFeasibleCriticalIndices family groups alpha S t
  if h : candidates.Nonempty then
    let selected := candidates.max' h
    exact Classical.choose
      ((mem_alphaFeasibleCriticalIndices_iff.mp
        (Finset.max'_mem candidates h)).2)
  else if hS : S.Nonempty then
    exact empiricalPointDistribution S hS
  else
    exact DiscreteDistribution.ofPMF
      (PMF.pure (Classical.choice
        (inferInstance : Nonempty α)))

theorem criticalFeasibleSampleDistribution_representative
    [Nonempty α]
    (family : GenLimit.Generic.LanguageFamily α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (S : Finset α) (t : ℕ) (hS : S.Nonempty) :
    groupSupDistance
        (criticalFeasibleSampleDistribution
          family groups alpha S t)
        S groups ≤ ENNReal.ofReal alpha := by
  classical
  let candidates :=
    alphaFeasibleCriticalIndices family groups alpha S t
  by_cases h : candidates.Nonempty
  · let selected := candidates.max' h
    have hselected :
        IsAlphaFeasibleOnSample
          (family selected) groups alpha S :=
      (mem_alphaFeasibleCriticalIndices_iff.mp
        (Finset.max'_mem candidates h)).2
    simp only [criticalFeasibleSampleDistribution,
      candidates, dif_pos h]
    exact (Classical.choose_spec hselected).2
  · simp only [criticalFeasibleSampleDistribution,
      candidates, dif_neg h, dif_pos hS]
    rw [empiricalPointDistribution_distance_zero]
    exact bot_le

/-- The noncomputable information-theoretic generator described after
published Definition 4.7. -/
noncomputable def criticalFeasibleLimitGenerator
    [Nonempty α]
    (family : GenLimit.Generic.LanguageFamily α)
    (groups : ℕ → Set α) (alpha : ℝ) :
    RandomizedGenerator α :=
  fun t xs =>
    criticalFeasibleSampleDistribution
      family groups alpha
      (GenLimit.Generic.sequenceSample xs) t

theorem criticalFeasibleLimitGenerator_representative
    [Nonempty α]
    (family : GenLimit.Generic.LanguageFamily α)
    (groups : ℕ → Set α) (alpha : ℝ) :
    IsAlphaRepresentative
      (criticalFeasibleLimitGenerator family groups alpha)
      groups alpha := by
  intro stream t ht
  have hS :
      (GenLimit.Generic.sample stream t).Nonempty :=
    ⟨stream 0, GenLimit.Generic.value_mem_sample ht⟩
  simpa only [distributionAt, criticalFeasibleLimitGenerator,
    GenLimit.Generic.sequenceSample_prefix] using
      criticalFeasibleSampleDistribution_representative
        family groups alpha
        (GenLimit.Generic.sample stream t) t hS

theorem criticalFeasibleLimitGenerator_consistent_of_target_candidate
    [Nonempty α]
    (family : GenLimit.Generic.LanguageFamily α)
    (groups : ℕ → Set α) (alpha : ℝ)
    {stream : GenLimit.Generic.Stream α} {t z : ℕ}
    (hzCritical : IsCriticalAt family stream t z)
    (hzFeasible :
      IsAlphaFeasibleAt
        (family z) groups alpha stream t) :
    IsConsistentAt
      (criticalFeasibleLimitGenerator family groups alpha)
      (family z) stream t := by
  classical
  let S := GenLimit.Generic.sample stream t
  let candidates :=
    alphaFeasibleCriticalIndices family groups alpha S t
  have hzMem : z ∈ candidates := by
    apply mem_alphaFeasibleCriticalIndices_iff.mpr
    exact
      ⟨(isCriticalOnSample_sample_iff
          family stream t z).mpr hzCritical,
        (isAlphaFeasibleOnSample_sample_iff
          (family z) groups alpha stream t).mpr hzFeasible⟩
  have hcandidates : candidates.Nonempty := ⟨z, hzMem⟩
  let selected := candidates.max' hcandidates
  have hselectedMem : selected ∈ candidates :=
    Finset.max'_mem candidates hcandidates
  have hselected :=
    mem_alphaFeasibleCriticalIndices_iff.mp hselectedMem
  have hzSelected : z ≤ selected :=
    Finset.le_max' candidates z hzMem
  have hselectedCritical :
      IsCriticalAt family stream t selected :=
    (isCriticalOnSample_sample_iff
      family stream t selected).mp hselected.1
  have hselectedSubset :
      family selected ⊆ family z :=
    critical_subset_of_le
      hzSelected hzCritical hselectedCritical
  have houtput :
      distributionAt
          (criticalFeasibleLimitGenerator family groups alpha)
          stream t =
        Classical.choose hselected.2 := by
    simp only [distributionAt, criticalFeasibleLimitGenerator,
      GenLimit.Generic.sequenceSample_prefix,
      criticalFeasibleSampleDistribution, S, candidates,
      dif_pos hcandidates, selected]
  apply isConsistentAt_iff_supportedOn.mpr
  rw [houtput]
  intro x hx
  have hxSelected :=
    (Classical.choose_spec hselected.2).1 x hx
  exact ⟨hselectedSubset hxSelected.1, hxSelected.2⟩

theorem criticalFeasibleLimitGenerator_succeeds
    [Nonempty α]
    (family : GenLimit.Generic.LanguageFamily α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (hUUS :
      GenLimit.Generic.UUS (Set.range family))
    (hsupport :
      HasFiniteExactProfileSupport
        (Set.range family) groups)
    {z : ℕ} {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream (family z))
    (halpha : 0 < alpha) :
    ∃ T, IsConsistentFrom
      (criticalFeasibleLimitGenerator family groups alpha)
      (family z) stream T := by
  obtain ⟨Tcritical, hcritical⟩ :=
    target_eventually_critical hP
  obtain ⟨Tfeasible, hfeasible⟩ :=
    eventually_isAlphaFeasibleAt_of_finiteExactProfileSupport
      hUUS hsupport (show family z ∈ Set.range family from
        ⟨z, rfl⟩) hP halpha
  refine ⟨max Tcritical Tfeasible, ?_⟩
  intro t ht
  apply criticalFeasibleLimitGenerator_consistent_of_target_candidate
  · exact hcritical t
      ((Nat.le_max_left Tcritical Tfeasible).trans ht)
  · exact hfeasible t
      ((Nat.le_max_right Tcritical Tfeasible).trans ht)

/-! ## Corrected published Theorem 4.4 -/

/-- Corrected published Theorem 4.4 for an explicitly enumerated class.  This is
stronger than the source-facing statement: neither the group-cover axiom nor
countability of the example type is used by the information-theoretic
argument once the class is supplied as a sequence. -/
theorem corrected_theorem_4_4_indexed
    (family : GenLimit.Generic.LanguageFamily α)
    (groups : ℕ → Set α)
    (hUUS :
      GenLimit.Generic.UUS (Set.range family))
    (hsupport :
      HasFiniteExactProfileSupport
        (Set.range family) groups) :
    RepresentativelyGeneratableInLimit
      (Set.range family) groups := by
  classical
  have hnonempty : (family 0).Nonempty :=
    (hUUS (family 0) ⟨0, rfl⟩).nonempty
  letI : Nonempty α := ⟨Classical.choose hnonempty⟩
  intro alpha halpha
  refine
    ⟨criticalFeasibleLimitGenerator family groups alpha,
      criticalFeasibleLimitGenerator_representative
        family groups alpha,
      ?_⟩
  intro L hL stream hP
  obtain ⟨z, rfl⟩ := hL
  exact criticalFeasibleLimitGenerator_succeeds
    family groups alpha hUUS hsupport hP halpha

/-- The empirical distribution, totalized by a point mass on the empty
sample. -/
noncomputable def empiricalSampleDistribution
    [Nonempty α] (S : Finset α) :
    DiscreteDistribution α := by
  classical
  if hS : S.Nonempty then
    exact empiricalPointDistribution S hS
  else
    exact DiscreteDistribution.ofPMF
      (PMF.pure (Classical.choice
        (inferInstance : Nonempty α)))

theorem empiricalSampleDistribution_distance_zero
    [Nonempty α] (S : Finset α) (hS : S.Nonempty)
    (groups : ℕ → Set α) :
    groupSupDistance
        (empiricalSampleDistribution S) S groups = 0 := by
  classical
  simp only [empiricalSampleDistribution, dif_pos hS]
  exact empiricalPointDistribution_distance_zero S hS groups

/-- A globally representative fallback generator, used to cover the empty
language-class edge case in the countable wrapper. -/
noncomputable def empiricalLimitGenerator
    [Nonempty α] : RandomizedGenerator α :=
  fun _t xs =>
    empiricalSampleDistribution
      (GenLimit.Generic.sequenceSample xs)

theorem empiricalLimitGenerator_representative
    [Nonempty α] (groups : ℕ → Set α) (alpha : ℝ) :
    IsAlphaRepresentative
      (empiricalLimitGenerator : RandomizedGenerator α)
      groups alpha := by
  intro stream t ht
  have hS :
      (GenLimit.Generic.sample stream t).Nonempty :=
    ⟨stream 0, GenLimit.Generic.value_mem_sample ht⟩
  rw [show
      groupSupDistance
          (distributionAt
            (empiricalLimitGenerator : RandomizedGenerator α)
            stream t)
          (GenLimit.Generic.sample stream t) groups = 0 by
    simpa only [distributionAt, empiricalLimitGenerator,
      GenLimit.Generic.sequenceSample_prefix] using
        empiricalSampleDistribution_distance_zero
          (GenLimit.Generic.sample stream t) hS groups]
  exact bot_le

/-- Corrected published Theorem 4.4 for an arbitrary countable class. -/
theorem corrected_theorem_4_4_of_countable
    [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α)
    (hHcountable : H.Countable)
    (hUUS : GenLimit.Generic.UUS H)
    (hsupport : HasFiniteExactProfileSupport H groups) :
    RepresentativelyGeneratableInLimit H groups := by
  classical
  by_cases hH : H.Nonempty
  · let enumeration : ℕ → H :=
      Classical.choose (hHcountable.exists_surjective hH)
    have henumeration : Function.Surjective enumeration :=
      Classical.choose_spec
        (hHcountable.exists_surjective hH)
    let family : GenLimit.Generic.LanguageFamily α :=
      fun n => (enumeration n : Set α)
    have hrange : Set.range family = H := by
      apply Set.Subset.antisymm
      · rintro L ⟨n, rfl⟩
        exact (enumeration n).property
      · intro L hLH
        obtain ⟨n, hn⟩ :=
          henumeration ⟨L, hLH⟩
        exact ⟨n, congrArg Subtype.val hn⟩
    rw [← hrange] at hUUS hsupport ⊢
    exact corrected_theorem_4_4_indexed
      family groups hUUS hsupport
  · have hempty : H = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hH
    rw [hempty]
    intro alpha _halpha
    refine
      ⟨(empiricalLimitGenerator : RandomizedGenerator α),
        empiricalLimitGenerator_representative groups alpha,
        ?_⟩
    intro L hL
    exact (Set.notMem_empty L hL).elim

/-- Published-facing corrected Theorem 4.4.  The countability of the example
space and the group-cover premise are retained from the paper's ambient
assumptions; the stronger theorem above shows that the repaired proof does
not use them. -/
theorem corrected_theorem_4_4
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α)
    (hHcountable : H.Countable)
    (hUUS : GenLimit.Generic.UUS H)
    (_hcover : GroupsCover groups)
    (hsupport : HasFiniteExactProfileSupport H groups) :
    RepresentativelyGeneratableInLimit H groups :=
  corrected_theorem_4_4_of_countable
    H groups hHcountable hUUS hsupport

end GenLimit.RepresentativeGeneration
