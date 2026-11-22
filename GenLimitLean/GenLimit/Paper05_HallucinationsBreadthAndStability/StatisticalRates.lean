import GenLimit.Paper05_HallucinationsBreadthAndStability.WeakSampling
import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalBreadth
import GenLimit.Paper03_HallucinationAndModeCollapse.ApproximateBreadthModel

/-! # Universal statistical rates for breadth (Theorems 5.2 and 5.3) -/

namespace GenLimit.BreadthCharacterizations

open GenLimit.HallucinationModeCollapse GenLimit.DiscreteIID GenLimit.Support Filter

/-- Equation (3) tests the full support produced after IID training. In the
lower bound the hard distribution stays fixed along the infinite subsequence. -/
theorem theorem_5_2 (O : OracleFamily) :
    (NontrivialCollection O.language → ∀ G : StatisticalGenerator,
      ∃ i p, ValidDistribution O.language i p ∧ ∃ᶠ n : ℕ in atTop,
        Real.exp (-2 * (n : ℝ)) ≤ breadthError O.language G p i n) ∧
    (IdentifiableInLimit O.language → ∃ G, ExponentialBreadth O.language G) ∧
    (¬IdentifiableInLimit O.language → ∀ G, NoBreadthRate O.language G) := by
  classical
  refine ⟨?_, ?_, noBreadthRate_of_not_identifiable O.language (familyMembership O)⟩
  · intro h G
    let Q := fun (xs : List ℕ) (x : ℕ) => decide (x ∈ (G xs).support)
    have hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support := by simp [Q]
    obtain ⟨i,p,hp,hf⟩ := lemma_5_1 _ h (deterministicIdentifier (breadthIdentifier (familyMembership O) Q))
    exact ⟨i,p,hp,(hf.and_eventually (identificationError_le_breadthError_eventually
      (familyMembership O) G Q hQ i p hp)).mono (fun _ h => h.1.trans h.2)⟩
  · intro h
    obtain ⟨emit,he,_⟩ := certifiedBreadth_of_identifiable O h
    exact ⟨_,oracle_identifiedBreadth_exponential O emit he⟩

private theorem approximate_lower (O : OracleFamily) (h : GenerationNontrivial O.language)
    (G : StatisticalGenerator) :
    ∃ i p, ValidDistribution O.language i p ∧ ∃ᶠ n : ℕ in atTop,
      Real.exp (-2 * (n : ℝ)) ≤ approximateBreadthError O.language G p i n := by
  classical
  obtain ⟨I,hI,⟨x,hx⟩,hfinite⟩ := h
  let fails := fun i n => ¬ApproximateBreadthAt (G (List.replicate n x)).support (O.language i)
  have hf : ∃ᶠ n : ℕ in atTop, ∃ i ∈ I, fails i n := by
    apply Frequently.of_forall
    intro n
    by_contra! hn
    let U := (G (List.replicate n x)).support
    have hall (i) (hi : i ∈ I) : ApproximateBreadthAt U (O.language i) := not_not.mp (hn i hi)
    have hu : U.Finite := hfinite.subset (fun y hy i hi => (hall i hi).1 hy)
    obtain ⟨i,hi⟩ := hI
    apply O.infinite' i
    apply (hu.union (hall i hi).2).subset
    intro y hy
    by_cases hmem : y ∈ U
    · exact Or.inl hmem
    · exact Or.inr ⟨hy,hmem⟩
  obtain ⟨i,hi,hiF⟩ := finite_frequently_choice I fails hf
  obtain ⟨p,hp,hat⟩ := exists_fullSupport_heavyAtom (O.language i) x (hx i hi)
  refine ⟨i,p,hp,(hiF.and_eventually (eventually_ge_atTop 1)).mono ?_⟩
  rintro n ⟨herr,hn⟩
  have hs : {List.replicate n x} ⊆ {xs | ¬ApproximateBreadthAt (G xs).support (O.language i)} :=
    Set.singleton_subset_iff.mpr herr
  calc
    _ ≤ (1 / 2 : ℝ) ^ (n+1) := exp_neg_two_le_half_pow n hn
    _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ (p x).toReal ^ n := pow_le_pow_left₀ (by norm_num) hat n
    _ = probability (samples p n) {List.replicate n x} := by
      simp [probability, PMF.toOuterMeasure_apply_singleton, samples_replicate]
    _ ≤ _ := probability_mono _ hs

private theorem weakLaw_exponential (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (he : ∀ i, CharikarPabbaraju.IsEnumeratedWeakTellTale O.language i (Angluin.enumeratedSet emit i)) :
    AchievesScaledApproximateBreadthRate O.language (weakLaw O emit) (fun r => Real.exp (-r)) := by
  intro i p hp
  obtain ⟨W,hW,N,hgood⟩ := weakLaw_finiteWitness O emit he i
  obtain ⟨c,hc,hmiss⟩ := finite_missing_exponential p W (fun x hx => by
    change x ∈ p.support
    rw [hp]
    exact hW hx)
  let D := ((W.card : ℝ)+1) * Real.exp (c*N)
  have hcard : (W.card : ℝ)+1 ≥ 1 := by linarith [Nat.cast_nonneg (α := ℝ) W.card]
  have hbig : (W.card : ℝ) ≤ D := by
    have he : 1 ≤ Real.exp (c*N) := Real.one_le_exp (by positivity)
    dsimp [D]
    nlinarith
  refine ⟨c,hc,D,by dsimp [D]; positivity,fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hm : approximateBreadthError O.language (weakLaw O emit) p i n ≤
        probability (samples p n) {xs | ¬∀ x ∈ W, x ∈ xs} := by
      rw [approximateBreadthError, ← probability_inter_support]
      apply probability_mono
      rintro xs ⟨hfail, hs⟩ hw
      obtain ⟨hl,hxs⟩ := (samples_support p n xs).mp hs
      exact hfail (hgood xs (hl.symm ▸ hn) (fun x hx => hp ▸ hxs x hx) hw)
    exact hm.trans ((hmiss n).trans (by rw [neg_mul]; exact mul_le_mul_of_nonneg_right hbig (Real.exp_nonneg _)))
  · apply (approximateBreadthError_le_one _ _ _ _ _).trans
    have hcast : (n : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    have hpos : 0 ≤ c * (N : ℝ) - c * n := by nlinarith
    have hex := Real.one_le_exp hpos
    dsimp [D]
    rw [mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]
    nlinarith

/-- The final clause of the pinned Theorem 5.3 explicitly names exact
breadth. Each clause retains its own hypotheses on the language family. -/
theorem theorem_5_3 (O : OracleFamily) :
    (GenerationNontrivial O.language → ∀ G : StatisticalGenerator,
      ∃ i p, ValidDistribution O.language i p ∧ ∃ᶠ n : ℕ in atTop,
        Real.exp (-2 * (n : ℝ)) ≤ approximateBreadthError O.language G p i n) ∧
    (WeakAngluinCondition O.language → ∃ G, AchievesScaledApproximateBreadthRate O.language G
      (fun r => Real.exp (-r))) ∧
    (¬WeakAngluinCondition O.language → ∀ G, NoBreadthRate O.language G) := by
  refine ⟨approximate_lower O,?_,?_⟩
  · intro hw
    obtain ⟨emit,he⟩ := weakEnumeration_of_condition hw
    exact ⟨_,weakLaw_exponential O emit he⟩
  · intro h
    apply (theorem_5_2 O).2.2
    intro hID
    apply h
    intro i
    obtain ⟨T,hT⟩ := (Angluin.semanticallyInferrable_iff_conditionTwo O.language).mp hID i
    exact ⟨T,hT.1,fun j hj hlt => (hlt.2 (hT.2 j hj hlt.1)).elim⟩

end GenLimit.BreadthCharacterizations
