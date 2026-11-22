import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Results.Supporting
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.SetDrivenObstruction
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.ReplayCounterexample

/-!
# Paper 07: main-results overview

Section 2 contains Theorems 2.1 and 2.3–2.6 and Corollary 2.2. The detailed
statements below include the truth-index minimax theorem and both explicit
element-density constants. The element-density guarantees use finite chronological
histories including the current input. The independent density proof uses patient scope.
Theorems 2.3, 2.4, 4.1 and 4.9 use the unordered sample of Section 2.1. The final
section gives counterexamples for accuracy and element density with this input.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.Results

open Filter

private theorem selector_valid_and_frequently_accurate {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    IndexValidInLimit C stream z ∧ ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r := by
  obtain ⟨j,hj,he⟩ := exists_first_occurrence C z
  simpa only [IndexValidInLimit,AccurateAt,he] using
    (GenLimit.KleinbergWei.DensityMeasures.theorem_2_1 (z := j) (he.symm ▸ hP) hj)

/-- Theorem 2.1. For each family `C`, the rule `indexHistoryRule C` uses the
finite ordered history. On every exact presentation its guesses are eventually
sublanguages of the target and equal the target at arbitrarily late rounds.
`index_set_counterexample` gives a counterexample when the rule receives only
the unordered set of observed words, as in Section 2.1. -/
theorem theorem_2_1 (C : LanguageFamily) :
    ∃ A : List ℕ → ℕ, ValidIndexRule C A ∧
      ∀ z s, Presents s (C z) → ∀ t, ∃ r ≥ t, C (A (textPrefix s r)) = C z := by
  refine ⟨indexHistoryRule C,fun z s hs ↦ ?_,fun z s hs t ↦ ?_⟩
  · obtain ⟨T,hT⟩ := (selector_valid_and_frequently_accurate hs).1
    exact eventually_atTop.mpr ⟨T,fun t ht ↦ by simpa only [indexHistoryRule_prefix] using hT t ht⟩
  · simpa only [indexHistoryRule_prefix,AccurateAt] using (selector_valid_and_frequently_accurate hs).2 t

/-- Corollary 2.2. With finite ordered histories, the upper densities of the
guessed languages have limsup one. -/
theorem corollary_2_2 {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (ordering : OrderedLanguage) (hcarrier : ordering.carrier = C z)
    (hP : Presents stream (C z)) :
    IndexValidInLimit C stream z ∧ indexUpperDensityLimsup C stream ordering = 1 := by
  obtain ⟨hv,ha⟩ := selector_valid_and_frequently_accurate hP
  exact ⟨hv,indexUpperDensityLimsup_eq_one_of_frequently_accurate ordering hcarrier ha⟩

/-- Theorem 2.3. For rules on the unordered sample, one countable family has
a target of zero worst-case index breadth. The finite-history version is
`GenLimit.KleinbergWei.DensityMeasures.theorem_2_3` in `VanishingBreadth.lean`. -/
theorem theorem_2_3 :
    ∃ (C : LanguageFamily) (z : ℕ) (O : OrderedLanguage), (∀ i, (C i).Infinite) ∧
      O.carrier = C z ∧ SetDriven.Vanishing C z O :=
  SetDriven.exists_vanishing

/-- Theorems 2.4 and 4.1. Vanishing breadth for rules on the unordered sample
is equivalent to perfect towers of arbitrarily small upper density. The finite-history
version is `GenLimit.KleinbergWei.DensityMeasures.theorem_4_1` in `VanishingBreadth.lean`. -/
theorem theorem_2_4 (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (z : ℕ) (O : OrderedLanguage) (hc : O.carrier = C z) :
    SetDriven.Vanishing C z O ↔ ∀ ε : ℝ, 0 < ε →
      HasPerfectTowerBound (Set.range C) ⟨C z,z,rfl⟩ O ε :=
  SetDriven.vanishing_iff C hi z O hc

open OrderedFocus in
/-- Theorem 2.5. For every constant below one half, a single finite-history
rule works for every target and every presentation in the ordered collection. -/
theorem theorem_2_5 (c : ℝ) (hc : c < 1/2)
    (O : ℕ → OrderedLanguage) (compat : Compatible O) :
    ∃ A : List ℕ → ℕ, ∀ z s, Presents s (O z).carrier →
      ElementValid s (play A s) (O z).carrier ∧
        c ≤ (O z).upperDensity (generatedIn A s (O z).carrier) := by
  refine ⟨historyRule O,fun _ _ hs ↦ ?_⟩
  obtain ⟨valid,hd⟩ := historyRule_upper O compat hs
  exact ⟨valid,hc.le.trans hd⟩

open OrderedFocus in
/-- Theorem 2.6. With finite ordered histories, the positive lower-density
constant is absolute across language collections. -/
theorem theorem_2_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ O : ℕ → OrderedLanguage, Compatible O →
      ∃ A : List ℕ → ℕ, ∀ z s, Presents s (O z).carrier →
        ElementValid s (play A s) (O z).carrier ∧
          c ≤ (O z).lowerDensity (generatedIn A s (O z).carrier) := by
  refine ⟨1/8, by norm_num, fun O compat ↦ ⟨historyRule O, fun _ _ hs ↦ ?_⟩⟩
  simpa only [generatedIn, play_historyRule, OrderedLanguage.lowerDensity_inter_carrier]
    using OrderedFocus.theorem_6_12 O compat hs

/-- Detailed Theorem 3.1. The selector on finite ordered histories works for
any index naming the target, including duplicates. -/
theorem theorem_3_1 {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    IndexValidInLimit C stream z ∧ ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r :=
  selector_valid_and_frequently_accurate hP

/-- Detailed Theorem 4.1 gives the set-driven characterization in Theorem 2.4. -/
theorem theorem_4_1 (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (z : ℕ) (O : OrderedLanguage) (hc : O.carrier = C z) :
    SetDriven.Vanishing C z O ↔ ∀ ε : ℝ, 0 < ε →
      HasPerfectTowerBound (Set.range C) ⟨C z,z,rfl⟩ O ε :=
  theorem_2_4 C hi z O hc

open SetDriven in
/-- Theorem 4.9. A rule on the unordered sample attains the truth index, and each
valid competing set-driven rule admits a presentation of breadth at most that index. The
finite-history version is `GenLimit.KleinbergWei.DensityMeasures.theorem_4_9`
in `VanishingBreadth.lean`. -/
theorem theorem_4_9 (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (z : ℕ) (O : OrderedLanguage) (hc : O.carrier = C z) :
    ∃ τ, IsTruthIndex (Set.range C) ⟨C z,z,rfl⟩ O τ ∧
      (∀ A, ValidIndex C A → ∃ s, Presents s (C z) ∧ indexBreadth C O (asHistory A) s ≤ τ) ∧
      ValidIndex C (selector C) ∧
      ∀ s, Presents s (C z) → τ ≤ indexBreadth C O (asHistory (selector C)) s :=
  minimax C hi z O hc

open OrderedFocus in
/-- Detailed Theorem 5.1. One finite-history rule simultaneously attains
the bound `c / 2` for every `c < 1`. -/
theorem theorem_5_1 (O : ℕ → OrderedLanguage) (compat : Compatible O) :
    ∃ A : List ℕ → ℕ, ∀ z s, Presents s (O z).carrier →
      ElementValid s (play A s) (O z).carrier ∧ ∀ c : ℝ, c < 1 →
        c / 2 ≤ (O z).upperDensity (generatedIn A s (O z).carrier) := by
  refine ⟨historyRule O, fun _ _ hs ↦ ?_⟩
  obtain ⟨valid, hd⟩ := historyRule_upper O compat hs
  exact ⟨valid, fun c hc ↦ (show c / 2 ≤ 1 / 2 by linarith).trans hd⟩

/-- Claim 6.1. The limit points are exactly the terminals of infinite perfect towers. -/
theorem claim_6_1 {X : Set Language} {K : TowerTopology.Point X}
    (s : ℕ → ℕ) (hs : Presents s K.val) :
    TowerTopology.IsLimitPoint K ↔ ∃ tower : ℕ → TowerTopology.Point X, PerfectTower X tower K :=
  GenLimit.KleinbergWei.DensityMeasures.claim_6_1 s hs

open OrderedFocus in
/-- Detailed Theorem 6.2. One finite-history rule attains the finite-rank bound at every
eligible rank. Its stronger uniform half-density estimate implies this bound. -/
theorem theorem_6_2 (O : ℕ → OrderedLanguage) (compat : Compatible O) :
    ∃ A : List ℕ → ℕ, ∀ r : ℕ, 0 < r →
      TowerTopology.FiniteRankAtMost (Set.range fun i ↦ (O i).carrier) r →
      ∀ z s, Presents s (O z).carrier →
        ElementValid s (play A s) (O z).carrier ∧
          1 / (3 * ((r : ℝ) + 1)) ≤ (O z).lowerDensity (generatedIn A s (O z).carrier) := by
  refine ⟨historyRule O,fun r _ _ _ _ hs ↦ ?_⟩
  obtain ⟨valid,hd⟩ := historyRule_density O compat hs
  have h : (2 : ℝ) ≤ 3 * ((r : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) r]
  exact ⟨valid,(one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h).trans hd⟩

open FiniteRankParent FiniteRankFallback TowerTopology in
/-- Counterexample to the bad-run assertion in Claim 6.11 on texts admitting repetitions. -/
theorem claim_6_11_counterexample :
    ∃ (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
      (hr : FiniteRankAtMost (FamilySpace C) 1) (s : ℕ → ℕ) (O : OrderedLanguage),
      O.carrier = C 0 ∧ Presents s (C 0) ∧
      ¬ EventuallyNoBadRun 1 O (badInputs O s (canonicalRunOutput hi s 1 hr)) :=
  ReplayCounterexample.not_claim_6_11_on_repeated_presentations

open OrderedFocus in
/-- P07 Theorem 6.12. One finite-history rule guarantees validity and lower density
at least one eighth on every target. The witness adapts P39's patient-scope
generator, whose one-half lower bound transfers via `historyRule_density`. -/
theorem theorem_6_12 (O : ℕ → OrderedLanguage) (compat : Compatible O) :
    ∃ A : List ℕ → ℕ, ∀ z s, Presents s (O z).carrier →
      ElementValid s (play A s) (O z).carrier ∧
        (1/8 : ℝ) ≤ (O z).lowerDensity (generatedIn A s (O z).carrier) := by
  refine ⟨historyRule O,fun _ _ hs ↦ ?_⟩
  obtain ⟨valid,hd⟩ := historyRule_density O compat hs
  exact ⟨valid,(by norm_num : (1/8 : ℝ) ≤ 1/2).trans hd⟩

/-! ## Counterexamples for the unordered sample in Section 2.1 -/

open SetDriven in
/-- Counterexample to the set-only readings of Theorem 2.1 and Corollary 2.2.
The adversary needs no repetitions. Eventually every guess misses the target,
and the limsup of the relative upper densities is zero. -/
theorem index_set_counterexample :
    ∃ (C : LanguageFamily) (z : ℕ) (O : OrderedLanguage), (∀ i, (C i).Infinite) ∧
      O.carrier = C z ∧ ∀ A : Finset ℕ → ℕ, ValidIndexOnInjective C A →
        ∃ s, Function.Injective s ∧ Presents s (C z) ∧
          (∀ᶠ t in atTop, C (output A s t) ≠ C z) ∧
          limsup (fun t ↦ O.upperDensity (C (output A s t))) atTop = 0 := by
  refine ⟨SquareTower.sparseFamily,0,SquareTower.natOrder,fun i ↦ ?_,rfl,index_counterexample⟩
  rw [← orders_carrier i,← (orders i).range_enumeration]
  exact Set.infinite_range_of_injective (orders i).enumeration_injective

open SetDriven in
/-- Counterexample to the set-only readings of Theorems 2.5, 2.6, 5.1, 6.2
and 6.12. The ordered family has rank at most two. Every set-only generator
valid on injective texts has an injective text of upper and lower density zero. -/
theorem element_set_counterexample :
    ∃ (O : ℕ → OrderedLanguage) (z : ℕ), OrderedFocus.Compatible O ∧
      TowerTopology.FiniteRankAtMost (Set.range fun i ↦ (O i).carrier) 2 ∧
      ∀ A : Finset ℕ → ℕ, ValidElementOnInjective (fun i ↦ (O i).carrier) A →
        ∃ s, Function.Injective s ∧ Presents s (O z).carrier ∧
          (O z).upperDensity (Set.range (output A s)) = 0 ∧
          (O z).lowerDensity (Set.range (output A s)) = 0 := by
  have family : (fun i ↦ (orders i).carrier) = SquareTower.sparseFamily := funext orders_carrier
  refine ⟨orders,0,orders_compatible,?_,?_⟩
  · rw [family]
    exact rank_two
  · intro A hv
    rw [family] at hv
    exact element_counterexample A hv

end GenLimit.KleinbergWei.DensityMeasures.Results
