import GenLimit.Paper05_HallucinationsBreadthAndStability.WeakSampling
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.DifferenceOracle
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.BreadthClaim52

/-! # The exhaustive clauses of Theorems 4.3 and 4.5 -/

namespace GenLimit.BreadthCharacterizations

/-- Definition 4.2 uses an ordered enumeration in generate-only mode and
counts its first member as the ordinary output at an earlier round. -/
abbrev Enumerator (α : Type*) := List α → ℕ → α

def EnumeratesExhaustively (A : Enumerator α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ i s, Generic.Presents s (F i) → ∃ T, ∀ t ≥ T,
    let R := Set.range (A (textPrefix s t))
    (R \ F i).Finite ∧ F i ⊆ (↑(Generic.sample s t) : Set α) ∪
      {x | ∃ j < t, A (textPrefix s j) 0 = x} ∪ R

def enumeratorSupport (A : Enumerator α) : SupportAlgorithm α := fun xs => Set.range (A xs)

private def tupleEnumerator (A : Enumerator α) : CharikarPabbaraju.ExhaustiveAlgorithm α :=
  fun _ xs => A (List.ofFn xs)

private theorem tupleEnumerator_inverse (A : CharikarPabbaraju.ExhaustiveAlgorithm α) :
    tupleEnumerator (learnerOfFiniteHistory A) = A := by
  funext t xs
  exact learnerOfFiniteHistory_ofFn A xs

private theorem exhaustive_iff_tuple (F : Generic.LanguageFamily α) (A : Enumerator α) :
    EnumeratesExhaustively A F ↔ CharikarPabbaraju.IsExhaustiveGenerator (tupleEnumerator A) (Set.range F) := by
  have he (K : Set α) (s : ℕ → α) (t : ℕ) :
      CharikarPabbaraju.ExhaustiveCorrectAt (tupleEnumerator A) K s t ↔
        (Set.range (A (textPrefix s t)) \ K).Finite ∧ K ⊆ (↑(Generic.sample s t) : Set α) ∪
        {x | ∃ j < t, A (textPrefix s j) 0 = x} ∪ Set.range (A (textPrefix s t)) := by
    simp only [CharikarPabbaraju.ExhaustiveCorrectAt, CharikarPabbaraju.generateOnly,
      CharikarPabbaraju.generatedBefore, CharikarPabbaraju.exhaustiveOutput,
      CharikarPabbaraju.generatorAt, tupleEnumerator, textPrefix_eq_ofFn]
  constructor
  · rintro h _ ⟨i,rfl⟩ s hp
    obtain ⟨T,hT⟩ := h i s hp
    exact ⟨T, fun t ht => (he _ _ _).mpr (hT t ht)⟩
  · intro h i s hp
    obtain ⟨T,hT⟩ := h _ (Set.mem_range_self i) s hp
    exact ⟨T, fun t ht => (he _ _ _).mp (hT t ht)⟩

private theorem rangeWeak_iff (F : Generic.LanguageFamily α) :
    CharikarPabbaraju.WeakAngluinExistence (Set.range F) ↔ WeakAngluinCondition F := by
  constructor
  · intro h i
    obtain ⟨T, hT, hw⟩ := h _ (Set.mem_range_self i)
    exact ⟨T, hT, fun j => hw _ (Set.mem_range_self j)⟩
  · rintro h _ ⟨i,rfl⟩
    obtain ⟨T, hT, hw⟩ := h i
    exact ⟨T, hT, fun _ ⟨j,e⟩ => e ▸ hw j⟩

/-- Theorem 4.3, exhaustive generation under the updated Definition 4.2. -/
theorem theorem_4_3_exhaustive [Countable α] (F : Generic.LanguageFamily α)
    (hinf : ∀ i, (F i).Infinite) :
    (∃ A, EnumeratesExhaustively A F) ↔ WeakAngluinCondition F := by
  rw [← rangeWeak_iff, ← CharikarPabbaraju.theorem4_exhaustive_generation_characterization F hinf]
  constructor
  · rintro ⟨A,hA⟩
    exact ⟨_, (exhaustive_iff_tuple F A).mp hA⟩
  · rintro ⟨A,hA⟩
    refine ⟨learnerOfFiniteHistory A, (exhaustive_iff_tuple _ _).mpr ?_⟩
    simpa only [tupleEnumerator_inverse] using hA

/-- A finite-difference oracle and finite membership queries implement the
exhaustive sufficiency direction on encoded words. -/
theorem theorem_4_3_exhaustive_oracles (O : OracleFamily)
    (D : CharikarPabbaraju.DifferenceOracle.Oracle O.language) (hw : WeakAngluinCondition O.language) :
    EnumeratesExhaustively (learnerOfFiniteHistory (CharikarPabbaraju.DifferenceOracle.algorithm O D)) O.language := by
  apply (exhaustive_iff_tuple _ _).mpr
  have h := CharikarPabbaraju.DifferenceOracle.proposition6_2 O D ((rangeWeak_iff _).mpr hw)
  simpa only [tupleEnumerator_inverse] using h

/-- Lemma 7.7 realizes Definition 4.2 with only membership queries and
weak tell-tale enumeration. The numerical search is total on every input. -/
theorem lemma_7_7 (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (he : ∀ i, CharikarPabbaraju.IsEnumeratedWeakTellTale O.language i (Angluin.enumeratedSet emit i)) :
    let B := CharikarPabbaraju.membershipExhaustiveAlgorithm O (Angluin.stageContents emit)
    EnumeratesExhaustively (learnerOfFiniteHistory B) O.language ∧
    (∀ t xs k, B t xs k ∈ CharikarPabbaraju.exhaustiveSearch O emit (List.ofFn xs,k)) ∧
    (Computable₂ O.query → Computable₂ emit → Computable (fun p : List ℕ × ℕ => B p.1.length p.1.get p.2)) := by
  refine ⟨?_,CharikarPabbaraju.exhaustiveSearch_realizes O emit,
    fun ho hem => CharikarPabbaraju.membershipExhaustive_computable O ho emit hem⟩
  apply (exhaustive_iff_tuple _ _).mpr
  simpa only [tupleEnumerator_inverse] using CharikarPabbaraju.proposition6_3_of_weakTellTaleApproximation O _
    (CharikarPabbaraju.weakTellTaleApproximation_of_enumeration he)

theorem theorem_4_3_exhaustive_tellOracle (O : OracleFamily) (hw : WeakAngluinCondition O.language) :
    ∃ emit, (∀ i, CharikarPabbaraju.IsEnumeratedWeakTellTale O.language i (Angluin.enumeratedSet emit i)) ∧
      let B := CharikarPabbaraju.membershipExhaustiveAlgorithm O (Angluin.stageContents emit)
      EnumeratesExhaustively (learnerOfFiniteHistory B) O.language ∧
      (∀ t xs k, B t xs k ∈ CharikarPabbaraju.exhaustiveSearch O emit (List.ofFn xs,k)) ∧
      (Computable₂ O.query → Computable₂ emit → Computable (fun p : List ℕ × ℕ => B p.1.length p.1.get p.2)) := by
  obtain ⟨emit,he⟩ := weakEnumeration_of_condition hw
  exact ⟨emit,he,lemma_7_7 O emit he⟩

/-- For the literal finite-hallucination convention the membership and
weak tell-tale learner actually stabilizes. Its eventual language contains
the target and adds at most finitely many words. -/
theorem stable_exhaustive_iff_weak (O : OracleFamily) :
    (∃ B, IsStableGenerator (enumeratorSupport B) O.language ∧ EnumeratesExhaustively B O.language) ↔
      WeakAngluinCondition O.language := by
  classical
  refine ⟨fun ⟨B,_,h⟩ => (theorem_4_3_exhaustive _ O.infinite').mp ⟨B,h⟩,fun hw => ?_⟩
  obtain ⟨emit,he⟩ := weakEnumeration_of_condition hw
  let A := Angluin.stageContents emit
  let B := CharikarPabbaraju.membershipExhaustiveAlgorithm O A
  have hA := CharikarPabbaraju.weakTellTaleApproximation_of_enumeration he
  refine ⟨learnerOfFiniteHistory B,?_,(exhaustive_iff_tuple _ _).mpr ?_⟩
  · intro z s hp
    choose T hT stage hstage using hA.2
    let K := O.language z
    let good := fun j => K ⊆ O.language j ∧ (T j : Set ℕ) ⊆ K
    have ex : ∃ j, good j := ⟨z,Set.Subset.rfl,(hT z).1⟩
    let g := Nat.find ex
    have hg : good g := Nat.find_spec ex
    let S := Generic.sample s
    have hsub (t) : (↑(S t) : Set ℕ) ⊆ K := by
      intro x hx
      obtain ⟨k,_,rfl⟩ := Generic.mem_sample_iff.mp hx
      change s k ∈ O.language z
      exact hp ▸ Set.mem_range_self k
    obtain ⟨M,hM⟩ := Generic.finset_eventually_subset_sample hp (T g) hg.2
    have single (j) (hj : j < g) : ∃ N, ∀ t ≥ N,
        ¬CharikarPabbaraju.WeakStageEligible O A (S t) t j := by
      have hn := Nat.find_min ex hj
      by_cases h : K ⊆ O.language j
      · refine ⟨stage j,fun t ht elig => hn ⟨h,fun x hx => hsub t (elig.1 ?_)⟩⟩
        rwa [show A j t = T j from hstage j t ht]
      · obtain ⟨x,hx,hout⟩ := Set.not_subset.mp h
        obtain ⟨N,hN⟩ := Generic.eventually_mem_sample_of_presents hp hx
        exact ⟨N,fun t ht elig => hout (elig.2 (hN t ht))⟩
    obtain ⟨N,hN⟩ := Angluin.eventually_all_lt single
    let cutoff := max (max M (stage g)) (max g N)
    have chosen (t) (ht : cutoff ≤ t) : CharikarPabbaraju.weakStageFocus O A (S t) t = g := by
      dsimp [cutoff] at ht
      have hgmem : g ∈ CharikarPabbaraju.weakStageCandidates O A (S t) t := by
        apply CharikarPabbaraju.mem_weakStageCandidates.mpr
        refine ⟨by omega,?_,(hsub t).trans hg.1⟩
        rw [show A g t = T g from hstage g t (by omega)]
        exact hM.trans (Generic.sample_mono (by omega : M ≤ t))
      apply le_antisymm (CharikarPabbaraju.weakStageFocus_le hgmem)
      apply le_of_not_gt
      intro h
      exact hN t (by omega) _ h
        (CharikarPabbaraju.mem_weakStageCandidates.mp (CharikarPabbaraju.weakStageFocus_mem hgmem)).2
    have range_eq (t) (ht : cutoff ≤ t) : supportAt (enumeratorSupport (learnerOfFiniteHistory B)) s t =
        O.language g := by
      change Set.range (learnerOfFiniteHistory B (textPrefix s t)) = _
      rw [textPrefix_eq_ofFn, learnerOfFiniteHistory_ofFn]
      change CharikarPabbaraju.generateOnly (CharikarPabbaraju.membershipExhaustiveAlgorithm O A) s t = _
      rw [CharikarPabbaraju.generateOnly_membershipExhaustiveAlgorithm, chosen t ht]
    exact ⟨cutoff,fun t u ht hu => (range_eq t ht).trans (range_eq u hu).symm⟩
  · simpa only [tupleEnumerator_inverse] using CharikarPabbaraju.proposition6_3_of_weakTellTaleApproximation O _ hA

private theorem no_condition_coSingleton : ¬ Angluin.ConditionTwo CharikarPabbaraju.coSingletonNatFamily := by
  intro h
  obtain ⟨T, hT, ht⟩ := h 0
  apply CharikarPabbaraju.coSingletonNatFamily_no_telltale_for_univ T
  refine ⟨hT, ?_⟩
  rintro _ ⟨j,rfl⟩ hj hss
  exact hss.ne (Set.Subset.antisymm hss.subset (ht j hj hss.subset))

/-- Under Definition 4.2 finite hallucinations are permitted in the future
range. The constant identity enumeration has stable full range on the whole
universe and every co-singleton, a family violating Angluin's condition. -/
theorem theorem_4_5_stable_exhaustive_counterexample :
    let F := CharikarPabbaraju.coSingletonNatFamily
    (∃ A : Enumerator ℕ, IsStableGenerator (enumeratorSupport A) F ∧ EnumeratesExhaustively A F) ∧
      ¬Angluin.ConditionTwo F := by
  refine ⟨⟨fun _ => id, fun _ _ _ => ⟨0, fun _ _ _ _ => rfl⟩, ?_⟩, no_condition_coSingleton⟩
  intro i s _
  refine ⟨0, fun t _ => ⟨?_, fun x _ => Or.inr ⟨x,rfl⟩⟩⟩
  cases i <;> simp [CharikarPabbaraju.coSingletonNatFamily]

end GenLimit.BreadthCharacterizations
