import GenLimit.Paper05_HallucinationsBreadthAndStability.EffectiveBreadth
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.MembershipImplementation

/-! # Approximate breadth from finite evidence and weak tell-tale enumeration -/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Support GenLimit.HallucinationModeCollapse GenLimit.CharikarPabbaraju

theorem weakEnumeration_of_condition {F : Generic.LanguageFamily ℕ} (hw : WeakAngluinCondition F) :
    ∃ emit, ∀ i, IsEnumeratedWeakTellTale F i (Angluin.enumeratedSet emit i) := by
  classical
  choose T hT using hw
  let emit := fun i s : ℕ => (T i).toList[s]?
  refine ⟨emit, fun i => ?_⟩
  have he : Angluin.enumeratedSet emit i = (T i : Set ℕ) := by
    ext x
    simp only [Angluin.enumeratedSet, Support.enumeratedSet, Set.mem_setOf_eq,
      Finset.mem_coe, ← Finset.mem_toList, List.mem_iff_getElem?]
    rfl
  rw [he]
  exact ⟨(T i).finite_toSet, (hT i).1, (hT i).2⟩

/-- Discard the first history-length many possible words from the language
selected by the bounded training program. Every conditioned law is normalized. -/
noncomputable def weakLaw (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ) : StatisticalGenerator :=
  fun xs => exactFreshSampler O (List.range xs.length)
    (identificationProgram.run (identificationOracle (familyMembership O) emit) xs)

/-- A fixed target requires only a finite witness in the sample and a
large enough sample length. Both are independent of the order of training. -/
theorem weakLaw_finiteWitness (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (hTell : ∀ i, IsEnumeratedWeakTellTale O.language i (Angluin.enumeratedSet emit i)) (z : ℕ) :
    ∃ W : Finset ℕ, (↑W : Set ℕ) ⊆ O.language z ∧ ∃ N, ∀ xs : List ℕ,
      N ≤ xs.length → (∀ x ∈ xs, x ∈ O.language z) → (∀ x ∈ W, x ∈ xs) →
      ApproximateBreadthAt ((weakLaw O emit xs).support) (O.language z) := by
  classical
  let A := Angluin.stageContents emit
  obtain ⟨_,hA⟩ := weakTellTaleApproximation_of_enumeration hTell
  choose T hT stage hstage using hA
  let K := O.language z
  have single (i : ℕ) : ∃ W : Finset ℕ, (↑W : Set ℕ) ⊆ K ∧ ∃ b : ℕ,
      ∀ S : Finset ℕ, ∀ t ≥ b, W ⊆ S → (↑S : Set ℕ) ⊆ K → WeakStageEligible O A S t i →
        K ⊆ O.language i ∧ ∀ x ∈ O.language i, t ≤ x → x ∈ K := by
    by_cases hk : K ⊆ O.language i
    · refine ⟨∅, by simp, ?_⟩
      by_cases ht : (↑(T i) : Set ℕ) ⊆ K
      · have hf : (O.language i \ K).Finite := by
          rcases eq_or_lt_of_le hk with eq | strict
          · simp [eq]
          · exact (hT i).2 z ht strict
        obtain ⟨b,hb⟩ := hf.bddAbove
        refine ⟨b+1, fun S t hb' _ _ _ => ⟨hk, fun x hx htx => ?_⟩⟩
        by_contra hn
        have hle := hb (show x ∈ O.language i \ K from ⟨hx,hn⟩)
        omega
      · refine ⟨stage i, fun S t ht' _ hsub elig => (ht ?_).elim⟩
        intro x hx
        apply hsub
        apply elig.1
        rwa [show A i t = T i from hstage i t ht']
    · obtain ⟨x,hx,hnot⟩ := Set.not_subset.mp hk
      refine ⟨{x}, by simpa using hx, 0, fun S t _ hS _ elig => ?_⟩
      exact (hnot (elig.2 (hS (Finset.mem_singleton_self x)))).elim
  choose W hW b hb using single
  let I := Finset.range (z+1)
  let evidence := T z ∪ I.biUnion W
  refine ⟨evidence, ?_, max (max z (stage z)) (I.sup b), ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with ht | hws
    · exact (hT z).1 ht
    · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hws
      exact hW j hj
  intro xs hn hxs hevidence
  let S := xs.toFinset
  let t := xs.length
  have hs : (↑S : Set ℕ) ⊆ K := fun _ hx => hxs _ (List.mem_toFinset.mp hx)
  have hWsub : evidence ⊆ S := fun _ hx => List.mem_toFinset.mpr (hevidence _ hx)
  have hz : z ∈ weakStageCandidates O A S t := by
    apply mem_weakStageCandidates.mpr
    refine ⟨by dsimp [t]; omega, ?_, hs⟩
    rw [show A z t = T z from hstage z _ (by dsimp [t]; omega)]
    exact Finset.Subset.trans Finset.subset_union_left hWsub
  let g := weakStageFocus O A S t
  have hgle : g ≤ z := weakStageFocus_le hz
  have hgI : g ∈ I := Finset.mem_range.mpr (by omega)
  have hbg : b g ≤ t := (Finset.le_sup hgI).trans ((Nat.le_max_right _ _).trans hn)
  obtain ⟨hkg,hgood⟩ := hb g S t hbg (fun x hx =>
    hWsub (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g,hgI,hx⟩))) hs
    (mem_weakStageCandidates.mp (weakStageFocus_mem hz)).2
  change ApproximateBreadthAt (exactFreshSampler O (List.range t) _).support K
  rw [exactFreshSampler_support, trainedFocus_eq]
  change (O.language g \ {x | x ∈ List.range t}) ⊆ K ∧ (K \ _).Finite
  constructor
  · intro x hx
    exact hgood x hx.1 (by simpa only [Set.mem_setOf_eq, List.mem_range, not_lt] using hx.2)
  · apply (Finset.range t).finite_toSet.subset
    intro x hx
    by_contra hn'
    exact hx.2 ⟨hkg hx.1, by simpa using hn'⟩

theorem weakLaw_approximate (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (hTell : ∀ i, IsEnumeratedWeakTellTale O.language i (Angluin.enumeratedSet emit i)) :
    IsApproximateBreadthGenerator (lawSupport (weakLaw O emit)) O.language := by
  intro i s hp
  obtain ⟨W, hW, N, h⟩ := weakLaw_finiteWitness O emit hTell i
  obtain ⟨M, hM⟩ := Generic.finset_eventually_subset_sample hp W hW
  refine ⟨max N M,fun t ht => h (textPrefix s t) (by rw [textPrefix_length]; omega) ?_ ?_⟩
  · intro x hx
    obtain ⟨k,_,rfl⟩ := mem_textPrefix_iff.mp hx
    exact hp ▸ Set.mem_range_self k
  · intro x hx
    exact mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp (Generic.sample_mono (by omega : M ≤ t) (hM hx)))

/-- Lemma 7.3 with a relative membership program for each trained support.
A computable presentation of the two training oracles gives one ordinary
sampler uniform in the history and seed. -/
theorem lemma_7_3 (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (he : ∀ i, IsEnumeratedWeakTellTale O.language i (Angluin.enumeratedSet emit i)) :
    IsApproximateBreadthGenerator (lawSupport (weakLaw O emit)) O.language ∧
    OracleMOP (generationOracle O) (weakLaw O emit) ∧
    (Computable₂ O.query → Computable₂ emit → HasComputableSampler (weakLaw O emit) ∧
      UniformDecidableMOP (weakLaw O emit)) := by
  let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
  refine ⟨weakLaw_approximate O emit he, fun xs => ?_, ?_⟩
  · exact ⟨freshMOPProgram (List.range xs.length) (A xs), freshMOPProgram_correct O _ _⟩
  intro ho hem
  have hA : Computable A := oracleIdentifier_computable O ho emit hem
  have mask : Computable (fun xs : List ℕ => List.range xs.length) :=
    Primrec.list_range.to_comp.comp Computable.list_length
  constructor
  · refine ⟨fun p => seededFreshSample O (List.range p.1.length) (A p.1) p.2, ?_, fun _ => rfl⟩
    exact Computable.comp
      (f := fun z : (List ℕ × ℕ) × ℕ => seededFreshSample O z.1.1 z.1.2 z.2)
      (g := fun p : List ℕ × ℕ => ((List.range p.1.length, A p.1), p.2))
      (seededFreshSample_computable O ho)
      (Computable.pair (Computable.pair (mask.comp Computable.fst) (hA.comp Computable.fst)) Computable.snd)
  · refine ⟨fun xs x => O.query (A xs) x && !(listContains (List.range xs.length) x), ?_, ?_⟩
    · exact (Primrec.and.to_comp.comp (ho.comp (hA.comp Computable.fst) Computable.snd)
        (Primrec.not.to_comp.comp (listContains_computable.comp (mask.comp Computable.fst) Computable.snd))).to₂
    · exact fun xs x => exactFreshSampler_query_spec O (List.range xs.length) (A xs) x

theorem theorem_3_8_sampling (O : OracleFamily) (hw : WeakAngluinCondition O.language) :
    ∃ emit : ℕ → ℕ → Option ℕ,
      (∀ i, IsEnumeratedWeakTellTale O.language i (Angluin.enumeratedSet emit i)) ∧
      IsApproximateBreadthGenerator (lawSupport (weakLaw O emit)) O.language ∧
      OracleMOP (generationOracle O) (weakLaw O emit) ∧
      (Computable₂ O.query → Computable₂ emit → HasComputableSampler (weakLaw O emit) ∧
        UniformDecidableMOP (weakLaw O emit)) := by
  obtain ⟨emit,he⟩ := weakEnumeration_of_condition hw
  exact ⟨emit,he,lemma_7_3 O emit he⟩

end GenLimit.BreadthCharacterizations
