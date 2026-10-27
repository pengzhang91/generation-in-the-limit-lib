import GenLimit.Paper03_HallucinationAndModeCollapse.UniversalRates
import GenLimit.Support.OracleTruthTable

/-!
# A certified finite-query oracle realization

Definition 11 supplies an oracle enumerating each finite tell-tale. At sample
size `n` the procedure queries only stages below `n` for candidate indices at
most `n`; it never tests whether an enumeration is complete. This matches the
stage learner used in `AngluinWitnessRates` for any supplied valid enumerator.

The learner below is one fixed truth-table procedure: its query formation is
primitive recursive and its postprocessor is computable. It queries only the
membership oracle and the tell-tale enumeration oracle. No rate-dependent advice
or distribution-dependent oracle is used.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.Support Encodable

def emissionCode (j s : ℕ) : ℕ := Nat.pair 0 (Nat.pair j s)
def memberCode (j x : ℕ) : ℕ := Nat.pair 1 (Nat.pair j x)

def identificationQueries (xs : List ℕ) : List ℕ :=
  (List.range (xs.length + 1)).flatMap (fun j =>
    (List.range xs.length).map (emissionCode j) ++ xs.map (memberCode j))

theorem identificationQueries_primrec : Primrec identificationQueries := by
  have ht : Primrec₂ emissionCode :=
    (Primrec₂.natPair.comp (Primrec.const 0) (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).to₂
  have hm : Primrec₂ memberCode :=
    (Primrec₂.natPair.comp (Primrec.const 1) (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).to₂
  have hmap : Primrec (fun z : List ℕ × ℕ => z.1.map (memberCode z.2)) :=
    Primrec.list_map Primrec.fst (Primrec.to₂
      (hm.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  have hem : Primrec (fun z : List ℕ × ℕ =>
      (List.range z.1.length).map (emissionCode z.2)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
      (Primrec.to₂ (ht.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact Primrec.list_flatMap
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
    ((Primrec.list_append.comp hem hmap).to₂)

def answerAt (data : List ℕ × List ℕ) (code : ℕ) : ℕ :=
  tableLookup (identificationQueries data.1) data.2 code

theorem answerAt_primrec : Primrec₂ answerAt := by
  have hi : Primrec (fun z : (List ℕ × List ℕ) × ℕ =>
      (identificationQueries z.1.1).idxOf z.2) :=
    Primrec.list_idxOf.comp Primrec.snd
      (identificationQueries_primrec.comp (Primrec.fst.comp Primrec.fst))
  exact (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) hi)
    (Primrec.const 0)).to₂

def decodedTell (data : List ℕ × List ℕ) (j : ℕ) : List ℕ :=
  (List.range data.1.length).filterMap (fun s =>
    (decode (α := Option ℕ) (answerAt data (emissionCode j s))).getD none)

theorem decodedTell_primrec : Primrec₂ decodedTell := by
  have hc : Primrec (fun z : ((List ℕ × List ℕ) × ℕ) × ℕ =>
      answerAt z.1.1 (emissionCode z.1.2 z.2)) :=
    answerAt_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.const 0)
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact (Primrec.listFilterMap
    (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
    ((Primrec.option_getD.comp (Primrec.decode.comp hc) (Primrec.const none)).to₂)).to₂

def tableEligible (data : List ℕ × List ℕ) (j : ℕ) : Bool :=
  decide ((∀ x ∈ decodedTell data j, x ∈ data.1) ∧
    (∀ x ∈ data.1, answerAt data (memberCode j x) = 1))

theorem tableEligible_primrec : Primrec₂ tableEligible := by
  let D := List ℕ × List ℕ
  have hmem : PrimrecRel (fun x : ℕ => fun xs : List ℕ => x ∈ xs) := by
    apply (Primrec.nat_lt.comp
      (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd)).of_eq
    intro z
    exact List.idxOf_lt_length_iff
  have ht : PrimrecPred (fun z : D × ℕ => ∀ x ∈ decodedTell z.1 z.2, x ∈ z.1.1) :=
    hmem.forall_mem_list.comp (decodedTell_primrec.comp Primrec.fst Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have hr : PrimrecRel (fun x : ℕ => fun z : D × ℕ => answerAt z.1 (memberCode z.2 x) = 1) :=
    Primrec.eq.comp
      (answerAt_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec₂.natPair.comp (Primrec.const 1)
          (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)))
      (Primrec.const 1)
  have ho : PrimrecPred (fun z : D × ℕ => ∀ x ∈ z.1.1,
      answerAt z.1 (memberCode z.2 x) = 1) :=
    hr.forall_mem_list.comp (Primrec.fst.comp Primrec.fst) Primrec.id
  exact (ht.and ho).decide.to₂

def identificationPost (data : List ℕ × List ℕ) : ℕ :=
  (firstTrue tableEligible data (data.1.length + 1)).getD 0

theorem identificationPost_computable : Computable identificationPost := by
  have hsearch := (firstTrue_computable tableEligible_primrec.to_comp).comp Computable.id
    ((Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)).to_comp)
  exact Computable.option_getD hsearch (Computable.const 0)

def identificationProgram : TruthTableProgram where
  queries := identificationQueries
  queries_primrec := identificationQueries_primrec
  output := identificationPost
  output_computable := identificationPost_computable

def identificationOracle {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (emit : ℕ → ℕ → Option ℕ) (code : ℕ) : ℕ :=
  if code.unpair.1 = 0 then encode (emit code.unpair.2.unpair.1 code.unpair.2.unpair.2)
  else if code.unpair.1 = 1 then
    if O.query code.unpair.2.unpair.1 code.unpair.2.unpair.2 then 1 else 0
  else 0

theorem tableEligible_iff_stage {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (emit : ℕ → ℕ → Option ℕ) (xs : List ℕ) (j : ℕ) (hj : j ≤ xs.length) :
    tableEligible (xs, (identificationQueries xs).map (identificationOracle O emit)) j = true ↔
      GenLimit.Angluin.StageEligible C (GenLimit.Angluin.stageContents emit) xs j := by
  have hqt (s : ℕ) (hs : s < xs.length) : emissionCode j s ∈ identificationQueries xs :=
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj),
      List.mem_append_left _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩)⟩
  have hqm (x : ℕ) (hx : x ∈ xs) : memberCode j x ∈ identificationQueries xs :=
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj),
      List.mem_append_right _ (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩
  have ht : decodedTell (xs, (identificationQueries xs).map (identificationOracle O emit)) j =
      (List.range xs.length).filterMap (emit j) := by
    have hdecode (s : ℕ) (hs : s ∈ List.range xs.length) :
        (decode (α := Option ℕ)
          (answerAt (xs, (identificationQueries xs).map (identificationOracle O emit))
            (emissionCode j s))).getD none = emit j s := by
      simp only [answerAt, tableLookup_map _ _ _ (hqt s (List.mem_range.mp hs))]
      simp [identificationOracle, emissionCode]
    unfold decodedTell
    exact List.filterMap_congr hdecode
  have hm (x : ℕ) (hx : x ∈ xs) :
      answerAt (xs, (identificationQueries xs).map (identificationOracle O emit)) (memberCode j x) = 1 ↔
        x ∈ C j := by
    simp only [answerAt, tableLookup_map _ _ _ (hqm x hx)]
    simp [identificationOracle, memberCode, O.query_spec]
  simp only [tableEligible, decide_eq_true_eq, ht]
  change _ ↔ j ≤ xs.length ∧ _
  simp only [hj, true_and, GenLimit.Angluin.historySample, GenLimit.Angluin.stageContents,
    GenLimit.Support.stageContents, Finset.subset_iff, List.mem_toFinset]
  constructor
  · rintro ⟨hT, hC⟩
    refine ⟨hT, ?_⟩
    intro x hx
    have hx' : x ∈ xs := by simpa using hx
    exact (hm x hx').mp (hC x hx')
  · rintro ⟨hT, hC⟩
    exact ⟨hT, fun x hx => (hm x hx).mpr (hC (by simpa using hx))⟩

theorem identificationProgram_eq_angluin {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (emit : ℕ → ℕ → Option ℕ) :
    identificationProgram.run (identificationOracle O emit) =
      GenLimit.Angluin.semanticLearner C (GenLimit.Angluin.stageContents emit) := by
  classical
  funext xs
  apply firstTrue_eq_least tableEligible
    (xs, (identificationQueries xs).map (identificationOracle O emit)) (xs.length + 1)
    (GenLimit.Angluin.StageEligible C (GenLimit.Angluin.stageContents emit) xs)
  · intro j hj
    exact tableEligible_iff_stage O emit xs j (Nat.lt_succ_iff.mp hj)
  · intro j hj; exact Nat.lt_succ_of_le hj.1

/-- The actual oracle procedure is ordinarily computable whenever its two
oracles are supplied by computable membership and emission functions. This
certificate concerns the same program used by the main theorem. -/
theorem identificationProgram_computable (F : GenLimit.Angluin.EffectiveIndexedFamily)
    (emit : ℕ → ℕ → Option ℕ) (hemit : Computable₂ emit) :
    Computable (identificationProgram.run (identificationOracle
      (C := F.language) ⟨F.membership, fun {i x} => F.membership_spec i x⟩ emit)) := by
  rw [identificationProgram_eq_angluin]
  have heq : GenLimit.Angluin.effectiveLearner F emit =
      GenLimit.Angluin.semanticLearner F.language (GenLimit.Angluin.stageContents emit) := by
    funext xs
    simpa using GenLimit.Angluin.effectiveLearner_eq_semanticLearner F emit xs.length xs.get
  rw [← heq]
  exact GenLimit.Angluin.effectiveLearner_computable F hemit

/-- Every valid supplied tell-tale enumeration suffices; the procedure reads
only finite prefixes and uses no completion test. -/
theorem oracle_exponentialIdentifies_of_enumeration
    (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (emit : ℕ → ℕ → Option ℕ)
    (hTell : ∀ i, GenLimit.Angluin.IsEnumeratedTellTale C i (GenLimit.Angluin.enumeratedSet emit i)) :
    ExponentialIdentifies C (deterministicIdentifier
      (identificationProgram.run (identificationOracle O emit))) := by
  rw [identificationProgram_eq_angluin]
  exact lemma_8_1 C _ (angluinLearner_finiteWitness C _
    (GenLimit.Angluin.tellTaleApproximation_of_enumeration hTell))

/-- The source's existential tell-tale oracle can be chosen independently of
both the target distribution and the rate exponent. One certified procedure
then attains the stronger exponential upper bound. -/
theorem oracle_exponentialIdentifies_of_conditionTwo
    (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (hC : GenLimit.Angluin.ConditionTwo C) :
    ∃ emit : ℕ → ℕ → Option ℕ,
      (∀ i, GenLimit.Angluin.IsEnumeratedTellTale C i (GenLimit.Angluin.enumeratedSet emit i)) ∧
      ExponentialIdentifies C (deterministicIdentifier
        (identificationProgram.run (identificationOracle O emit))) := by
  classical
  let T := GenLimit.Angluin.chosenTellTale C hC
  let emit : ℕ → ℕ → Option ℕ := fun i s => (T i).toList[s]?
  have hset (i : ℕ) : GenLimit.Angluin.enumeratedSet emit i = (↑(T i) : Set ℕ) := by
    ext x
    simp only [GenLimit.Angluin.enumeratedSet, GenLimit.Support.enumeratedSet, Set.mem_setOf_eq,
      Finset.mem_coe, ← Finset.mem_toList, List.mem_iff_getElem?]
    rfl
  have hTell (i : ℕ) : GenLimit.Angluin.IsEnumeratedTellTale C i
      (GenLimit.Angluin.enumeratedSet emit i) := by
    rw [hset]
    have hi := GenLimit.Angluin.chosenTellTale_spec C hC i
    exact ⟨(T i).finite_toSet, hi.1, hi.2⟩
  refine ⟨emit, hTell, ?_⟩
  exact oracle_exponentialIdentifies_of_enumeration C O emit hTell

/-- Full Theorem 3.1 with an explicit oracle computation witness for the
positive branch. The first three conjuncts are the mathematical source
dichotomy; the last certifies a finite-query realization using the standing
membership oracle and a valid existentially chosen tell-tale oracle. -/
theorem theorem_3_1 (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (hC : NontrivialCollection C) :
    ((AlmostExponentialIdentifiable C ∧ ¬NoIdentificationRate C) ∨
      (¬AlmostExponentialIdentifiable C ∧ NoIdentificationRate C)) ∧
      (AlmostExponentialIdentifiable C ↔ GenLimit.Angluin.ConditionTwo C) ∧
      (∀ A : StatisticalIdentifier, ∃ i p, ValidDistribution C i p ∧
        ∃ᶠ n : ℕ in Filter.atTop, Real.exp (-2 * (n : ℝ)) ≤ identificationError C A p i n) ∧
      (GenLimit.Angluin.ConditionTwo C →
        ∃ emit : ℕ → ℕ → Option ℕ,
          (∀ i, GenLimit.Angluin.IsEnumeratedTellTale C i (GenLimit.Angluin.enumeratedSet emit i)) ∧
          ExponentialIdentifies C (deterministicIdentifier
            (identificationProgram.run (identificationOracle O emit)))) := by
  obtain ⟨hd, hi, hl⟩ := theorem_3_1_mathematical C hC
  exact ⟨hd, hi, hl, oracle_exponentialIdentifies_of_conditionTwo C O⟩

end GenLimit.HallucinationModeCollapse
