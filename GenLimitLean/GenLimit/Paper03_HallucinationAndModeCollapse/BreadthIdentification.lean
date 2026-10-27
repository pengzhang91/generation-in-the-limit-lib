import GenLimit.Paper03_HallucinationAndModeCollapse.BreadthModel
import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineReductions
import GenLimit.Support.OracleTruthTable

/-!
# Lemma 6.4: statistical breadth reduces to identification

The identifier checks only candidate indices at most the sample length and
domain points below that length. It adds the training sample back to the
proposed fresh support. Its error is eventually bounded by breadth error.
The mathematical impossibility uses the existing randomized necessity theorem
and is stronger than the source restriction to generators with decidable MOP.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID GenLimit.Support Filter

def breadthMatches {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (Q : List ℕ → ℕ → Bool) (xs : List ℕ) (j : ℕ) : Bool :=
  boundedAll (fun data : List ℕ × ℕ => fun x =>
    O.query data.2 x == (Q data.1 x || listContains data.1 x)) (xs, j) xs.length

def breadthIdentifier {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (Q : List ℕ → ℕ → Bool) (xs : List ℕ) : ℕ :=
  (firstTrue (breadthMatches O Q) xs (xs.length + 1)).getD 0

theorem breadthMatches_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (hO : Computable₂ O.query)
    (Q : List ℕ → ℕ → Bool) (hQ : Computable₂ Q) : Computable₂ (breadthMatches O Q) := by
  have hp : Computable₂ (fun data : List ℕ × ℕ => fun x =>
      O.query data.2 x == (Q data.1 x || listContains data.1 x)) :=
    (Primrec.beq.to_comp.comp
      (hO.comp (Computable.snd.comp Computable.fst) Computable.snd)
      (Primrec.or.to_comp.comp
        (hQ.comp (Computable.fst.comp Computable.fst) Computable.snd)
        (listContains_computable.comp (Computable.fst.comp Computable.fst) Computable.snd))).to₂
  exact ((boundedAll_computable hp).comp Computable.id
    (Computable.list_length.comp Computable.fst)).to₂

theorem breadthIdentifier_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (hO : Computable₂ O.query)
    (Q : List ℕ → ℕ → Bool) (hQ : Computable₂ Q) : Computable (breadthIdentifier O Q) := by
  exact Computable.option_getD
    ((firstTrue_computable (breadthMatches_computable O hO Q hQ)).comp Computable.id
      ((Primrec.succ.comp Primrec.list_length).to_comp)) (Computable.const 0)

theorem breadthMatches_correct {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support) (xs : List ℕ) (j : ℕ) :
    breadthMatches O Q xs j = true ↔
      MatchesInitialSegment C ((G xs).support ∪ {x | x ∈ xs}) xs.length j := by
  simp only [breadthMatches, boundedAll_eq_true_iff, beq_iff_eq]
  constructor
  · intro h x hx
    have he := congrArg (fun b : Bool => b = true) (h x hx)
    simpa only [O.query_spec, Bool.or_eq_true, hQ, listContains_eq_true_iff,
      Set.mem_union, Set.mem_setOf_eq] using Iff.of_eq he
  · intro h x hx
    apply Bool.eq_iff_iff.mpr
    simpa only [O.query_spec, Bool.or_eq_true, hQ, listContains_eq_true_iff,
      Set.mem_union, Set.mem_setOf_eq] using h x hx

theorem breadthIdentifier_eventually_correct {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support) (i : ℕ) :
    ∃ N, ∀ xs : List ℕ, N ≤ xs.length → (∀ x ∈ xs, x ∈ C i) →
      (G xs).support = C i \ {x | x ∈ xs} → C (breadthIdentifier O Q xs) = C i := by
  classical
  let hex : ∃ j, C j = C i := ⟨i, rfl⟩
  let z := Nat.find hex
  have hz : C z = C i := Nat.find_spec hex
  have hleast : IsLeastTargetIndex C z := by
    intro j hj he
    exact Nat.find_min hex hj (he.trans hz)
  obtain ⟨T, hT⟩ := eventually_leastMatching_of_target hleast
  refine ⟨max T z, ?_⟩
  intro xs hn hxs hgood
  have hcomplete : (G xs).support ∪ {x | x ∈ xs} = C z := by
    rw [hgood, hz]
    exact Set.diff_union_of_subset (fun x hx => hxs x hx)
  have hmatch : breadthMatches O Q xs z = true := by
    apply (breadthMatches_correct O G Q hQ xs z).mpr
    rw [hcomplete]
    exact fun _ _ => Iff.rfl
  have hzlen : z < xs.length + 1 := Nat.lt_succ_of_le ((le_max_right _ _).trans hn)
  have hsome : firstTrue (breadthMatches O Q) xs (xs.length + 1) ≠ none := by
    intro hnone
    have hf := (firstTrue_eq_none_iff _ _ _).mp hnone z hzlen
    simp [hmatch] at hf
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hsome
  have hjle : j ≤ z := firstTrue_le_of_true hj hzlen hmatch
  have hjz : j = z := by
    by_contra hne
    have hlt : j < z := lt_of_le_of_ne hjle hne
    have hjmatch := (breadthMatches_correct O G Q hQ xs j).mp (firstTrue_spec hj).2.1
    rw [hcomplete] at hjmatch
    exact hT xs.length ((le_max_left _ _).trans hn) j hlt hjmatch
  simp only [breadthIdentifier, hj, Option.getD_some, hjz, hz]

theorem identificationError_le_breadthError_eventually {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support)
    (i : ℕ) (p : PMF ℕ) (hp : ValidDistribution C i p) :
    ∀ᶠ n : ℕ in atTop, identificationError C (deterministicIdentifier (breadthIdentifier O Q)) p i n ≤
      breadthError C G p i n := by
  obtain ⟨N, hN⟩ := breadthIdentifier_eventually_correct O G Q hQ i
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  rw [identificationError_deterministic, ← probability_inter_support]
  apply probability_mono
  rintro xs ⟨hwrong, hs⟩ hgood
  obtain ⟨hl, hm⟩ := (samples_support p n xs).mp hs
  exact hwrong (hN xs (hl.symm ▸ hn) (fun x hx => hp ▸ hm x hx) hgood)

/-- Lemma 6.4, strengthened to a fixed-distribution limsup bound. The proof
already rules out arbitrary semantic PMF generators, so in particular it
covers both the pointwise and uniform decidable-MOP classes. -/
theorem lemma_6_4 (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (hC : ¬IdentifiableInLimit C) (G : StatisticalGenerator) :
    ∃ i p, ValidDistribution C i p ∧
      (1 / 2 : ℝ) ≤ limsup (fun n => breadthError C G p i n) atTop := by
  classical
  let Q : List ℕ → ℕ → Bool := fun xs x => decide (x ∈ (G xs).support)
  have hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support := by simp [Q]
  have hnot : ¬GenLimit.Angluin.ConditionTwo C :=
    fun h => hC ((GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo C).mpr h)
  obtain ⟨i, p, hp, hf⟩ := lemma_5_8_frequently C hnot
    (deterministicIdentifier (breadthIdentifier O Q))
  have hbound := identificationError_le_breadthError_eventually O G Q hQ i p hp
  refine ⟨i, p, hp, le_limsup_of_frequently_le ?_ ?_⟩
  · exact (hf.and_eventually hbound).mono (fun _ h => h.1.trans h.2)
  · exact isBoundedUnder_of ⟨1, breadthError_le_one C G p i⟩

theorem noBreadthRate_of_not_identifiable (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (hC : ¬IdentifiableInLimit C) (G : StatisticalGenerator) :
    NoBreadthRate C G := by
  obtain ⟨i, p, hp, hl⟩ := lemma_6_4 C O hC G
  exact ⟨i, p, hp, lt_of_lt_of_le (by norm_num) hl⟩

end GenLimit.HallucinationModeCollapse
