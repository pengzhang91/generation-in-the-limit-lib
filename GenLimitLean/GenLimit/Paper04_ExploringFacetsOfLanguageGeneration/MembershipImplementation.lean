import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.MembershipExhaustive
import GenLimit.Paper03_HallucinationAndModeCollapse.BreadthConstruction

/-! # Proposition 6.3 as a computation on encoded histories -/

namespace GenLimit.CharikarPabbaraju

open GenLimit.HallucinationModeCollapse

theorem trainedFocus_eq (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ) (xs : List ℕ) :
    identificationProgram.run (identificationOracle (familyMembership O) emit) xs =
      weakStageFocus O (Angluin.stageContents emit) xs.toFinset xs.length := by
  classical
  rw [identificationProgram_eq_angluin]
  let A := Angluin.stageContents emit
  let C := weakStageCandidates O A xs.toFinset xs.length
  have hm (j) : j ∈ C ↔ Angluin.StageEligible O.language A xs j := by
    have hx : Angluin.historySample xs = xs.toFinset := by ext x; simp [Angluin.historySample]
    simp only [C, mem_weakStageCandidates, WeakStageEligible, Angluin.StageEligible, hx]
  by_cases h : C.Nonempty
  · have hx : ∃ i, Angluin.StageEligible O.language A xs i := ⟨_, (hm _).mp h.choose_spec⟩
    have hs := Angluin.semanticLearner_eligible hx
    exact le_antisymm (Angluin.semanticLearner_le_of_eligible ((hm _).mp (weakStageFocus_mem h.choose_spec)))
      (weakStageFocus_le ((hm _).mpr hs))
  · have hn : ¬∃ i, Angluin.StageEligible O.language A xs i := fun ⟨i, hi⟩ => h ⟨i, (hm _).mpr hi⟩
    simp only [Angluin.semanticLearner, weakStageFocus, dif_neg hn, dif_neg h, A, C] at *

/-- The existing dependent enumeration is the ordinary numerical oracle
search for the first accepted output. -/
private theorem scan_rfind (O : OracleFamily) (i n : ℕ) :
    enumerateOracleLanguage O i n ∈ Nat.rfind (fun x => Part.some (decide (n ≤ x) && O.query i x)) := by
  rw [Nat.mem_rfind]
  obtain ⟨hge, hmem⟩ := enumerateOracleLanguage_spec O i n
  constructor
  · simp [hge, (O.query_spec i _).mpr hmem]
  · intro m hlt
    have hn := Nat.find_min (oracle_language_has_member_at_or_above O i n) hlt
    by_cases hnm : n ≤ m
    · simp [hnm] at hn
      simp [hnm, hn]
    · simp [hnm]

/-- Membership-only training and search, evaluated on an ordered history
and a seed. The stage predicate is total relative to the membership oracle. -/
def exhaustiveSearch (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (input : List ℕ × ℕ) : Part ℕ :=
  let i := identificationProgram.run (identificationOracle (familyMembership O) emit) input.1
  Nat.rfind (fun x => Part.some (decide (input.2 ≤ x) && O.query i x))

theorem exhaustiveSearch_realizes (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (t : ℕ) (xs : Fin t → ℕ) (n : ℕ) :
    membershipExhaustiveAlgorithm O (Angluin.stageContents emit) t xs n ∈
      exhaustiveSearch O emit (List.ofFn xs, n) := by
  have hs : (List.ofFn xs).toFinset = Generic.sequenceSample xs := by
    ext x
    simp [Generic.sequenceSample, List.mem_ofFn]
  unfold exhaustiveSearch
  rw [trainedFocus_eq, List.length_ofFn, hs]
  exact scan_rfind O _ _

/-- An ordinary computability certificate when the membership oracle itself
is computable. Without that assumption the same finite training program
and terminating oracle search are certified by `exhaustiveSearch_realizes`. -/
theorem membershipExhaustive_computable (O : OracleFamily) (hO : Computable₂ O.query)
    (emit : ℕ → ℕ → Option ℕ) (he : Computable₂ emit) :
    Computable (fun p : List ℕ × ℕ =>
      membershipExhaustiveAlgorithm O (Angluin.stageContents emit) p.1.length p.1.get p.2) := by
  have hi := oracleIdentifier_computable O hO emit he
  let check := fun (p : List ℕ × ℕ) (x : ℕ) => decide (p.2 ≤ x) && O.query
      (identificationProgram.run (identificationOracle (familyMembership O) emit) p.1) x
  have test : Computable₂ check :=
    (Primrec.and.to_comp.comp (Primrec.nat_le.decide.to_comp.comp
      (Computable.snd.comp Computable.fst) Computable.snd)
      (hO.comp (hi.comp (Computable.fst.comp Computable.fst)) Computable.snd)).to₂
  have search : Partrec (exhaustiveSearch O emit) :=
    Partrec.rfind (p := fun p x => Part.some (check p x)) test
  apply search.of_eq_tot
  intro p
  simpa using exhaustiveSearch_realizes O emit p.1.length p.1.get p.2

/-- Proposition 6.3 with one algorithm and the implementation certificate
for that very algorithm, including its default behavior before convergence. -/
theorem proposition6_3_certified (O : OracleFamily) (hw : WeakAngluinEnumeration O) :
    ∃ emit : ℕ → ℕ → Option ℕ, Computable₂ emit ∧
      IsExhaustiveGenerator (membershipExhaustiveAlgorithm O (Angluin.stageContents emit)) (Set.range O.language) ∧
      (∀ t xs n, membershipExhaustiveAlgorithm O (Angluin.stageContents emit) t xs n ∈
        exhaustiveSearch O emit (List.ofFn xs, n)) ∧
      (Computable₂ O.query → Computable (fun p : List ℕ × ℕ =>
        membershipExhaustiveAlgorithm O (Angluin.stageContents emit) p.1.length p.1.get p.2)) := by
  obtain ⟨emit, he, hT⟩ := hw
  exact ⟨emit, he, proposition6_3_of_weakTellTaleApproximation O _
      (weakTellTaleApproximation_of_enumeration hT), exhaustiveSearch_realizes O emit,
    fun hO => membershipExhaustive_computable O hO emit he⟩

end GenLimit.CharikarPabbaraju
