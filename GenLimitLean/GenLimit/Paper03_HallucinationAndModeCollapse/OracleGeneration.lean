import GenLimit.Paper03_HallucinationAndModeCollapse.KMGenerationRates
import GenLimit.Paper03_HallucinationAndModeCollapse.GenerationLowerBound
import GenLimit.Support.OracleSearchProgram

/-!
# Membership-only oracle computation for Theorem 3.2

Search over encoded pairs of a finite cutoff and a candidate index. At each
stage, read a finite membership table, check maximal finite criticality and a
fresh endpoint, and return that endpoint if the checks pass. P01's terminating
KM round supplies a successful stage. This stateless use of the same round
search resets the cutoff above the sample instead of carrying it between
samples. Its finite-witness guarantee is unchanged.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit GenLimit.Support

private theorem primrec_imp {α : Type*} [Primcodable α] {p r : α → Prop}
    (hp : PrimrecPred p) (hr : PrimrecPred r) : PrimrecPred (fun a => p a → r a) := by
  classical
  exact (hp.not.or hr).of_eq (fun _ => by tauto)

abbrev GenerationTable := (List ℕ × ℕ) × List ℕ

def generationQueries (input : List ℕ × ℕ) : List ℕ :=
  (List.range input.1.length).flatMap (fun j =>
    (input.1 ++ List.range input.2.unpair.1).map (Nat.pair j))

theorem generationQueries_primrec : Primrec generationQueries := by
  have hpoints : Primrec (fun z : (List ℕ × ℕ) × ℕ =>
      z.1.1 ++ List.range z.1.2.unpair.1) :=
    Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_range.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
  exact Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
    (Primrec.list_map hpoints
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂

def generationAnswer (data : GenerationTable) (code : ℕ) : ℕ :=
  tableLookup (generationQueries data.1) data.2 code

theorem generationAnswer_primrec : Primrec₂ generationAnswer := by
  have hi : Primrec (fun z : GenerationTable × ℕ =>
      (generationQueries z.1.1).idxOf z.2) :=
    Primrec.list_idxOf.comp Primrec.snd
      (generationQueries_primrec.comp (Primrec.fst.comp Primrec.fst))
  exact (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) hi) (Primrec.const 0)).to₂

def generationConsistent (data : GenerationTable) (j : ℕ) : Bool :=
  decide (∀ x ∈ data.1.1, generationAnswer data (Nat.pair j x) = 1)

theorem generationConsistent_primrec : Primrec₂ generationConsistent := by
  have hr : PrimrecRel (fun x : ℕ => fun z : GenerationTable × ℕ =>
      generationAnswer z.1 (Nat.pair z.2 x) = 1) :=
    Primrec.eq.comp
      (generationAnswer_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)) (Primrec.const 1)
  exact (hr.forall_mem_list.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.id).decide.to₂

def generationSubset (data : GenerationTable) (pair : ℕ) : Bool :=
  decide (∀ x ∈ List.range data.1.2.unpair.1,
    generationAnswer data (Nat.pair pair.unpair.1 x) = 1 →
      generationAnswer data (Nat.pair pair.unpair.2 x) = 1)

theorem generationSubset_primrec : Primrec₂ generationSubset := by
  have hcode₁ : Primrec (fun z : ℕ × (GenerationTable × ℕ) => Nat.pair z.2.2.unpair.1 z.1) :=
    Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))) Primrec.fst
  have hcode₂ : Primrec (fun z : ℕ × (GenerationTable × ℕ) => Nat.pair z.2.2.unpair.2 z.1) :=
    Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))) Primrec.fst
  have hr : PrimrecRel (fun x : ℕ => fun z : GenerationTable × ℕ =>
      generationAnswer z.1 (Nat.pair z.2.unpair.1 x) = 1 →
        generationAnswer z.1 (Nat.pair z.2.unpair.2 x) = 1) :=
    primrec_imp (Primrec.eq.comp (generationAnswer_primrec.comp (Primrec.fst.comp Primrec.snd) hcode₁)
      (Primrec.const 1))
    (Primrec.eq.comp (generationAnswer_primrec.comp (Primrec.fst.comp Primrec.snd) hcode₂)
      (Primrec.const 1))
  exact (hr.forall_mem_list.comp
    (Primrec.list_range.comp (Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))) Primrec.id).decide.to₂

def generationCritical (data : GenerationTable) (j : ℕ) : Bool :=
  generationConsistent data j && (List.range (j + 1)).all (fun k =>
    !(generationConsistent data k) || generationSubset data (Nat.pair j k))

theorem generationCritical_primrec : Primrec₂ generationCritical := by
  have hr : PrimrecRel (fun k : ℕ => fun z : GenerationTable × ℕ =>
      generationConsistent z.1 k = true → generationSubset z.1 (Nat.pair z.2 k) = true) :=
    primrec_imp (Primrec.eq.comp (generationConsistent_primrec.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.const true))
    (Primrec.eq.comp
      (generationSubset_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)) (Primrec.const true))
  have hall := hr.forall_mem_list.comp
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) Primrec.id
  apply (((Primrec.eq.comp (generationConsistent_primrec.comp Primrec.fst Primrec.snd)
    (Primrec.const true)).and hall).decide.to₂).of_eq
  intro data j
  apply Bool.eq_iff_iff.mpr
  simp [generationCritical, List.all_eq_true, Bool.or_eq_true, or_iff_not_imp_left]

def generationHasConsistent (data : GenerationTable) : Prop :=
  ∃ j ∈ List.range data.1.1.length, generationConsistent data j = true

instance (data : GenerationTable) : Decidable (generationHasConsistent data) := by
  unfold generationHasConsistent
  infer_instance

theorem generationHasConsistent_primrec : PrimrecPred generationHasConsistent := by
  have hr : PrimrecRel (fun j : ℕ => fun data : GenerationTable =>
      generationConsistent data j = true) :=
    Primrec.eq.comp (generationConsistent_primrec.comp Primrec.snd Primrec.fst) (Primrec.const true)
  exact hr.exists_mem_list.comp
    (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))) Primrec.id

def generationAccept (data : GenerationTable) : Prop :=
  let m := data.1.2.unpair.1
  let j := data.1.2.unpair.2
  0 < m ∧ j < data.1.1.length ∧ generationCritical data j = true ∧
    (∀ k ∈ List.range data.1.1.length, generationCritical data k = true → k ≤ j) ∧
    generationAnswer data (Nat.pair j (m - 1)) = 1 ∧
    (∀ x ∈ data.1.1, x < m - 1)

instance (data : GenerationTable) : Decidable (generationAccept data) := by
  unfold generationAccept
  infer_instance

theorem generationAccept_primrec : PrimrecPred generationAccept := by
  have hm : Primrec (fun data : GenerationTable => data.1.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))
  have hj : Primrec (fun data : GenerationTable => data.1.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))
  have hxs : Primrec (fun data : GenerationTable => data.1.1) := Primrec.fst.comp Primrec.fst
  have hmax : PrimrecRel (fun k : ℕ => fun data : GenerationTable =>
      generationCritical data k = true → k ≤ data.1.2.unpair.2) :=
    primrec_imp (Primrec.eq.comp (generationCritical_primrec.comp Primrec.snd Primrec.fst)
      (Primrec.const true)) (Primrec.nat_le.comp Primrec.fst (hj.comp Primrec.snd))
  have hfresh : PrimrecRel (fun x : ℕ => fun data : GenerationTable => x < data.1.2.unpair.1 - 1) :=
    Primrec.nat_lt.comp Primrec.fst (Primrec.pred.comp (hm.comp Primrec.snd))
  exact (Primrec.nat_lt.comp (Primrec.const 0) hm).and
    ((Primrec.nat_lt.comp hj (Primrec.list_length.comp hxs)).and
      ((Primrec.eq.comp (generationCritical_primrec.comp Primrec.id hj) (Primrec.const true)).and
        ((hmax.forall_mem_list.comp (Primrec.list_range.comp (Primrec.list_length.comp hxs)) Primrec.id).and
          ((Primrec.eq.comp
            (generationAnswer_primrec.comp Primrec.id (Primrec₂.natPair.comp hj (Primrec.pred.comp hm)))
            (Primrec.const 1)).and (hfresh.forall_mem_list.comp hxs Primrec.id)))))

def generationPost (data : GenerationTable) : Option ℕ :=
  if generationHasConsistent data then
    if generationAccept data then some (data.1.2.unpair.1 - 1) else none
  else some 0

theorem generationPost_computable : Computable generationPost := by
  exact (Primrec.ite generationHasConsistent_primrec
    (Primrec.ite generationAccept_primrec
      (Primrec.option_some.comp (Primrec.pred.comp (Primrec.fst.comp
        (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))) (Primrec.const none))
    (Primrec.const (some 0))).to_comp

def generationProgram : OracleSearchProgram where
  queries := generationQueries
  queries_primrec := generationQueries_primrec
  output := generationPost
  output_computable := generationPost_computable

def generationOracle (O : OracleFamily) (code : ℕ) : ℕ :=
  if O.query code.unpair.1 code.unpair.2 then 1 else 0

def generationData (O : OracleFamily) (xs : List ℕ) (q : ℕ) : GenerationTable :=
  ((xs, q), (generationQueries (xs, q)).map (generationOracle O))

theorem generationAnswer_correct (O : OracleFamily) (xs : List ℕ) (q j x : ℕ)
    (hj : j < xs.length) (hx : x ∈ xs ∨ x < q.unpair.1) :
    generationAnswer (generationData O xs q) (Nat.pair j x) = 1 ↔ x ∈ O.language j := by
  have hq : Nat.pair j x ∈ generationQueries (xs, q) := by
    apply List.mem_flatMap.mpr
    refine ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨x, ?_, rfl⟩⟩
    exact List.mem_append.mpr (hx.imp_right List.mem_range.mpr)
  simp only [generationAnswer, generationData, tableLookup_map _ _ _ hq]
  simp [generationOracle, O.query_spec]

theorem generationConsistent_correct (O : OracleFamily) (xs : List ℕ) (q j : ℕ)
    (hj : j < xs.length) :
    generationConsistent (generationData O xs q) j = true ↔
      Consistent O.language (listStream xs) xs.length j := by
  simp only [generationConsistent, decide_eq_true_eq]
  constructor
  · intro h x hx
    have hx' := (mem_sample_listStream xs x).mp hx
    exact (generationAnswer_correct O xs q j x hj (Or.inl hx')).mp (h x hx')
  · intro h x hx
    exact (generationAnswer_correct O xs q j x hj (Or.inl hx)).mpr
      (h ((mem_sample_listStream xs x).mpr hx))

theorem generationCritical_correct (O : OracleFamily) (xs : List ℕ) (q j : ℕ)
    (hj : j < xs.length) :
    generationCritical (generationData O xs q) j = true ↔
      FinitelyCritical O.language (listStream xs) xs.length q.unpair.1 j := by
  have heq : generationCritical (generationData O xs q) j = true ↔
      generationConsistent (generationData O xs q) j = true ∧
        ∀ k ∈ List.range (j + 1), generationConsistent (generationData O xs q) k = true →
          generationSubset (generationData O xs q) (Nat.pair j k) = true := by
    simp [generationCritical, List.all_eq_true, Bool.or_eq_true, or_iff_not_imp_left]
  rw [heq]
  rw [generationConsistent_correct O xs q j hj]
  constructor
  · rintro ⟨hc, hall⟩
    refine ⟨hc, ?_⟩
    intro k hkj hk x hxm hxj
    have hkt : k < xs.length := lt_of_le_of_lt hkj hj
    have hs := hall k (List.mem_range.mpr (Nat.lt_succ_of_le hkj))
      ((generationConsistent_correct O xs q k hkt).mpr hk)
    simp only [generationSubset, decide_eq_true_eq, Nat.unpair_pair] at hs
    apply (generationAnswer_correct O xs q k x hkt (Or.inr hxm)).mp
    exact hs x (List.mem_range.mpr hxm)
      ((generationAnswer_correct O xs q j x hj (Or.inr hxm)).mpr hxj)
  · rintro ⟨hc, hall⟩
    refine ⟨hc, ?_⟩
    intro k hk hcon
    have hkj : k ≤ j := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
    have hkt : k < xs.length := lt_of_le_of_lt hkj hj
    simp only [generationSubset, decide_eq_true_eq, Nat.unpair_pair]
    intro x hx hmem
    have hxm : x < q.unpair.1 := List.mem_range.mp hx
    exact (generationAnswer_correct O xs q k x hkt (Or.inr hxm)).mpr
      (hall k hkj ((generationConsistent_correct O xs q k hkt).mp hcon) x hxm
        ((generationAnswer_correct O xs q j x hj (Or.inr hxm)).mp hmem))

theorem generationHasConsistent_correct (O : OracleFamily) (xs : List ℕ) (q : ℕ) :
    generationHasConsistent (generationData O xs q) ↔
      O.HasConsistent (listStream xs) xs.length := by
  constructor
  · rintro ⟨j, hj, hc⟩
    have hjt : j < xs.length := List.mem_range.mp hj
    exact ⟨j, O.mem_consistentCandidates.mpr ⟨hjt, O.consistentAt_iff.mpr
      ((generationConsistent_correct O xs q j hjt).mp hc)⟩⟩
  · rintro ⟨j, hj⟩
    obtain ⟨hjt, hc⟩ := O.mem_consistentCandidates.mp hj
    exact ⟨j, List.mem_range.mpr hjt,
      (generationConsistent_correct O xs q j hjt).mpr (O.consistentAt_iff.mp hc)⟩

/-- P01's termination proof supplies a finite successful search stage. -/
theorem generationProgram_terminates (O : OracleFamily) :
    generationProgram.Terminates (generationOracle O) := by
  intro xs
  by_cases h : O.HasConsistent (listStream xs) xs.length
  · let m := O.roundCounter (listStream xs) xs.length h (freshStart xs)
    let j := O.selected (listStream xs) xs.length m h
    let q := Nat.pair m j
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (O.roundCounter_gt h _)
    have hj := O.selected_lt (m := m) h
    have hhas := (generationHasConsistent_correct O xs q).mpr h
    have hacc : generationAccept (generationData O xs q) := by
      unfold generationAccept
      simp only [generationData, q, Nat.unpair_pair]
      refine ⟨hm, hj, ?_, ?_, ?_, ?_⟩
      · apply (generationCritical_correct O xs q j hj).mpr
        simpa only [q, Nat.unpair_pair] using O.selected_finitelyCritical (m := m) h
      · intro k hk hc
        have hkt : k < xs.length := List.mem_range.mp hk
        apply O.selected_max h hkt
        apply O.finitelyCriticalAt_iff.mpr
        simpa only [q, Nat.unpair_pair] using (generationCritical_correct O xs q k hkt).mp hc
      · apply (generationAnswer_correct O xs q j (m - 1) hj
          (Or.inr (by simpa only [q, Nat.unpair_pair] using Nat.sub_one_lt (Nat.ne_of_gt hm)))).mpr
        exact (O.mem_finitePrefix.mp (O.roundCounter_output_mem_selectedPrefix h (freshStart xs))).2
      · intro x hx
        have hlo := lt_freshStart xs hx
        have hhi : freshStart xs ≤ m - 1 := Nat.le_sub_one_of_lt (O.roundCounter_gt h _)
        omega
    refine ⟨q, m - 1, ?_⟩
    change generationPost (generationData O xs q) = _
    rw [generationPost, if_pos hhas, if_pos hacc]
    simp only [generationData, q, Nat.unpair_pair]
  · refine ⟨0, 0, ?_⟩
    change generationPost (generationData O xs 0) = _
    simp only [generationPost, if_neg (fun hh => h ((generationHasConsistent_correct O xs 0).mp hh))]

def certifiedKM (O : OracleFamily) : List ℕ → ℕ :=
  generationProgram.run (generationOracle O) (generationProgram_terminates O)

theorem certifiedKM_finiteWitness (O : OracleFamily) :
    FiniteWitnessGenerates O.language (certifiedKM O) := by
  intro z
  obtain ⟨T, hT, hcritical⟩ := exists_KM_witness O.language z
  refine ⟨T, hT, z + 1, ?_⟩
  intro xs hn hxs hobs
  have hz := hcritical xs hxs hobs
  have hzt : z < xs.length := Nat.lt_of_succ_le hn
  have hhas : O.HasConsistent (listStream xs) xs.length :=
    ⟨z, O.mem_consistentCandidates.mpr ⟨hzt, O.consistentAt_iff.mpr hz.1⟩⟩
  obtain ⟨q, hq⟩ := generationProgram.run_stage (generationOracle O) (generationProgram_terminates O) xs
  change generationPost (generationData O xs q) = some (certifiedKM O xs) at hq
  rw [generationPost, if_pos ((generationHasConsistent_correct O xs q).mpr hhas)] at hq
  split at hq
  · rename_i ha
    obtain ⟨hm, hj, hfc, hmax, hout, hfresh⟩ := ha
    have hje : q.unpair.2 < xs.length := hj
    have hjfc := (generationCritical_correct O xs q q.unpair.2 hje).mp hfc
    have hzfc := critical_finitelyCritical hz q.unpair.1
    have hzj := hmax z (List.mem_range.mpr hzt)
      ((generationCritical_correct O xs q z hzt).mpr hzfc)
    have hy : q.unpair.1 - 1 ∈ O.language q.unpair.2 :=
      (generationAnswer_correct O xs q q.unpair.2 (q.unpair.1 - 1) hje
        (Or.inr (Nat.sub_one_lt (Nat.ne_of_gt hm)))).mp hout
    have he : certifiedKM O xs = q.unpair.1 - 1 := (Option.some.inj hq).symm
    rw [he]
    exact ⟨finitelyCritical_prefix_subset hzj hzfc hjfc _
      (Nat.sub_one_lt (Nat.ne_of_gt hm)) hy, fun hmem => (lt_irrefl _) (hfresh _ hmem)⟩
  · simp at hq

theorem certifiedKM_exponential (O : OracleFamily) :
    ExponentialGenerates O.language (deterministicIdentifier (certifiedKM O)) :=
  lemma_5_11 O.language _ (certifiedKM_finiteWitness O)

/-- Ordinary uniform computability when the membership procedure is computable. -/
theorem certifiedKM_computable (O : OracleFamily) (hO : Computable₂ O.query) :
    Computable (certifiedKM O) := by
  have ho : Computable (generationOracle O) :=
    (Computable.cond (hO.comp (Primrec.fst.comp Primrec.unpair).to_comp
      (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const 1) (Computable.const 0)).of_eq
      (fun code => by
        dsimp [generationOracle]
        cases O.query code.unpair.1 code.unpair.2 <;> simp)
  exact generationProgram.run_computable ho (generationProgram_terminates O)

/-- Theorem 3.2 in the source's infinite-language, membership-oracle model.
One fixed certified procedure has an exponential upper rate for every valid
target distribution. Nontriviality is needed only for the randomized lower
bound. The positive constants may depend on the witnessing distribution. -/
theorem theorem_3_2 (O : OracleFamily) :
    ExponentialGenerates O.language (deterministicIdentifier (certifiedKM O)) ∧
      (Computable₂ O.query → Computable (certifiedKM O)) ∧
      (GenerationNontrivial O.language → ∀ G : StatisticalGenerator,
        ∃ i p, ValidDistribution O.language i p ∧
          ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
            ∃ᶠ n : ℕ in Filter.atTop,
              D * Real.exp (-c * n) ≤ generationError O.language G p i n) :=
  ⟨certifiedKM_exponential O, certifiedKM_computable O, fun h G => lemma_5_10 O.language h G⟩

end GenLimit.HallucinationModeCollapse
