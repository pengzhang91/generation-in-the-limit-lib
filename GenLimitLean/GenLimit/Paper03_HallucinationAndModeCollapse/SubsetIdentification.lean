import GenLimit.Core.SubsetOracle
import GenLimit.Support.ComputableLastSearch
import GenLimit.Support.OracleProcedureComputability
import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalModel

/-!
# A certified last-critical identifier using subset queries

Source: Proposition 3.10 and Appendix B.1 of arXiv:2411.09642v3. At sample
length `n`, zero-based indices below `n` are considered. A candidate is
critical if it contains the sample and is contained in every earlier
sample-consistent candidate. The last critical index is returned, or index
zero if none exists. The program asks only finitely many membership and
subset queries. It does not read a tell-tale or its enumeration.

The query list is primitive recursive and its postprocessor is computable.
An ordinary computability certificate is supplied when both oracles are
computable; correctness of semantic oracles alone is not such a certificate.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.Support

def SubsetCritical (C : Generic.LanguageFamily ℕ) (xs : List ℕ) (j : ℕ) : Prop :=
  (∀ x ∈ xs, x ∈ C j) ∧ ∀ k < j, (∀ x ∈ xs, x ∈ C k) → C j ⊆ C k

def subsetMemberCode (j x : ℕ) : ℕ := Nat.pair 0 (Nat.pair j x)
def subsetInclusionCode (j k : ℕ) : ℕ := Nat.pair 1 (Nat.pair j k)

def subsetIdentificationQueries (xs : List ℕ) : List ℕ :=
  (List.range xs.length).flatMap (fun j =>
    (List.range j).map (subsetInclusionCode j) ++ xs.map (subsetMemberCode j))

theorem subsetIdentificationQueries_primrec : Primrec subsetIdentificationQueries := by
  have hs : Primrec₂ subsetInclusionCode :=
    (Primrec₂.natPair.comp (Primrec.const 1) (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).to₂
  have hm : Primrec₂ subsetMemberCode :=
    (Primrec₂.natPair.comp (Primrec.const 0) (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).to₂
  have hmem : Primrec (fun z : List ℕ × ℕ => z.1.map (subsetMemberCode z.2)) :=
    Primrec.list_map Primrec.fst (hm.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hsub : Primrec (fun z : List ℕ × ℕ => (List.range z.2).map (subsetInclusionCode z.2)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (hs.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length)
    (Primrec.list_append.comp hsub hmem).to₂

def subsetAnswerAt (data : List ℕ × List ℕ) (code : ℕ) : ℕ :=
  tableLookup (subsetIdentificationQueries data.1) data.2 code

theorem subsetAnswerAt_primrec : Primrec₂ subsetAnswerAt := by
  have hi : Primrec (fun z : (List ℕ × List ℕ) × ℕ =>
      (subsetIdentificationQueries z.1.1).idxOf z.2) :=
    Primrec.list_idxOf.comp Primrec.snd
      (subsetIdentificationQueries_primrec.comp (Primrec.fst.comp Primrec.fst))
  exact (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) hi) (Primrec.const 0)).to₂

def subsetTableConsistent (data : List ℕ × List ℕ) (j : ℕ) : Bool :=
  decide (∀ x ∈ data.1, subsetAnswerAt data (subsetMemberCode j x) = 1)

theorem subsetTableConsistent_primrec : Primrec₂ subsetTableConsistent := by
  let D := List ℕ × List ℕ
  have hr : PrimrecRel (fun x : ℕ => fun z : D × ℕ =>
      subsetAnswerAt z.1 (subsetMemberCode z.2 x) = 1) :=
    Primrec.eq.comp
      (subsetAnswerAt_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec₂.natPair.comp (Primrec.const 0)
          (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)))
      (Primrec.const 1)
  exact (hr.forall_mem_list.comp (Primrec.fst.comp Primrec.fst) Primrec.id).decide.to₂

def subsetTableCritical (data : List ℕ × List ℕ) (j : ℕ) : Bool :=
  subsetTableConsistent data j && boundedAll (fun z : (List ℕ × List ℕ) × ℕ => fun k =>
    !(subsetTableConsistent z.1 k) || (subsetAnswerAt z.1 (subsetInclusionCode z.2 k) == 1)) (data, j) j

theorem subsetTableCritical_computable : Computable₂ subsetTableCritical := by
  let D := (List ℕ × List ℕ) × ℕ
  have hc : Computable (fun z : D × ℕ => subsetTableConsistent z.1.1 z.2) :=
    subsetTableConsistent_primrec.to_comp.comp (Computable.fst.comp Computable.fst) Computable.snd
  have hs : Computable (fun z : D × ℕ =>
      subsetAnswerAt z.1.1 (subsetInclusionCode z.1.2 z.2) == 1) :=
    Primrec.beq.to_comp.comp
      (subsetAnswerAt_primrec.to_comp.comp (Computable.fst.comp Computable.fst)
        ((Primrec₂.natPair.comp (Primrec.const 1)
          (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to_comp))
      (Computable.const 1)
  have hp : Computable₂ (fun z : D => fun k =>
      !(subsetTableConsistent z.1 k) || (subsetAnswerAt z.1 (subsetInclusionCode z.2 k) == 1)) :=
    (Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hc) hs).to₂
  exact (Primrec.and.to_comp.comp subsetTableConsistent_primrec.to_comp
    ((boundedAll_computable hp).comp Computable.id Computable.snd)).to₂

def subsetIdentificationPost (data : List ℕ × List ℕ) : ℕ :=
  (lastTrue subsetTableCritical data data.1.length).getD 0

theorem subsetIdentificationPost_computable : Computable subsetIdentificationPost :=
  Computable.option_getD
    ((lastTrue_computable subsetTableCritical_computable).comp Computable.id
      (Computable.list_length.comp Computable.fst)) (Computable.const 0)

def subsetIdentificationProgram : TruthTableProgram where
  queries := subsetIdentificationQueries
  queries_primrec := subsetIdentificationQueries_primrec
  output := subsetIdentificationPost
  output_computable := subsetIdentificationPost_computable

def subsetIdentificationOracle {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (S : GenLimit.SubsetOracle C) (code : ℕ) : ℕ :=
  bif code.unpair.1 == 0 then
    (bif O.query code.unpair.2.unpair.1 code.unpair.2.unpair.2 then 1 else 0)
  else bif code.unpair.1 == 1 then
    (bif S.query code.unpair.2.unpair.1 code.unpair.2.unpair.2 then 1 else 0)
  else 0

theorem subsetIdentificationOracle_member {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C) (j x : ℕ) :
    subsetIdentificationOracle O S (subsetMemberCode j x) = 1 ↔ x ∈ C j := by
  have h : O.query j x = true ↔ x ∈ C j := O.query_spec
  cases hb : O.query j x <;> simpa [subsetIdentificationOracle, subsetMemberCode, hb] using h

theorem subsetIdentificationOracle_subset {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C) (j k : ℕ) :
    subsetIdentificationOracle O S (subsetInclusionCode j k) = 1 ↔ C j ⊆ C k := by
  have h := S.query_spec j k
  cases hb : S.query j k <;> simpa [subsetIdentificationOracle, subsetInclusionCode, hb] using h

theorem subsetIdentificationOracle_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C)
    (hO : Computable₂ O.query) (hS : Computable₂ S.query) : Computable (subsetIdentificationOracle O S) := by
  have hl : Computable (fun n : ℕ => n.unpair.1) := (Primrec.nat_iff.mpr Nat.Primrec.left).to_comp
  have hr : Computable (fun n : ℕ => n.unpair.2) := (Primrec.nat_iff.mpr Nat.Primrec.right).to_comp
  have hm := Computable.cond (hO.comp (hl.comp hr) (hr.comp hr)) (Computable.const 1) (Computable.const 0)
  have hs := Computable.cond (hS.comp (hl.comp hr) (hr.comp hr)) (Computable.const 1) (Computable.const 0)
  exact Computable.cond (Primrec.beq.to_comp.comp hl (Computable.const 0)) hm
    (Computable.cond (Primrec.beq.to_comp.comp hl (Computable.const 1)) hs (Computable.const 0))

def subsetIdentifier {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (S : GenLimit.SubsetOracle C) : GenLimit.Learner ℕ ℕ :=
  subsetIdentificationProgram.run (subsetIdentificationOracle O S)

theorem subsetIdentifier_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C)
    (hO : Computable₂ O.query) (hS : Computable₂ S.query) : Computable (subsetIdentifier O S) :=
  subsetIdentificationProgram.run_computable (subsetIdentificationOracle_computable O S hO hS)

theorem subsetTableConsistent_iff {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C)
    (xs : List ℕ) (j : ℕ) (hj : j < xs.length) :
    subsetTableConsistent (xs, (subsetIdentificationQueries xs).map (subsetIdentificationOracle O S)) j = true ↔
      ∀ x ∈ xs, x ∈ C j := by
  have hq (x : ℕ) (hx : x ∈ xs) : subsetMemberCode j x ∈ subsetIdentificationQueries xs :=
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
      List.mem_append_right _ (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩
  have hm (x : ℕ) (hx : x ∈ xs) : subsetAnswerAt
      (xs, (subsetIdentificationQueries xs).map (subsetIdentificationOracle O S)) (subsetMemberCode j x) = 1 ↔
      x ∈ C j := by
    rw [subsetAnswerAt, tableLookup_map _ _ _ (hq x hx)]
    exact subsetIdentificationOracle_member O S j x
  simp only [subsetTableConsistent, decide_eq_true_eq]
  exact ⟨fun h x hx => (hm x hx).mp (h x hx), fun h x hx => (hm x hx).mpr (h x hx)⟩

theorem subsetTableCritical_iff {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C)
    (xs : List ℕ) (j : ℕ) (hj : j < xs.length) :
    subsetTableCritical (xs, (subsetIdentificationQueries xs).map (subsetIdentificationOracle O S)) j = true ↔
      SubsetCritical C xs j := by
  let data := (xs, (subsetIdentificationQueries xs).map (subsetIdentificationOracle O S))
  have hq (k : ℕ) (hk : k < j) : subsetInclusionCode j k ∈ subsetIdentificationQueries xs :=
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
      List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)⟩
  have hs (k : ℕ) (hk : k < j) : subsetAnswerAt data (subsetInclusionCode j k) = 1 ↔ C j ⊆ C k := by
    rw [subsetAnswerAt, tableLookup_map _ _ _ (hq k hk)]
    exact subsetIdentificationOracle_subset O S j k
  change (subsetTableConsistent data j && _) = true ↔ _
  rw [Bool.and_eq_true, boundedAll_eq_true_iff]
  constructor
  · rintro ⟨hcons, hcrit⟩
    refine ⟨(subsetTableConsistent_iff O S xs j hj).mp hcons, ?_⟩
    intro k hk hkc
    have hc := (subsetTableConsistent_iff O S xs k (hk.trans hj)).mpr hkc
    apply (hs k hk).mp
    have hh := hcrit k hk
    simpa [hc] using hh
  · rintro ⟨hcons, hcrit⟩
    refine ⟨(subsetTableConsistent_iff O S xs j hj).mpr hcons, ?_⟩
    intro k hk
    by_cases hc : subsetTableConsistent data k = true
    · have hkc := (subsetTableConsistent_iff O S xs k (hk.trans hj)).mp hc
      have hincl := (hs k hk).mpr (hcrit k hk hkc)
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
      exact Or.inr hincl
    · simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
      exact Or.inl (Bool.eq_false_of_not_eq_true hc)

end GenLimit.HallucinationModeCollapse
