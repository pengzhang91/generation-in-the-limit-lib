import GenLimit.Paper03_HallucinationAndModeCollapse.FiniteIdentification
import GenLimit.Support.OracleProcedureComputability
import GenLimit.Support.ComputableLists

/-!
# Certified membership-only computation for Propositions 3.11--3.12

The truth-table program queries the observed points and the first `n` domain
points in the first `n+1` candidate languages. Its output is proved equal to
the existing bounded version-space learner. Both exponential-rate proofs
therefore apply to this same certified program. Proposition 3.12 retains the
documented repair of the printed least-consistent construction.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.Support

private def booleanMembership (q : ℕ → ℕ → Bool) :
    GenLimit.MembershipOracle (fun j => {x | q j x = true}) where
  query := q
  query_spec := Iff.rfl

private theorem all_congr_mem {α : Type*} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.all f = xs.all g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro hf x hx; rw [← h x hx]; exact hf x hx
  · intro hg x hx; rw [h x hx]; exact hg x hx

private theorem prefixMinimal_query_congr {C D : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (Q : GenLimit.MembershipOracle D) (xs : List ℕ)
    (h : ∀ j ≤ xs.length, ∀ x, x ∈ xs ∨ x < xs.length → O.query j x = Q.query j x)
    (j : ℕ) (hj : j ≤ xs.length) : prefixMinimal O xs j = prefixMinimal Q xs j := by
  have hc (k : ℕ) (hk : k ≤ xs.length) : sampleConsistent O xs k = sampleConsistent Q xs k :=
    all_congr_mem xs _ _ (fun x hx => h k hk x (Or.inl hx))
  unfold prefixMinimal
  rw [hc j hj]
  congr 1
  apply all_congr_mem
  intro k hk
  have hk' : k ≤ xs.length := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
  rw [hc k hk']
  congr 1
  apply all_congr_mem
  intro x hx
  rw [h j hj x (Or.inr (List.mem_range.mp hx)), h k hk' x (Or.inr (List.mem_range.mp hx))]

theorem finiteVersionSpaceLearner_eq_firstTrue {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (xs : List ℕ) :
    finiteVersionSpaceLearner O xs = (firstTrue (prefixMinimal O) xs (xs.length + 1)).getD 0 := by
  classical
  let s := (Finset.range (xs.length + 1)).filter (fun j => prefixMinimal O xs j)
  by_cases hs : s.Nonempty
  · let j := s.min' hs
    have hj := Finset.mem_filter.mp (Finset.min'_mem s hs)
    have ht : prefixMinimal O xs j = true := by simpa [j] using hj.2
    have hb : j < xs.length + 1 := List.mem_range.mp (by simpa using hj.1)
    have hne : firstTrue (prefixMinimal O) xs (xs.length + 1) ≠ none := by
      intro hn
      have hf := (firstTrue_eq_none_iff _ _ _).mp hn j hb
      simp [ht] at hf
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hne
    have hsel : finiteVersionSpaceLearner O xs = j := by simp [finiteVersionSpaceLearner, s, hs, j]
    rw [hsel, hk, Option.getD_some]
    apply Nat.le_antisymm
    · exact Finset.min'_le s k (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (firstTrue_spec hk).1, (firstTrue_spec hk).2.1⟩)
    · exact firstTrue_le_of_true hk hb ht
  · have hn : firstTrue (prefixMinimal O) xs (xs.length + 1) = none := by
      apply (firstTrue_eq_none_iff _ _ _).mpr
      intro j hj
      apply Bool.eq_false_of_not_eq_true
      intro ht
      exact hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ht⟩⟩
    simp [finiteVersionSpaceLearner, s, hs, hn]

private theorem prefixPolicy_computable {α : Type*} [Primcodable α]
    (xs : α → List ℕ) (q : α → ℕ → ℕ → Bool) (hxs : Computable xs)
    (hq : Computable (fun z : α × (ℕ × ℕ) => q z.1 z.2.1 z.2.2)) :
    Computable₂ (fun a j => prefixMinimal (booleanMembership (q a)) (xs a) j) := by
  let D := α × ℕ
  let E := D × ℕ
  have hleft : Computable (fun z : E × ℕ => q z.1.1.1 z.1.1.2 z.2) :=
    Computable.comp (f := fun z : α × (ℕ × ℕ) => q z.1 z.2.1 z.2.2)
      (g := fun z : E × ℕ => (z.1.1.1, (z.1.1.2, z.2))) hq
      (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.pair (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd))
  have hright : Computable (fun z : E × ℕ => q z.1.1.1 z.1.2 z.2) :=
    Computable.comp (f := fun z : α × (ℕ × ℕ) => q z.1 z.2.1 z.2.2)
      (g := fun z : E × ℕ => (z.1.1.1, (z.1.2, z.2))) hq
      (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
  have hi : Computable (fun z : E => (List.range (xs z.1.1).length).all
      (fun x => !(q z.1.1 z.1.2 x) || q z.1.1 z.2 x)) :=
    ComputableLists.all (l := fun z : E => List.range (xs z.1.1).length)
      (f := fun z x => !(q z.1.1 z.1.2 x) || q z.1.1 z.2 x)
      (Primrec.list_range.to_comp.comp (Computable.list_length.comp
        (hxs.comp (Computable.fst.comp Computable.fst))))
      (Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hleft) hright).to₂
  have hc : Computable (fun z : E => (xs z.1.1).all (q z.1.1 z.2)) :=
    ComputableLists.all (l := fun z : E => xs z.1.1) (f := fun z x => q z.1.1 z.2 x)
      (hxs.comp (Computable.fst.comp Computable.fst)) hright.to₂
  have ho : Computable (fun z : D => (List.range ((xs z.1).length + 1)).all
      (fun k => !((xs z.1).all (q z.1 k)) ||
        (List.range (xs z.1).length).all (fun x => !(q z.1 z.2 x) || q z.1 k x))) :=
    ComputableLists.all (l := fun z : D => List.range ((xs z.1).length + 1))
      (f := fun z k => !((xs z.1).all (q z.1 k)) ||
        (List.range (xs z.1).length).all (fun x => !(q z.1 z.2 x) || q z.1 k x))
      ((Primrec.list_range.comp Primrec.succ).to_comp.comp
        (Computable.list_length.comp (hxs.comp Computable.fst)))
      (Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hc) hi).to₂
  have hs : Computable (fun z : D => (xs z.1).all (q z.1 z.2)) :=
    ComputableLists.all (l := fun z : D => xs z.1) (f := fun z x => q z.1 z.2 x)
      (hxs.comp Computable.fst)
      (Computable.comp (f := fun z : α × (ℕ × ℕ) => q z.1 z.2.1 z.2.2)
        (g := fun z : D × ℕ => (z.1.1, (z.1.2, z.2))) hq
        (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))).to₂
  exact (Primrec.and.to_comp.comp hs ho).to₂

def finiteIdentificationQueries (xs : List ℕ) : List ℕ :=
  (List.range (xs.length + 1)).flatMap (fun j => (xs ++ List.range xs.length).map (Nat.pair j))

theorem finiteIdentificationQueries_primrec : Primrec finiteIdentificationQueries :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
    (Primrec.list_map (Primrec.list_append.comp Primrec.fst
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)))
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂

def finiteTableQuery (data : List ℕ × List ℕ) (j x : ℕ) : Bool :=
  tableLookup (finiteIdentificationQueries data.1) data.2 (Nat.pair j x) == 1

theorem finiteTableQuery_computable :
    Computable (fun z : (List ℕ × List ℕ) × (ℕ × ℕ) => finiteTableQuery z.1 z.2.1 z.2.2) := by
  have hi : Computable (fun z : (List ℕ × List ℕ) × (ℕ × ℕ) =>
      (finiteIdentificationQueries z.1.1).idxOf (Nat.pair z.2.1 z.2.2)) :=
    Primrec.list_idxOf.to_comp.comp
      (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
      (finiteIdentificationQueries_primrec.to_comp.comp (Computable.fst.comp Computable.fst))
  exact Primrec.beq.to_comp.comp
    (Computable.option_getD (Computable.list_getElem?.comp (Computable.snd.comp Computable.fst) hi)
      (Computable.const 0)) (Computable.const 1)

def finiteIdentificationPost (data : List ℕ × List ℕ) : ℕ :=
  (firstTrue (fun data j => prefixMinimal (booleanMembership (finiteTableQuery data)) data.1 j)
    data (data.1.length + 1)).getD 0

theorem finiteIdentificationPost_computable : Computable finiteIdentificationPost :=
  Computable.option_getD
    ((firstTrue_computable (prefixPolicy_computable Prod.fst finiteTableQuery Computable.fst
      finiteTableQuery_computable)).comp Computable.id
      ((Primrec.succ.comp Primrec.list_length).to_comp.comp Computable.fst)) (Computable.const 0)

def finiteIdentificationProgram : TruthTableProgram where
  queries := finiteIdentificationQueries
  queries_primrec := finiteIdentificationQueries_primrec
  output := finiteIdentificationPost
  output_computable := finiteIdentificationPost_computable

def finiteMembershipOracle {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C) (code : ℕ) : ℕ :=
  bif O.query code.unpair.1 code.unpair.2 then 1 else 0

theorem finiteMembershipOracle_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (hO : Computable₂ O.query) : Computable (finiteMembershipOracle O) :=
  Computable.cond (hO.comp (Primrec.nat_iff.mpr Nat.Primrec.left).to_comp
    (Primrec.nat_iff.mpr Nat.Primrec.right).to_comp) (Computable.const 1) (Computable.const 0)

theorem finiteIdentificationProgram_eq_learner {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) :
    finiteIdentificationProgram.run (finiteMembershipOracle O) = finiteVersionSpaceLearner O := by
  funext xs
  let data := (xs, (finiteIdentificationQueries xs).map (finiteMembershipOracle O))
  have hq (j : ℕ) (hj : j ≤ xs.length) (x : ℕ) (hx : x ∈ xs ∨ x < xs.length) :
      finiteTableQuery data j x = O.query j x := by
    have hm : Nat.pair j x ∈ finiteIdentificationQueries xs := List.mem_flatMap.mpr
      ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj), List.mem_map.mpr
        ⟨x, List.mem_append.mpr (hx.imp_right List.mem_range.mpr), rfl⟩⟩
    unfold finiteTableQuery
    rw [tableLookup_map _ _ _ hm]
    cases hb : O.query j x <;> simp [finiteMembershipOracle, hb]
  have hp (j : ℕ) (hj : j < xs.length + 1) :
      prefixMinimal (booleanMembership (finiteTableQuery data)) xs j = prefixMinimal O xs j :=
    prefixMinimal_query_congr _ _ xs hq j (Nat.lt_succ_iff.mp hj)
  rw [finiteVersionSpaceLearner_eq_firstTrue]
  change (firstTrue _ data (xs.length + 1)).getD 0 = _
  congr 1
  have he (n : ℕ) (hn : n ≤ xs.length + 1) :
      firstTrue (fun data j => prefixMinimal (booleanMembership (finiteTableQuery data)) data.1 j) data n =
        firstTrue (prefixMinimal O) xs n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [firstTrue_succ, firstTrue_succ, ih (by omega), hp n (by omega)]
  exact he _ le_rfl

theorem finiteVersionSpaceLearner_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (hO : Computable₂ O.query) : Computable (finiteVersionSpaceLearner O) := by
  rw [← finiteIdentificationProgram_eq_learner O]
  exact finiteIdentificationProgram.run_computable (finiteMembershipOracle_computable O hO)

theorem proposition_3_11 (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (hRange : (Set.range C).Finite) :
    ExponentialIdentifies C (deterministicIdentifier (finiteVersionSpaceLearner O)) ∧
      (Computable₂ O.query → Computable (finiteVersionSpaceLearner O)) :=
  ⟨proposition_3_11_semantic C O hRange, finiteVersionSpaceLearner_computable O⟩

theorem proposition_3_12 (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (hfinite : ∀ i, (C i).Finite) :
    ExponentialIdentifies C (deterministicIdentifier (finiteVersionSpaceLearner O)) ∧
      (Computable₂ O.query → Computable (finiteVersionSpaceLearner O)) :=
  ⟨proposition_3_12_semantic C O hfinite, finiteVersionSpaceLearner_computable O⟩

end GenLimit.HallucinationModeCollapse
