import GenLimit.Paper03_HallucinationAndModeCollapse.FiniteWitnessRates

/-!
# Exponential identification for two finite cases

A single bounded version-space learner handles finite-range families and
families of finite targets. Its operations are finite Boolean membership
queries. The proof uses a target-dependent witness excluding every candidate
which fails to contain the target, then finite-prefix tests remove the
finitely many earlier strict supersets.

This adapts Algorithm 8.2 of arXiv:2411.09642v3 to an indexed family. It also
repairs the proof of Proposition 3.12: the printed least-consistent learner
can get stuck on an earlier strict superset. We certify the semantic rate
and give a finite-query definition, but do not provide a Turing-code
computability theorem.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic

/-- Consistency with every observed positive example. -/
def sampleConsistent {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (xs : List ℕ) (j : ℕ) : Bool := xs.all (O.query j)

/-- On the first `n` domain points, the candidate is contained in every
consistent member of the bounded version space. -/
def prefixMinimal {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (xs : List ℕ) (j : ℕ) : Bool :=
  sampleConsistent O xs j && (List.range (xs.length + 1)).all (fun k =>
    !(sampleConsistent O xs k) || (List.range xs.length).all (fun x =>
      !(O.query j x) || O.query k x))

/-- A total learner using finitely many membership queries per sample. -/
def finiteVersionSpaceLearner {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (xs : List ℕ) : ℕ :=
  let candidates := (Finset.range (xs.length + 1)).filter (fun j => prefixMinimal O xs j)
  if h : candidates.Nonempty then candidates.min' h else 0

theorem sampleConsistent_iff {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (xs : List ℕ) (j : ℕ) :
    sampleConsistent O xs j = true ↔ ∀ x ∈ xs, x ∈ C j := by
  simp [sampleConsistent, O.query_spec]

theorem prefixMinimal_iff {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (xs : List ℕ) (j : ℕ) :
    prefixMinimal O xs j = true ↔
      (∀ x ∈ xs, x ∈ C j) ∧
      ∀ k ≤ xs.length, (∀ x ∈ xs, x ∈ C k) →
        ∀ x < xs.length, x ∈ C j → x ∈ C k := by
  simp [prefixMinimal, sampleConsistent_iff, O.query_spec,
    Nat.lt_succ_iff, or_iff_not_imp_left]

/-- A positive witness excludes all languages not containing the target.
This is stronger than an Angluin tell-tale and is used only for these two
finite cases. -/
def PositiveSubsetWitness (C : Generic.LanguageFamily ℕ) (i : ℕ) (T : Finset ℕ) : Prop :=
  (∀ x ∈ T, x ∈ C i) ∧ ∀ j, (∀ x ∈ T, x ∈ C j) → C i ⊆ C j

theorem finiteVersionSpace_finiteWitness {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C)
    (hC : ∀ i, ∃ T : Finset ℕ, PositiveSubsetWitness C i T) :
    FiniteWitnessIdentifies C (finiteVersionSpaceLearner O) := by
  classical
  intro i
  obtain ⟨T, hTi, hT⟩ := hC i
  let bad := (Finset.range (i + 1)).filter (fun j => C i ⊂ C j)
  have hex (j : {j // j ∈ bad}) : ∃ x, x ∈ C j.1 ∧ x ∉ C i :=
    Set.not_subset.mp (Finset.mem_filter.mp j.2).2.2
  let witness := fun j : {j // j ∈ bad} => Classical.choose (hex j)
  let N := max i ((bad.attach.image witness).sup id + 1)
  refine ⟨T, hTi, N, ?_⟩
  intro xs hn hxs hobs
  have hsup (k : ℕ) (hk : ∀ x ∈ xs, x ∈ C k) : C i ⊆ C k :=
    hT k (fun x hx => hk x (hobs x hx))
  have hi : prefixMinimal O xs i = true := by
    apply (prefixMinimal_iff O xs i).mpr
    exact ⟨hxs, fun k _ hk x _ hx => hsup k hk hx⟩
  let s := (Finset.range (xs.length + 1)).filter (fun j => prefixMinimal O xs j)
  have himem : i ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_max_left _ _).trans hn)), hi⟩
  have hs : s.Nonempty := ⟨i, himem⟩
  have hsel : finiteVersionSpaceLearner O xs = s.min' hs := by
    simp only [finiteVersionSpaceLearner, dif_pos hs, s]
  rw [hsel]
  let j := s.min' hs
  have hjle : j ≤ i := Finset.min'_le s i himem
  have hjmin := (prefixMinimal_iff O xs j).mp
    (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hsub : C i ⊆ C j := hsup j hjmin.1
  apply Set.Subset.antisymm _ hsub
  by_contra hnot
  have hjbad : j ∈ bad := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjle),
      ⟨hsub, hnot⟩⟩
  let b : {j // j ∈ bad} := ⟨j, hjbad⟩
  have hw := Classical.choose_spec (hex b)
  have hwmem : witness b ∈ bad.attach.image witness :=
    Finset.mem_image.mpr ⟨b, Finset.mem_attach _ _, rfl⟩
  have hwb : witness b ≤ (bad.attach.image witness).sup id := Finset.le_sup (f := id) hwmem
  have hwlt : witness b < xs.length :=
    (Nat.lt_succ_of_le hwb).trans_le ((le_max_right _ _).trans hn)
  exact hw.2 (hjmin.2 i ((le_max_left _ _).trans hn) hxs (witness b) hwlt hw.1)

theorem finiteRange_positiveSubsetWitness (C : Generic.LanguageFamily ℕ)
    (hRange : (Set.range C).Finite) (i : ℕ) :
    ∃ T : Finset ℕ, PositiveSubsetWitness C i T := by
  classical
  let bad := hRange.toFinset.filter (fun L => ¬C i ⊆ L)
  have hex (L : {L // L ∈ bad}) : ∃ x, x ∈ C i ∧ x ∉ L.1 :=
    Set.not_subset.mp (Finset.mem_filter.mp L.2).2
  let w := fun L : {L // L ∈ bad} => Classical.choose (hex L)
  refine ⟨bad.attach.image w, ?_, ?_⟩
  · intro x hx
    obtain ⟨L, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Classical.choose_spec (hex L)).1
  · intro j hj
    by_contra hnot
    have hb : C j ∈ bad := Finset.mem_filter.mpr ⟨by simp, hnot⟩
    let L : {L // L ∈ bad} := ⟨C j, hb⟩
    have hw := Classical.choose_spec (hex L)
    exact hw.2 (hj (w L) (Finset.mem_image.mpr ⟨L, Finset.mem_attach _ _, rfl⟩))

/-- Statistical upper-rate component of Proposition 3.11. The learner is fixed
before the distribution, and finite range permits infinite target languages. -/
theorem proposition_3_11_semantic (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (hRange : (Set.range C).Finite) :
    ExponentialIdentifies C (deterministicIdentifier (finiteVersionSpaceLearner O)) :=
  lemma_8_1 C _ (finiteVersionSpace_finiteWitness O (finiteRange_positiveSubsetWitness C hRange))

/-- Statistical upper-rate component of Proposition 3.12, using the repaired
bounded version-space learner rather than the printed least-consistent rule. -/
theorem proposition_3_12_semantic (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (hfinite : ∀ i, (C i).Finite) :
    ExponentialIdentifies C (deterministicIdentifier (finiteVersionSpaceLearner O)) := by
  apply lemma_8_1 C _ (finiteVersionSpace_finiteWitness O ?_)
  intro i
  refine ⟨(hfinite i).toFinset, ?_, ?_⟩
  · intro x hx; simpa using hx
  · intro j hj x hx
    exact hj x (by simpa using hx)

/-- A counterexample to the printed Proposition 3.12 proof: even after the
whole finite target is observed, index zero can be consistent and wrong.
As the least possible index, it would be chosen by the least-consistent rule. -/
theorem leastConsistent_counterexample :
    ∃ C : Generic.LanguageFamily ℕ, (∀ j, (C j).Finite) ∧
      ∃ xs : List ℕ, {x | x ∈ xs} = C 1 ∧
        C 0 ≠ C 1 ∧ (∀ x ∈ xs, x ∈ C 0) := by
  let C : Generic.LanguageFamily ℕ := fun j => if j = 0 then {0, 1} else {0}
  refine ⟨C, ?_, [0], ?_, ?_, ?_⟩
  · intro j; by_cases hj : j = 0 <;> simp [C, hj]
  · ext x; simp [C]
  · intro h
    have hmem : 1 ∈ C 0 := by simp [C]
    rw [h] at hmem
    simp [C] at hmem
  · simp [C]

end GenLimit.HallucinationModeCollapse
