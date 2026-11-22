import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.ExhaustiveCharacterization
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Core.OracleFamily

/-! # Proposition 6.2 with the finite-difference oracle

For a fixed training history only finitely many subset comparisons occur.
While enumerating the output, test these comparisons on longer and longer
prefixes. Each stabilizes. Revisit every proposed word infinitely often so
even small words enter the range after stabilization. The finitely many
premature outputs are allowed by exhaustive generation.
-/

namespace GenLimit.CharikarPabbaraju.DifferenceOracle

structure Oracle (F : LanguageFamily) where
  query : ℕ → ℕ → Bool
  spec : ∀ i j, query i j = true ↔ (F i \ F j).Finite

def prefixSubset (O : OracleFamily) (q i j : ℕ) : Bool :=
  decide (∀ x ∈ Finset.range q, O.query i x = true → O.query j x = true)

private theorem eventualComparisons (O : OracleFamily) (t : ℕ) :
    ∃ Q, ∀ q ≥ Q, ∀ i ≤ t, ∀ j ≤ t,
      prefixSubset O q i j = true ↔ O.language i ⊆ O.language j := by
  have single (i j : ℕ) : ∃ Q, ∀ q ≥ Q, prefixSubset O q i j = true ↔ O.language i ⊆ O.language j := by
    by_cases hij : O.language i ⊆ O.language j
    · refine ⟨0, fun q _ => ?_⟩
      simp only [prefixSubset, decide_eq_true_eq, O.query_spec, iff_true_intro hij, iff_true]
      exact fun x _ hx => hij hx
    · obtain ⟨x, hx, hn⟩ := Set.not_subset.mp hij
      refine ⟨x+1, fun q hq => ?_⟩
      simp only [prefixSubset, decide_eq_true_eq, Finset.mem_range, O.query_spec]
      exact ⟨fun h => (hn (h x hq hx)).elim, fun h => (hij h).elim⟩
  have inner (i) := Angluin.eventually_all_lt (k := t+1) (fun j _ => single i j)
  obtain ⟨Q, hQ⟩ := Angluin.eventually_all_lt (k := t+1) (fun i _ => inner i)
  exact ⟨Q, fun q hq i hi j hj => hQ q hq i (by omega) j (by omega)⟩

def consistent (O : OracleFamily) {t : ℕ} (xs : Fin t → ℕ) (i : ℕ) : Bool :=
  decide (∀ k, O.query i (xs k) = true)

private theorem consistent_spec (O : OracleFamily) {t : ℕ} (xs : Fin t → ℕ) (i : ℕ) :
    consistent O xs i = true ↔ ExhaustiveHistoryConsistent O.language xs i := by
  simp only [consistent, decide_eq_true_eq, O.query_spec]
  exact ⟨fun h _ hx => by obtain ⟨k,rfl⟩ := Generic.mem_sequenceSample_iff.mp hx; exact h k,
    fun h k => h (Generic.mem_sequenceSample_iff.mpr ⟨k,rfl⟩)⟩

def candidates (O : OracleFamily) {t : ℕ} (xs : Fin t → ℕ) (q : ℕ) : Finset ℕ :=
  (Finset.range (t+1)).filter (fun i : ℕ => consistent O xs i &&
    (List.range (i+1)).all (fun j => decide (consistent O xs j = true → prefixSubset O q i j = true)))

private theorem candidates_eventual (O : OracleFamily) {t : ℕ} (xs : Fin t → ℕ) :
    ∃ Q, ∀ q ≥ Q, candidates O xs q = exhaustiveCriticalIndices O.language xs := by
  obtain ⟨Q, hQ⟩ := eventualComparisons O t
  refine ⟨Q, fun q hq => ?_⟩
  ext i
  simp only [candidates, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, consistent_spec, mem_exhaustiveCriticalIndices, ExhaustiveHistoryCritical]
  exact ⟨fun ⟨hi, hc, hall⟩ => ⟨hi, hc, fun j hj hjc =>
    (hQ q hq i hi j (hj.trans hi)).mp (hall j hj hjc)⟩,
    fun ⟨hi, hc, hall⟩ => ⟨hi, hc, fun j hj hjc =>
    (hQ q hq i hi j (hj.trans hi)).mpr (hall j hj hjc)⟩⟩

def accepts (O : OracleFamily) (D : Oracle O.language) (cs : Finset ℕ) (x : ℕ) : Bool :=
  let f := Support.greatestCandidateWithFallback cs 0
  O.query f x || decide (∃ j ∈ cs, j ≤ f ∧ D.query j f = true ∧ O.query j x = true)

private theorem accepts_spec (O : OracleFamily) (D : Oracle O.language) {t : ℕ} (xs : Fin t → ℕ) (x : ℕ) :
    accepts O D (exhaustiveCriticalIndices O.language xs) x = true ↔ x ∈ exhaustiveOracleSet O.language xs := by
  let f := exhaustiveFocus O.language xs
  let cs := exhaustiveCriticalIndices O.language xs
  have hf : f ≤ t := by
    by_cases h : cs.Nonempty
    · exact (mem_exhaustiveCriticalIndices.mp (Support.greatestCandidateWithFallback_mem (fallback := 0) h)).1
    · simp [f, exhaustiveFocus, Support.greatestCandidateWithFallback, cs] at h ⊢
      split <;> simp_all
  change (O.query f x || decide (∃ j ∈ cs, j ≤ f ∧ D.query j f = true ∧ O.query j x = true)) = true ↔ _
  simp only [Bool.or_eq_true, decide_eq_true_eq, O.query_spec, D.spec, exhaustiveOracleSet,
    Set.mem_union, exhaustiveAugmentationExtra, Set.mem_iUnion, exists_prop, Finset.mem_coe, mem_exhaustiveAugmentationIndices]
  change (_ ∨ _) ↔ (x ∈ O.language f ∨ ∃ j, (j ≤ f ∧ _ ∧ _) ∧ x ∈ O.language j \ O.language f)
  constructor
  · rintro (hx | ⟨j, hj, hjf, hd, hx⟩)
    · exact Or.inl hx
    · by_cases h : x ∈ O.language f
      · exact Or.inl h
      · exact Or.inr ⟨j, ⟨hjf,(mem_exhaustiveCriticalIndices.mp hj).2,hd⟩,hx,h⟩
  · rintro (hx | ⟨j, ⟨hjf,hc,hd⟩, hx, _⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨j,mem_exhaustiveCriticalIndices.mpr ⟨hjf.trans hf,hc⟩,hjf,hd,hx⟩

/-- All loops are bounded by the training length or the generate-only step.
The fallback word contributes at most one extra element to the range. -/
def algorithm (O : OracleFamily) (D : Oracle O.language) : ExhaustiveAlgorithm ℕ :=
  fun _ xs n => if accepts O D (candidates O xs n) n.unpair.1 then n.unpair.1 else 0

theorem range_approximates (O : OracleFamily) (D : Oracle O.language) {t : ℕ} (xs : Fin t → ℕ) :
    let R := Set.range (algorithm O D t xs)
    let B := exhaustiveOracleSet O.language xs
    B ⊆ R ∧ (R \ B).Finite := by
  obtain ⟨Q, hQ⟩ := candidates_eventual O xs
  constructor
  · intro x hx
    refine ⟨Nat.pair x Q, ?_⟩
    simp [algorithm, hQ _ (Nat.right_le_pair x Q), (accepts_spec O D xs x).mpr hx]
  · apply (((Finset.range Q).image (algorithm O D t xs)).finite_toSet.union (Set.finite_singleton 0)).subset
    rintro x ⟨⟨n,rfl⟩, hbad⟩
    by_cases hn : n < Q
    · exact Or.inl (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩)
    · right
      have hcs := hQ n (Nat.le_of_not_gt hn)
      simp only [algorithm, hcs] at hbad ⊢
      split at hbad
      next h => exact (hbad ((accepts_spec O D xs _).mp h)).elim
      next h => simp [h]

/-- Proposition 6.2 and the subset-query elimination of Remark 5. -/
theorem proposition6_2 (O : OracleFamily) (D : Oracle O.language)
    (hw : WeakAngluinExistence (Set.range O.language)) :
    IsExhaustiveGenerator (algorithm O D) (Set.range O.language) := by
  rintro _ ⟨z, rfl⟩ s hp
  obtain ⟨T, hT⟩ := exhaustiveOracleSet_eventually_approximates_target hw hp
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hsub, hextra⟩ := range_approximates O D (fun i : Fin t => s i)
  obtain ⟨hfin, hcov⟩ := hT t ht
  constructor
  · apply (hextra.union hfin).subset
    intro x hx
    by_cases h : x ∈ exhaustiveOracleSet O.language (fun i : Fin t => s i)
    · exact Or.inr ⟨h,hx.2⟩
    · exact Or.inl ⟨hx.1,h⟩
  · exact fun x hx => Or.inr (hsub (hcov hx))

end GenLimit.CharikarPabbaraju.DifferenceOracle
