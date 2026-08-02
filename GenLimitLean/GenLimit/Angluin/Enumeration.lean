import GenLimit.Angluin.SemanticSufficiency

/-!
# From a finite enumeration to the semantic stage approximation

This file connects the literal stage-by-stage enumeration in Angluin's
Condition 1 to the finite approximation used by the kernel-checked semantic
correctness proof.  It proves all set-theoretic content of the sufficiency
direction starting from the source-faithful `ConditionOne` predicate.

What it does *not* yet prove is that `semanticLearner` is a `Computable`
function in Mathlib's partial-recursive model.  Thus the public conclusion is
explicitly semantic, rather than being mislabeled as the full effective
Theorem 1.
-/

namespace GenLimit.Angluin

/-- Content emitted strictly before stage `n`, with duplicate emissions
removed. -/
def stageContents
    (emit : ℕ → ℕ → Option ℕ) (i n : ℕ) : Finset ℕ :=
  ((List.range n).filterMap (emit i)).toFinset

theorem mem_stageContents_iff
    {emit : ℕ → ℕ → Option ℕ} {i n x : ℕ} :
    x ∈ stageContents emit i n ↔
      ∃ stage < n, emit i stage = some x := by
  simp [stageContents]

theorem stageContents_mono
    {emit : ℕ → ℕ → Option ℕ} {i n m : ℕ} (hnm : n ≤ m) :
    stageContents emit i n ⊆ stageContents emit i m := by
  intro x hx
  obtain ⟨stage, hstage, hout⟩ := mem_stageContents_iff.mp hx
  exact mem_stageContents_iff.mpr
    ⟨stage, lt_of_lt_of_le hstage hnm, hout⟩

/-- Finitely many emitted values all occur before one common stage. -/
theorem finite_emissions_bounded
    {emit : ℕ → ℕ → Option ℕ} {i : ℕ} (T : Finset ℕ)
    (hT : ∀ x, x ∈ T → ∃ stage, emit i stage = some x) :
    ∃ N, ∀ x, x ∈ T → ∃ stage < N, emit i stage = some x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x T hxT ih =>
      obtain ⟨stageX, hstageX⟩ := hT x (by simp)
      have hTail : ∀ y, y ∈ T → ∃ stage, emit i stage = some y := by
        intro y hy
        exact hT y (by simp [hy])
      obtain ⟨NT, hNT⟩ := ih hTail
      refine ⟨max (stageX + 1) NT, ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact ⟨stageX,
          lt_of_lt_of_le (Nat.lt_succ_self stageX) (Nat.le_max_left _ _),
          hstageX⟩
      · obtain ⟨stage, hstage, hout⟩ := hNT y hy
        exact ⟨stage, lt_of_lt_of_le hstage (Nat.le_max_right _ _), hout⟩

/-- A finite set-valued tell-tale enumeration yields the monotone, eventually
stable stage approximation used in Angluin's learner proof. -/
theorem tellTaleApproximation_of_enumeration
    {C : GenLimit.Generic.LanguageFamily ℕ}
    {emit : ℕ → ℕ → Option ℕ}
    (hTell : ∀ i,
      IsEnumeratedTellTale C i (enumeratedSet emit i)) :
    IsTellTaleApproximation C (stageContents emit) := by
  classical
  constructor
  · intro i n m hnm
    exact stageContents_mono hnm
  · intro i
    let hfinite : (enumeratedSet emit i).Finite := (hTell i).1
    let T : Finset ℕ := hfinite.toFinset
    have hTmem {x : ℕ} : x ∈ T ↔ x ∈ enumeratedSet emit i := by
      exact hfinite.mem_toFinset
    have hTtell : IsTellTale C i T := by
      constructor
      · intro x hx
        exact (hTell i).2.1 (hTmem.mp hx)
      · intro j hTj hji
        apply (hTell i).2.2 j
        · intro x hx
          exact hTj (hTmem.mpr hx)
        · exact hji
    have hEvery : ∀ x, x ∈ T → ∃ stage, emit i stage = some x := by
      intro x hx
      exact hTmem.mp hx
    obtain ⟨N, hN⟩ := finite_emissions_bounded T hEvery
    refine ⟨T, hTtell, N, ?_⟩
    intro n hn
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨stage, -, hout⟩ := mem_stageContents_iff.mp hx
      exact hTmem.mpr ⟨stage, hout⟩
    · intro x hx
      obtain ⟨stage, hstage, hout⟩ := hN x hx
      exact mem_stageContents_iff.mpr
        ⟨stage, lt_of_lt_of_le hstage hn, hout⟩

/-- Exact Condition 1 supplies the approximation needed by the semantic
stabilization proof.  The computability witness remains present in the
hypothesis even though this erasure lemma only uses its extensional output. -/
theorem ConditionOne.exists_tellTaleApproximation
    {F : EffectiveIndexedFamily} (h : ConditionOne F) :
    ∃ A : ℕ → ℕ → Finset ℕ,
      IsTellTaleApproximation F.language A := by
  obtain ⟨emit, -, hTell⟩ := h
  exact ⟨stageContents emit,
    tellTaleApproximation_of_enumeration hTell⟩

/-- Kernel-checked effective-hypothesis/semantic-conclusion slice of the
sufficiency half of Angluin's Theorem 1. -/
theorem ConditionOne.semantic_sufficiency
    {F : EffectiveIndexedFamily} (h : ConditionOne F) :
    ∃ M : SemanticIdentifier ℕ,
      SemanticallyIdentifies M F.language := by
  obtain ⟨A, hA⟩ := h.exists_tellTaleApproximation
  exact ⟨semanticLearner F.language A,
    semanticLearner_semanticallyIdentifies hA⟩

end GenLimit.Angluin
