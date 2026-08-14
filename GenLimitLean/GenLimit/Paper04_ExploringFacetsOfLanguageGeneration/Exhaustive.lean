import GenLimit.Core.GenericGeneration
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Common.IntegerSweep
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.SymmDiff

/-!
# Charikar--Pabbaraju: exhaustive generation

This file formalizes the exhaustive-generation model from Definition 5 of
Charikar--Pabbaraju, *Exploring Facets of Language Generation in the Limit*,
arXiv:2411.15364v2, together with the complete separation in Example 9 and
the Weak Angluin condition used in Theorem 4.

At time `t`, an exhaustive algorithm receives the ordered prefix of length
`t` and returns a generator `ℕ → α`.  Its value at `0` is the ordinary online
output at that time.  If the input is stopped, the whole range of that same
generator is the paper's set `Z_{≥t}`.  The set `Z_{<t}` consists of the
ordinary outputs at the earlier times.

Paper time starts at one, whereas Lean time starts at zero.  This harmless
shift changes `G_t(1)` into `G_t(0)`.
-/

namespace GenLimit.CharikarPabbaraju

open scoped symmDiff

/-- The algorithmic object in Definition 5: each finite input history is
mapped to a generator for a possible generate-only continuation. -/
abbrev ExhaustiveAlgorithm (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → (ℕ → α)

/-- The generator returned by `A` after seeing the first `t` elements of
`stream`. -/
def generatorAt
    (A : ExhaustiveAlgorithm α) (stream : GenLimit.Generic.Stream α) (t : ℕ) : ℕ → α :=
  A t (fun i => stream i)

/-- The paper's online output `G_t(1)`, with zero-based generator index. -/
def exhaustiveOutput
    (A : ExhaustiveAlgorithm α) (stream : GenLimit.Generic.Stream α) (t : ℕ) : α :=
  generatorAt A stream t 0

/-- `Z_{<t}` in Definition 5: the distinct ordinary outputs before time `t`. -/
def generatedBefore
    (A : ExhaustiveAlgorithm α) (stream : GenLimit.Generic.Stream α) (t : ℕ) : Set α :=
  {x | ∃ s < t, exhaustiveOutput A stream s = x}

/-- `Z_{≥t}` in Definition 5: the range obtained by stopping the input at
time `t` and running the returned generator forever. -/
def generateOnly
    (A : ExhaustiveAlgorithm α) (stream : GenLimit.Generic.Stream α) (t : ℕ) : Set α :=
  Set.range (generatorAt A stream t)

/-- The two conclusions of Definition 5 at one time `t`.

The first conjunct is eventual validity up to finitely many hallucinations.
The second is exhaustive coverage by the input, past outputs, and the
generate-only continuation. -/
def ExhaustiveCorrectAt
    (A : ExhaustiveAlgorithm α) (K : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  (generateOnly A stream t \ K).Finite ∧
    K ⊆ (↑(GenLimit.Generic.sample stream t) : Set α) ∪
      generatedBefore A stream t ∪ generateOnly A stream t

/-- Definition 5: `A` exhaustively generates every target in `C`. -/
def IsExhaustiveGenerator
    (A : ExhaustiveAlgorithm α) (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ K, K ∈ C → ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream K →
      ∃ tStar : ℕ, ∀ t, tStar ≤ t → ExhaustiveCorrectAt A K stream t

/-- A collection is exhaustively generatable when it has an algorithm
satisfying Definition 5. -/
def ExhaustivelyGeneratable (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ A : ExhaustiveAlgorithm α, IsExhaustiveGenerator A C

theorem generatedBefore_finite
    (A : ExhaustiveAlgorithm α) (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    (generatedBefore A stream t).Finite := by
  let f : Fin t → α := fun s => exhaustiveOutput A stream s
  have hrange : generatedBefore A stream t = Set.range f := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, s.isLt, rfl⟩
  rw [hrange]
  exact Set.finite_range f

/-- The relaxed one-condition correctness notion in Remark 4. -/
def RelaxedExhaustiveCorrectAt
    (A : ExhaustiveAlgorithm α) (K : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  (generateOnly A stream t ∆ K).Finite

/-- The implication asserted in Remark 4: Definition 5 implies finite
symmetric difference between the generate-only range and the target. -/
theorem exhaustiveCorrectAt_implies_relaxed
    {A : ExhaustiveAlgorithm α} {K : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (h : ExhaustiveCorrectAt A K stream t) :
    RelaxedExhaustiveCorrectAt A K stream t := by
  rw [RelaxedExhaustiveCorrectAt, Set.symmDiff_def]
  apply h.1.union
  apply ((GenLimit.Generic.sample stream t).finite_toSet.union
    (generatedBefore_finite A stream t)).subset
  rintro x ⟨hxK, hxFuture⟩
  rcases h.2 hxK with hEarlier | hFuture
  · exact hEarlier
  · exact (hxFuture hFuture).elim

/-! ## Example 9: exhaustive generation is weaker than identification -/

/-- The collection `C = {ℤ} ∪ {ℤ \ {i} : i ∈ ℤ}` in Example 9. -/
def coSingletonIntegerClass : GenLimit.Generic.LanguageClass ℤ :=
  {K | K = Set.univ ∨ ∃ i : ℤ, K = Set.univ \ {i}}

theorem coSingletonIntegerClass_countable : coSingletonIntegerClass.Countable := by
  let f : Option ℤ → Set ℤ
    | none => Set.univ
    | some i => Set.univ \ {i}
  have hEq : coSingletonIntegerClass = Set.range f := by
    ext K
    constructor
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some i, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i => exact Or.inr ⟨i, rfl⟩
  rw [hEq]
  exact Set.countable_range f

/-- The finite tell-tale property inside Angluin's Condition with
Enumeration (condition (3)), separated from the effectiveness requirement
on the procedure producing the tell-tales. -/
def IsAngluinTellTale
    (C : GenLimit.Generic.LanguageClass α) (L : GenLimit.Generic.Language α)
    (T : Finset α) : Prop :=
  (↑T : Set α) ⊆ L ∧
    ∀ L', L' ∈ C → (↑T : Set α) ⊆ L' → ¬ L' ⊂ L

/-- The non-identifiability obstruction proved in Example 9: no finite set
is an Angluin tell-tale for `L∞ = ℤ`, even before imposing the computability
requirement from condition (3). -/
theorem coSingletonIntegerClass_no_telltale_for_univ (T : Finset ℤ) :
    ¬ IsAngluinTellTale coSingletonIntegerClass Set.univ T := by
  intro hTell
  obtain ⟨i, hiT⟩ := T.exists_notMem
  let L' : Set ℤ := Set.univ \ {i}
  have hL' : L' ∈ coSingletonIntegerClass := Or.inr ⟨i, rfl⟩
  have hTL' : (↑T : Set ℤ) ⊆ L' := by
    intro z hz
    simp only [L', Set.mem_diff, Set.mem_univ, true_and, Set.mem_singleton_iff]
    intro hzi
    exact hiT (hzi ▸ hz)
  have hproper : L' ⊂ (Set.univ : Set ℤ) := by
    apply Set.ssubset_univ_iff.mpr
    exact (Set.ne_univ_iff_exists_notMem L').2 ⟨i, by simp [L']⟩
  exact hTell.2 L' hL' hTL' hproper

/-- The input-oblivious exhaustive algorithm from Example 9.  At time `t`,
its generate-only mode enumerates the tail of the fixed integer sweep. -/
def integerSweepAlgorithm : ExhaustiveAlgorithm ℤ :=
  fun t _ n => integerSweep (t + n)

@[simp] theorem integerSweepAlgorithm_generatorAt
    (stream : GenLimit.Generic.Stream ℤ) (t n : ℕ) :
    generatorAt integerSweepAlgorithm stream t n = integerSweep (t + n) :=
  rfl

@[simp] theorem integerSweepAlgorithm_output
    (stream : GenLimit.Generic.Stream ℤ) (t : ℕ) :
    exhaustiveOutput integerSweepAlgorithm stream t = integerSweep t := by
  simp [exhaustiveOutput, generatorAt, integerSweepAlgorithm]

/-- At every stopping time, past online outputs together with the
generate-only tail cover every integer. -/
theorem integerSweep_past_union_future
    (stream : GenLimit.Generic.Stream ℤ) (t : ℕ) :
    generatedBefore integerSweepAlgorithm stream t ∪
      generateOnly integerSweepAlgorithm stream t = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  let n := Equiv.intEquivNat z
  by_cases hn : n < t
  · left
    exact ⟨n, hn, by simp [n]⟩
  · right
    refine ⟨n - t, ?_⟩
    simp only [integerSweepAlgorithm_generatorAt]
    rw [Nat.add_sub_of_le (Nat.le_of_not_gt hn)]
    exact integerSweep_equivIndex z

/-- For the punctured target `ℤ \ {i}`, the sweep makes no further error
once it has passed the unique index at which it emits `i`.  This is the
stronger property proved in Example 9, beyond Definition 5's allowance of
finitely many generate-only errors. -/
theorem integerSweep_future_subset_coSingleton
    (stream : GenLimit.Generic.Stream ℤ) (i : ℤ) {t : ℕ}
    (ht : Equiv.intEquivNat i < t) :
    generateOnly integerSweepAlgorithm stream t ⊆ Set.univ \ {i} := by
  rintro z ⟨n, rfl⟩
  simp only [integerSweepAlgorithm_generatorAt, Set.mem_diff, Set.mem_univ, true_and,
    Set.mem_singleton_iff]
  intro hEq
  have hIndex : t + n = Equiv.intEquivNat i := by
    apply integerSweep_bijective.injective
    simp [hEq, integerSweep_equivIndex]
  have : t ≤ Equiv.intEquivNat i := hIndex ▸ Nat.le_add_right t n
  exact (Nat.not_le_of_gt ht) this

theorem integerSweep_generateOnly_diff_coSingleton_finite
    (stream : GenLimit.Generic.Stream ℤ) (i : ℤ) (t : ℕ) :
    (generateOnly integerSweepAlgorithm stream t \ (Set.univ \ {i})).Finite := by
  apply (Set.finite_singleton i).subset
  intro z hz
  have hnot : z ∉ Set.univ \ ({i} : Set ℤ) := hz.2
  simpa using hnot

/-- The complete positive claim in Example 9: the non-identifiable
co-singleton collection can nevertheless be exhaustively generated. -/
theorem example9_exhaustivelyGeneratable :
    ExhaustivelyGeneratable coSingletonIntegerClass := by
  refine ⟨integerSweepAlgorithm, ?_⟩
  intro K hK stream _hPresents
  refine ⟨0, ?_⟩
  intro t _ht
  constructor
  · rcases hK with rfl | ⟨i, rfl⟩
    · simp
    · exact integerSweep_generateOnly_diff_coSingleton_finite stream i t
  · intro z hz
    have hcover : z ∈ generatedBefore integerSweepAlgorithm stream t ∪
        generateOnly integerSweepAlgorithm stream t := by
      rw [integerSweep_past_union_future stream t]
      trivial
    rcases hcover with hPast | hFuture
    · exact Or.inl (Or.inr hPast)
    · exact Or.inr hFuture

/-! ## The condition characterizing exhaustive generation -/

/-- Weak Angluin's Condition with Existence, equation (7). -/
def WeakAngluinExistence (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∃ T : Finset α,
    (↑T : Set α) ⊆ L ∧
      ∀ L', L' ∈ C → (↑T : Set α) ⊆ L' → L' ⊂ L → (L \ L').Finite

/-- The collection in Example 9 satisfies equation (7), as predicted by
the characterization in Theorem 4. -/
theorem coSingletonIntegerClass_weakAngluinExistence :
    WeakAngluinExistence coSingletonIntegerClass := by
  intro L hL
  refine ⟨∅, by simp, ?_⟩
  intro L' hL' _hEmpty hproper
  rcases hL with rfl | ⟨i, rfl⟩
  · rcases hL' with rfl | ⟨j, rfl⟩
    · exact (hproper.ne rfl).elim
    · have hEq : (Set.univ : Set ℤ) \ (Set.univ \ {j}) = {j} := by
        ext z
        simp
      rw [hEq]
      exact Set.finite_singleton j
  · rcases hL' with rfl | ⟨j, rfl⟩
    · have hEq : (Set.univ : Set ℤ) = Set.univ \ {i} :=
        Set.Subset.antisymm hproper.subset (Set.subset_univ _)
      exact (hproper.ne hEq).elim
    · have hsub : Set.univ \ {j} ⊆ Set.univ \ {i} := hproper.subset
      have hij : i = j := by
        by_contra hne
        have hiMem : i ∈ Set.univ \ ({j} : Set ℤ) := by simp [hne]
        have := hsub hiMem
        simp at this
      subst j
      exact (hproper.ne rfl).elim

end GenLimit.CharikarPabbaraju
