import GenLimit.Core.Countable
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.SymmDiff
import Mathlib.Logic.Equiv.Nat

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

/-- The ordering `0, -1, 1, -2, 2, ...` used verbatim in Example 9. -/
def integerSweep : ℕ → ℤ := Equiv.intEquivNat.symm

theorem integerSweep_bijective : Function.Bijective integerSweep :=
  Equiv.intEquivNat.symm.bijective

@[simp] theorem integerSweep_equivIndex (z : ℤ) :
    integerSweep (Equiv.intEquivNat z) = z :=
  Equiv.intEquivNat.symm_apply_apply z

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

/-- The ray collection used in the proof of Theorem 3, expressed on `ℤ`:
`L∞ = ℤ` and `L_i = {-i, -i+1, ...}`. -/
def integerRayClass : GenLimit.Generic.LanguageClass ℤ :=
  {K | K = Set.univ ∨ ∃ i : ℤ, K = Set.Ici (-i)}

theorem integerRayClass_countable : integerRayClass.Countable := by
  let f : Option ℤ → Set ℤ
    | none => Set.univ
    | some i => Set.Ici (-i)
  have hEq : integerRayClass = Set.range f := by
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

private theorem exists_integer_lowerBound (T : Finset ℤ) :
    ∃ b : ℤ, ∀ z ∈ T, b ≤ z := by
  classical
  by_cases hT : T.Nonempty
  · refine ⟨T.min' hT, ?_⟩
    intro z hz
    exact Finset.min'_le T z hz
  · refine ⟨0, ?_⟩
    intro z hz
    exact (hT ⟨z, hz⟩).elim

theorem integer_Iio_infinite (b : ℤ) : (Set.Iio b).Infinite := by
  let f : ℕ → ℤ := fun n => b - (n : ℤ) - 1
  have hf : Function.Injective f := by
    intro m n h
    simp only [f] at h
    omega
  have hrange : Set.range f ⊆ Set.Iio b := by
    rintro z ⟨n, rfl⟩
    simp only [Set.mem_Iio, f]
    omega
  exact Set.infinite_range_of_injective hf |>.mono hrange

/-- Equation (8), specialized to `L∞`, for the concrete lower-bound
collection in Theorem 3: every finite positive sample is contained in a
proper ray whose complement in `ℤ` is infinite. -/
theorem integerRayClass_no_finite_weak_telltale (T : Finset ℤ) :
    ∃ L' ∈ integerRayClass,
      (↑T : Set ℤ) ⊆ L' ∧ L' ⊂ (Set.univ : Set ℤ) ∧
        ((Set.univ : Set ℤ) \ L').Infinite := by
  classical
  obtain ⟨b, hb⟩ := exists_integer_lowerBound T
  refine ⟨Set.Ici b, ?_, ?_, ?_, ?_⟩
  · right
    exact ⟨-b, by simp⟩
  · intro z hz
    exact hb z hz
  · apply Set.ssubset_univ_iff.mpr
    exact (Set.ne_univ_iff_exists_notMem (Set.Ici b)).2 ⟨b - 1, by simp⟩
  · simpa only [Set.diff_eq, Set.univ_inter, Set.compl_Ici] using integer_Iio_infinite b

/-- The exact Condition-(7) obstruction exhibited by the collection in the
proof of Theorem 3.  Completing Theorem 3 from this statement requires
Proposition 6.1's infinite adversarial diagonal construction. -/
theorem integerRayClass_not_weakAngluinExistence :
    ¬ WeakAngluinExistence integerRayClass := by
  intro hWeak
  obtain ⟨T, _hT, hTell⟩ := hWeak Set.univ (Or.inl rfl)
  obtain ⟨L', hL', hTL', hproper, hinfinite⟩ :=
    integerRayClass_no_finite_weak_telltale T
  exact hinfinite (hTell L' hL' hTL' hproper)

/-! ## Theorem 3: the adversarial ray diagonal -/

/-- The subfamily `L_i = {-i, -i+1, ...}` used by the diagonal proof,
indexed by natural-number phases. -/
def naturalIntegerRay (i : ℕ) : Set ℤ := Set.Ici (-(i : ℤ))

theorem naturalIntegerRay_mem_integerRayClass (i : ℕ) :
    naturalIntegerRay i ∈ integerRayClass := by
  right
  exact ⟨(i : ℤ), rfl⟩

/-- Extend a finite prefix by the canonical enumeration
`-i, -i+1, -i+2, ...` of `L_i`. -/
def rayPrefixExtension
    (base : GenLimit.Generic.Stream ℤ) (length i : ℕ) : GenLimit.Generic.Stream ℤ :=
  fun n => if n < length then base n else -(i : ℤ) + (n - length : ℕ)

theorem rayPrefixExtension_agrees
    (base : GenLimit.Generic.Stream ℤ) (length i n : ℕ) (hn : n < length) :
    rayPrefixExtension base length i n = base n := by
  simp [rayPrefixExtension, hn]

theorem rayPrefixExtension_mem
    (base : GenLimit.Generic.Stream ℤ) (length i n : ℕ)
    (hbase : ∀ m < length, base m ∈ naturalIntegerRay i) :
    rayPrefixExtension base length i n ∈ naturalIntegerRay i := by
  by_cases hn : n < length
  · simpa [rayPrefixExtension, hn] using hbase n hn
  · simp only [rayPrefixExtension, if_neg hn, naturalIntegerRay, Set.mem_Ici]
    omega

theorem rayPrefixExtension_presents
    (base : GenLimit.Generic.Stream ℤ) (length i : ℕ)
    (hbase : ∀ m < length, base m ∈ naturalIntegerRay i) :
    GenLimit.Generic.Presents (rayPrefixExtension base length i) (naturalIntegerRay i) := by
  apply Set.Subset.antisymm
  · rintro z ⟨n, rfl⟩
    exact rayPrefixExtension_mem base length i n hbase
  · intro z hz
    simp only [naturalIntegerRay, Set.mem_Ici] at hz
    have hnonneg : 0 ≤ z + (i : ℤ) := by omega
    let k := Int.toNat (z + (i : ℤ))
    refine ⟨length + k, ?_⟩
    have hnot : ¬ length + k < length := Nat.not_lt_of_ge (Nat.le_add_right length k)
    simp only [rayPrefixExtension, if_neg hnot, Nat.add_sub_cancel_left]
    dsimp only [k]
    rw [Int.toNat_of_nonneg hnonneg]
    omega

/-- A finite prefix ready for phase `i`; every committed input is in `L_i`. -/
structure RayDiagonalPrefix (i : ℕ) where
  length : ℕ
  stream : GenLimit.Generic.Stream ℤ
  mem_ray : ∀ n < length, stream n ∈ naturalIntegerRay i

/-- One completed phase of the proof of Theorem 3.  The next prefix extends
the old one, the stopping-time generator has only finitely many errors
outside `L_i`, and the phase appends both `-(i+1)` and `i`. -/
structure RayDiagonalStep
    (A : ExhaustiveAlgorithm ℤ) (i : ℕ) (P : RayDiagonalPrefix i) where
  endpoint : ℕ
  next : RayDiagonalPrefix (i + 1)
  next_length : next.length = endpoint + 2
  endpoint_lt : endpoint < next.length
  growth : P.length + 2 ≤ next.length
  agrees : ∀ n < P.length, next.stream n = P.stream n
  future_finite : (generateOnly A next.stream endpoint \ naturalIntegerRay i).Finite
  negative_value : next.stream endpoint = -((i : ℤ) + 1)
  nonnegative_value : next.stream (endpoint + 1) = (i : ℤ)

/-- Carry out one phase of the paper's diagonal construction. -/
noncomputable def buildRayDiagonalStep
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass)
    (i : ℕ) (P : RayDiagonalPrefix i) : RayDiagonalStep A i P := by
  classical
  let phaseStream := rayPrefixExtension P.stream P.length i
  have hPresents : GenLimit.Generic.Presents phaseStream (naturalIntegerRay i) :=
    rayPrefixExtension_presents P.stream P.length i P.mem_ray
  let hExists :=
    hA (naturalIntegerRay i) (naturalIntegerRay_mem_integerRayClass i) phaseStream hPresents
  let tStar := Classical.choose hExists
  have hAfter := Classical.choose_spec hExists
  let e := max tStar P.length
  have heStar : tStar ≤ e := Nat.le_max_left _ _
  have heLength : P.length ≤ e := Nat.le_max_right _ _
  have hfinitePhase :
      (generateOnly A phaseStream e \ naturalIntegerRay i).Finite :=
    (hAfter e heStar).1
  let nextStream : GenLimit.Generic.Stream ℤ := fun n =>
    if n < e then phaseStream n
    else if n = e then -((i : ℤ) + 1)
    else if n = e + 1 then (i : ℤ)
    else 0
  have hnextMem : ∀ n < e + 2, nextStream n ∈ naturalIntegerRay (i + 1) := by
    intro n hn
    by_cases hne : n < e
    · have hmem : phaseStream n ∈ naturalIntegerRay i := by
        simpa only [phaseStream] using
          rayPrefixExtension_mem P.stream P.length i n P.mem_ray
      simp only [nextStream, if_pos hne, naturalIntegerRay, Set.mem_Ici]
      simp only [naturalIntegerRay, Set.mem_Ici] at hmem
      omega
    · have hcases : n = e ∨ n = e + 1 := by omega
      rcases hcases with rfl | rfl
      · simp only [nextStream, lt_irrefl, if_false, naturalIntegerRay,
          Set.mem_Ici]
        omega
      · have hlt : ¬ e + 1 < e := by omega
        have hneEq : e + 1 ≠ e := by omega
        simp only [nextStream, hlt, hneEq, if_false, naturalIntegerRay,
          Set.mem_Ici]
        omega
  let next : RayDiagonalPrefix (i + 1) :=
    ⟨e + 2, nextStream, hnextMem⟩
  have hagrees : ∀ n < P.length, next.stream n = P.stream n := by
    intro n hn
    have hne : n < e := lt_of_lt_of_le hn heLength
    simp only [next, nextStream, if_pos hne]
    exact rayPrefixExtension_agrees P.stream P.length i n hn
  have hhist :
      (fun j : Fin e => next.stream j) = (fun j : Fin e => phaseStream j) := by
    funext j
    simp only [next, nextStream, if_pos j.isLt]
  have hfutureEq : generateOnly A next.stream e = generateOnly A phaseStream e := by
    simp only [generateOnly, generatorAt]
    rw [hhist]
  refine
    { endpoint := e
      next := next
      next_length := rfl
      endpoint_lt := by simp [next]
      growth := by simp only [next]; omega
      agrees := hagrees
      future_finite := ?_
      negative_value := by simp [next, nextStream]
      nonnegative_value := by simp [next, nextStream]
    }
  rwa [hfutureEq]

/-- The empty prefix before phase zero. -/
def initialRayDiagonalPrefix : RayDiagonalPrefix 0 where
  length := 0
  stream := fun _ => 0
  mem_ray := by simp

/-- The nested finite prefixes produced by the phases of Theorem 3. -/
noncomputable def rayDiagonalPrefix
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) :
    (i : ℕ) → RayDiagonalPrefix i
  | 0 => initialRayDiagonalPrefix
  | i + 1 => (buildRayDiagonalStep A hA i (rayDiagonalPrefix A hA i)).next

/-- The phase step associated with the recursively constructed prefix. -/
noncomputable def rayDiagonalStep
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    RayDiagonalStep A i (rayDiagonalPrefix A hA i) :=
  buildRayDiagonalStep A hA i (rayDiagonalPrefix A hA i)

@[simp] theorem rayDiagonalPrefix_succ
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    rayDiagonalPrefix A hA (i + 1) = (rayDiagonalStep A hA i).next := by
  rfl

theorem rayDiagonalPrefix_length_lowerBound
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    2 * i ≤ (rayDiagonalPrefix A hA i).length := by
  induction i with
  | zero => simp [rayDiagonalPrefix, initialRayDiagonalPrefix]
  | succ i ih =>
      rw [rayDiagonalPrefix_succ]
      have hgrowth := (rayDiagonalStep A hA i).growth
      omega

theorem rayDiagonalPrefix_length_mono
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    (rayDiagonalPrefix A hA i).length ≤ (rayDiagonalPrefix A hA (i + 1)).length := by
  rw [rayDiagonalPrefix_succ]
  exact (Nat.le_add_right _ 2).trans (rayDiagonalStep A hA i).growth

theorem rayDiagonalPrefix_length_mono_iterate
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass)
    (i k : ℕ) :
    (rayDiagonalPrefix A hA i).length ≤
      (rayDiagonalPrefix A hA (i + k)).length := by
  induction k with
  | zero => simp
  | succ k ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using rayDiagonalPrefix_length_mono A hA (i + k))

theorem rayDiagonalPrefix_agrees_iterate
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass)
    (i k n : ℕ) (hn : n < (rayDiagonalPrefix A hA i).length) :
    (rayDiagonalPrefix A hA (i + k)).stream n =
      (rayDiagonalPrefix A hA i).stream n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show i + (k + 1) = (i + k) + 1 by omega, rayDiagonalPrefix_succ]
      rw [(rayDiagonalStep A hA (i + k)).agrees n
        (lt_of_lt_of_le hn (rayDiagonalPrefix_length_mono_iterate A hA i k))]
      exact ih

theorem rayDiagonalPrefix_agrees_of_le
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass)
    {i j n : ℕ} (hij : i ≤ j) (hn : n < (rayDiagonalPrefix A hA i).length) :
    (rayDiagonalPrefix A hA j).stream n = (rayDiagonalPrefix A hA i).stream n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact rayDiagonalPrefix_agrees_iterate A hA i k n hn

/-- The limiting enumeration obtained by taking the diagonal of the nested
phase prefixes. -/
noncomputable def rayDiagonalStream
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) :
    GenLimit.Generic.Stream ℤ :=
  fun n => (rayDiagonalPrefix A hA (n + 1)).stream n

theorem rayDiagonalStream_agrees
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass)
    (i n : ℕ) (hn : n < (rayDiagonalPrefix A hA i).length) :
    rayDiagonalStream A hA n = (rayDiagonalPrefix A hA i).stream n := by
  unfold rayDiagonalStream
  by_cases hni : i ≤ n + 1
  · exact rayDiagonalPrefix_agrees_of_le A hA hni hn
  · have hle : n + 1 ≤ i := by omega
    symm
    apply rayDiagonalPrefix_agrees_of_le A hA hle
    have hbound := rayDiagonalPrefix_length_lowerBound A hA (n + 1)
    omega

theorem rayDiagonalStream_hits_negative
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    ∃ n, rayDiagonalStream A hA n = -((i : ℤ) + 1) := by
  let e := (rayDiagonalStep A hA i).endpoint
  refine ⟨e, ?_⟩
  rw [rayDiagonalStream_agrees A hA (i + 1) e]
  · rw [rayDiagonalPrefix_succ]
    exact (rayDiagonalStep A hA i).negative_value
  · rw [rayDiagonalPrefix_succ]
    exact (rayDiagonalStep A hA i).endpoint_lt

theorem rayDiagonalStream_hits_nonnegative
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    ∃ n, rayDiagonalStream A hA n = (i : ℤ) := by
  let e := (rayDiagonalStep A hA i).endpoint
  refine ⟨e + 1, ?_⟩
  rw [rayDiagonalStream_agrees A hA (i + 1) (e + 1)]
  · rw [rayDiagonalPrefix_succ]
    exact (rayDiagonalStep A hA i).nonnegative_value
  · rw [rayDiagonalPrefix_succ]
    rw [(rayDiagonalStep A hA i).next_length]
    omega

theorem rayDiagonalStream_presents_univ
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) :
    GenLimit.Generic.Presents (rayDiagonalStream A hA) Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  cases z with
  | ofNat i =>
      obtain ⟨n, hn⟩ := rayDiagonalStream_hits_nonnegative A hA i
      exact ⟨n, hn⟩
  | negSucc i =>
      obtain ⟨n, hn⟩ := rayDiagonalStream_hits_negative A hA i
      exact ⟨n, by simpa [Int.negSucc_eq, Nat.cast_succ] using hn⟩

/-- The final stream has the same history at phase `i`'s endpoint as the
finite prefix on which that phase established its validity invariant. -/
theorem rayDiagonalStream_generateOnly_at_endpoint
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    generateOnly A (rayDiagonalStream A hA) (rayDiagonalStep A hA i).endpoint =
      generateOnly A (rayDiagonalPrefix A hA (i + 1)).stream
        (rayDiagonalStep A hA i).endpoint := by
  simp only [generateOnly, generatorAt]
  congr 2
  funext j
  apply rayDiagonalStream_agrees A hA (i + 1) j
  rw [rayDiagonalPrefix_succ]
  exact lt_trans j.isLt (rayDiagonalStep A hA i).endpoint_lt

theorem rayDiagonal_endpoint_future_finite
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    (generateOnly A (rayDiagonalStream A hA) (rayDiagonalStep A hA i).endpoint \
      naturalIntegerRay i).Finite := by
  rw [rayDiagonalStream_generateOnly_at_endpoint A hA i]
  rw [rayDiagonalPrefix_succ]
  exact (rayDiagonalStep A hA i).future_finite

theorem rayDiagonal_endpoint_ge_index
    (A : ExhaustiveAlgorithm ℤ) (hA : IsExhaustiveGenerator A integerRayClass) (i : ℕ) :
    i ≤ (rayDiagonalStep A hA i).endpoint := by
  have hlen := rayDiagonalPrefix_length_lowerBound A hA i
  have hgrowth := (rayDiagonalStep A hA i).growth
  rw [(rayDiagonalStep A hA i).next_length] at hgrowth
  omega

/-- Semantic core of overview Theorem 3: the concrete countable ray
collection in the paper cannot satisfy Definition 5, even allowing arbitrary
set-theoretic algorithms.  This is stronger than the paper's computability
restriction. -/
theorem integerRayClass_not_exhaustivelyGeneratable :
    ¬ ExhaustivelyGeneratable integerRayClass := by
  rintro ⟨A, hA⟩
  let stream := rayDiagonalStream A hA
  have hPresents : GenLimit.Generic.Presents stream Set.univ :=
    rayDiagonalStream_presents_univ A hA
  obtain ⟨tInf, hInf⟩ := hA Set.univ (Or.inl rfl) stream hPresents
  let i := tInf
  let e := (rayDiagonalStep A hA i).endpoint
  have hei : i ≤ e := rayDiagonal_endpoint_ge_index A hA i
  have hcorrect := hInf e hei
  have hfuture : (generateOnly A stream e \ naturalIntegerRay i).Finite := by
    simpa [stream, e] using rayDiagonal_endpoint_future_finite A hA i
  have hleftInfinite :
      (((Set.univ : Set ℤ) \ naturalIntegerRay i) \
        (generateOnly A stream e \ naturalIntegerRay i)).Infinite := by
    have hIio : ((Set.univ : Set ℤ) \ naturalIntegerRay i).Infinite := by
      simpa only [naturalIntegerRay, Set.diff_eq, Set.univ_inter, Set.compl_Ici] using
        integer_Iio_infinite (-(i : ℤ))
    exact hIio.diff hfuture
  have hEarlierFinite :
      ((↑(GenLimit.Generic.sample stream e) : Set ℤ) ∪ generatedBefore A stream e).Finite :=
    (GenLimit.Generic.sample stream e).finite_toSet.union
      (generatedBefore_finite A stream e)
  apply hleftInfinite
  apply hEarlierFinite.subset
  intro z hz
  have hzCover := hcorrect.2 (show z ∈ (Set.univ : Set ℤ) from trivial)
  rcases hzCover with hEarlier | hFuture
  · exact hEarlier
  · exact (hz.2 ⟨hFuture, hz.1.2⟩).elim

/-- The countability-and-impossibility content of overview Theorem 3,
packaged existentially.  The paper's additional parenthetical claim that the
languages are regular depends on choosing and formalizing a concrete finite-
alphabet encoding of `ℤ`; the semantic lower bound itself is complete above. -/
theorem theorem3_countable_exhaustive_generation_lower_bound :
    ∃ C : GenLimit.Generic.LanguageClass ℤ,
      C.Countable ∧ ¬ ExhaustivelyGeneratable C :=
  ⟨integerRayClass, integerRayClass_countable,
    integerRayClass_not_exhaustivelyGeneratable⟩

end GenLimit.CharikarPabbaraju
