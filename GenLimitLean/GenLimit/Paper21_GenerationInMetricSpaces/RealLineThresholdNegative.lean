import GenLimit.Paper21_GenerationInMetricSpaces.RealLineThreshold
import GenLimit.Paper21_GenerationInMetricSpaces.ScaleMonotonicity
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin

/-!
# Example 4.5: the infinite-row negative direction

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1, Example 4.5 and
Appendix C.2.

This file proves the negative half of Example 4.5 directly.  Against an
alleged `(1, 1/2)` limit generator, phase `n` temporarily presents the
language associated with the `(n+1)`st odd prime.  The generator is forced
to output from that prime's protected support.  The limiting presentation
instead belongs to the first odd prime and contains exactly the even
row-points exposed during the phases.  Distinct odd-prime supports are
disjoint, so every forced output is either invalid for the limiting target
or already non-novel.

The proof does not assert the printed general Lemma C.3.  Its hypotheses
only cover the chosen target by the displayed row points; they do not state
that those points belong to the target, although the proof feeds them to the
generator as a target-valued presentation.  The concrete construction below
checks this missing membership property at every phase.
-/

namespace GenLimit.MetricSpaces
namespace RealLineThreshold

noncomputable section

/-- The increasing enumeration `3, 5, 7, ...` of odd primes. -/
def diagonalOddPrime (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i + 1)

theorem diagonalOddPrime_prime (i : ℕ) :
    (diagonalOddPrime i).Prime := by
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (i + 1)

theorem diagonalOddPrime_strictMono :
    StrictMono diagonalOddPrime := by
  intro i j hij
  exact
    (Nat.nth_strictMono Nat.infinite_setOf_prime)
      (Nat.add_lt_add_right hij 1)

theorem diagonalOddPrime_two_lt (i : ℕ) :
    2 < diagonalOddPrime i := by
  have h :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime)
      (show 0 < i + 1 by omega)
  simpa [diagonalOddPrime, Nat.nth_prime_zero_eq_two] using h

theorem diagonalOddPrime_odd (i : ℕ) :
    Odd (diagonalOddPrime i) :=
  (diagonalOddPrime_prime i).odd_of_ne_two
    (ne_of_gt (diagonalOddPrime_two_lt i))

theorem diagonalOddPrime_injective :
    Function.Injective diagonalOddPrime :=
  diagonalOddPrime_strictMono.injective

/-- Row `i` consists of the predecessor points `pᵢ^(j+1) - 1`. -/
def diagonalRow (i j : ℕ) : ℝ :=
  ((diagonalOddPrime i ^ (j + 1) - 1 : ℕ) : ℝ)

theorem diagonalRow_mem_support (i j : ℕ) :
    diagonalRow i j ∈ primePairSupport (diagonalOddPrime i) := by
  exact ⟨j, Or.inr rfl⟩

theorem diagonalRow_mem_positiveEvenIntegers (i j : ℕ) :
    diagonalRow i j ∈ positiveEvenIntegers := by
  have hodd :
      Odd (diagonalOddPrime i ^ (j + 1)) :=
    (diagonalOddPrime_odd i).pow
  have heven :
      Even (diagonalOddPrime i ^ (j + 1) - 1) :=
    hodd.tsub_odd odd_one
  have hpow :
      1 < diagonalOddPrime i ^ (j + 1) := by
    exact one_lt_pow₀
      (lt_trans Nat.one_lt_two (diagonalOddPrime_two_lt i))
      (Nat.succ_ne_zero j)
  rcases heven with ⟨k, hk⟩
  have hkpos : 0 < k := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hkpos)
  refine ⟨m, ?_⟩
  dsimp [diagonalRow]
  exact_mod_cast (show
    diagonalOddPrime i ^ (j + 1) - 1 =
      2 * (m + 1) by omega)

/-- Supports associated with distinct odd primes are disjoint. -/
theorem primePairSupport_disjoint_of_distinct_primes
    {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q)
    (hpq : p ≠ q) :
    Disjoint (primePairSupport p) (primePairSupport q) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  obtain ⟨m, hm | hm⟩ := hxp
  · obtain ⟨n, hn | hn⟩ := hxq
    · have hpowers :
          p ^ (m + 1) = q ^ (n + 1) := by
        exact_mod_cast hm.symm.trans hn
      exact hpq (Nat.Prime.pow_inj hp hq hpowers).1
    · have heq :
          p ^ (m + 1) = q ^ (n + 1) - 1 := by
        exact_mod_cast hm.symm.trans hn
      have hleft : Odd (p ^ (m + 1)) := hpodd.pow
      have hright : Even (q ^ (n + 1) - 1) :=
        hqodd.pow.tsub_odd odd_one
      rw [heq] at hleft
      exact (Nat.not_even_iff_odd.mpr hleft) hright
  · obtain ⟨n, hn | hn⟩ := hxq
    · have heq :
          p ^ (m + 1) - 1 = q ^ (n + 1) := by
        exact_mod_cast hm.symm.trans hn
      have hleft : Even (p ^ (m + 1) - 1) :=
        hpodd.pow.tsub_odd odd_one
      have hright : Odd (q ^ (n + 1)) := hqodd.pow
      rw [heq] at hleft
      exact (Nat.not_even_iff_odd.mpr hright) hleft
    · have hpred :
          p ^ (m + 1) - 1 = q ^ (n + 1) - 1 := by
        exact_mod_cast hm.symm.trans hn
      have hpPos : 0 < p ^ (m + 1) :=
        pow_pos hp.pos (m + 1)
      have hqPos : 0 < q ^ (n + 1) :=
        pow_pos hq.pos (n + 1)
      have hpowers :
          p ^ (m + 1) = q ^ (n + 1) := by
        omega
      exact hpq (Nat.Prime.pow_inj hp hq hpowers).1

theorem diagonalSupports_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint
      (primePairSupport (diagonalOddPrime i))
      (primePairSupport (diagonalOddPrime j)) := by
  exact primePairSupport_disjoint_of_distinct_primes
    (diagonalOddPrime_prime i)
    (diagonalOddPrime_prime j)
    (diagonalOddPrime_odd i)
    (diagonalOddPrime_odd j)
    (fun h ↦ hij (diagonalOddPrime_injective h))

/-! ## Finite histories and temporary row presentations -/

/-- Values occurring in a finite history. -/
def listRange (xs : List α) : Set α :=
  Set.range xs.get

theorem mem_listRange_iff {xs : List α} {x : α} :
    x ∈ listRange xs ↔ x ∈ xs := by
  constructor
  · rintro ⟨i, rfl⟩
    exact List.get_mem xs i
  · intro hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    exact ⟨i, hi⟩

/-- Prefix a finite history to an infinite tail. -/
def prependListStream
    (xs : List α) (tail : GenLimit.Generic.Stream α) :
    GenLimit.Generic.Stream α :=
  fun n ↦ if h : n < xs.length then xs.get ⟨n, h⟩
    else tail (n - xs.length)

theorem prependListStream_of_lt
    (xs : List α) (tail : GenLimit.Generic.Stream α)
    {n : ℕ} (hn : n < xs.length) :
    prependListStream xs tail n = xs.get ⟨n, hn⟩ := by
  simp [prependListStream, hn]

theorem prependListStream_add
    (xs : List α) (tail : GenLimit.Generic.Stream α) (n : ℕ) :
    prependListStream xs tail (xs.length + n) = tail n := by
  simp [prependListStream]

/-- The literal list of the first `t` stream values. -/
def finiteStreamPrefix
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : List α :=
  List.ofFn fun i : Fin t ↦ stream i

@[simp] theorem finiteStreamPrefix_length
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    (finiteStreamPrefix stream t).length = t := by
  simp [finiteStreamPrefix]

@[simp] theorem finiteStreamPrefix_get
    (stream : GenLimit.Generic.Stream α) (t : ℕ) (i : Fin t) :
    (finiteStreamPrefix stream t).get
        ⟨i, by simp [finiteStreamPrefix]⟩ =
      stream i := by
  simp [finiteStreamPrefix]

/-- A prefix generator has the same output on streams agreeing throughout
the observed prefix. -/
theorem output_eq_of_eq_on_prefix
    (gen : GenLimit.Generic.Generator α)
    {stream₁ stream₂ : GenLimit.Generic.Stream α} {t : ℕ}
    (h : ∀ i : Fin t, stream₁ i = stream₂ i) :
    GenLimit.Generic.output gen stream₁ t =
      GenLimit.Generic.output gen stream₂ t := by
  unfold GenLimit.Generic.output
  congr 1
  funext i
  exact h i

/-- Every point of `Aₚ` is within radius one of the predecessor row
`p^(j+1)-1`. -/
theorem primePairSupport_subset_row_neighborhood
    {p : ℕ} (hp : 0 < p) :
    primePairSupport p ⊆
      closedNeighborhood realDistance
        (Set.range fun j : ℕ ↦
          (((p ^ (j + 1) - 1 : ℕ) : ℕ) : ℝ))
        1 := by
  intro x hx η hη
  obtain ⟨j, hj | hj⟩ := hx
  · refine
      ⟨(((p ^ (j + 1) - 1 : ℕ) : ℕ) : ℝ),
        ⟨j, rfl⟩, ?_⟩
    rw [hj]
    have hpow : 0 < p ^ (j + 1) :=
      pow_pos hp (j + 1)
    rw [realDistance, Nat.cast_sub (by omega : 1 ≤ p ^ (j + 1))]
    norm_num
    exact hη
  · refine
      ⟨(((p ^ (j + 1) - 1 : ℕ) : ℕ) : ℝ),
        ⟨j, rfl⟩, ?_⟩
    rw [hj]
    simp [realDistance]
    linarith

/-- Finite histories used in the diagonal contain only positive even
integers, so they may be added as the arbitrary `B` part of Example 4.5. -/
structure EvenHistory where
  data : List ℝ
  within :
    ∀ x, x ∈ data → x ∈ positiveEvenIntegers

def emptyEvenHistory : EvenHistory :=
  ⟨[], by simp⟩

/-- The row-zero point inserted at phase `n`, followed by the old history. -/
def phaseBase (n : ℕ) (state : EvenHistory) : List ℝ :=
  state.data ++ [diagonalRow 0 n]

/-- Temporary target based on the next odd prime. -/
def phaseTarget (n : ℕ) (state : EvenHistory) : Set ℝ :=
  primePairSupport (diagonalOddPrime (n + 1)) ∪
    listRange (phaseBase n state)

/-- Temporary presentation: retain the old history and the new row-zero
point, then enumerate the whole `(n+1)`st row. -/
def phaseStream
    (n : ℕ) (state : EvenHistory) :
    GenLimit.Generic.Stream ℝ :=
  prependListStream (phaseBase n state) (diagonalRow (n + 1))

theorem phaseBase_within_positiveEven
    (n : ℕ) (state : EvenHistory) :
    ∀ x, x ∈ phaseBase n state →
      x ∈ positiveEvenIntegers := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact state.within x hx
  · have hxEq : x = diagonalRow 0 n := by
      simpa using hx
    subst x
    exact diagonalRow_mem_positiveEvenIntegers 0 n

theorem phaseTarget_mem_languageClass
    (n : ℕ) (state : EvenHistory) :
    phaseTarget n state ∈ languageClass := by
  refine
    ⟨diagonalOddPrime (n + 1),
      diagonalOddPrime_prime (n + 1),
      diagonalOddPrime_odd (n + 1),
      listRange (phaseBase n state), ?_, rfl⟩
  intro x hx
  exact phaseBase_within_positiveEven n state x
    (mem_listRange_iff.mp hx)

theorem phaseStream_streamIn
    (n : ℕ) (state : EvenHistory) :
    GenLimit.Generic.StreamIn
      (phaseStream n state) (phaseTarget n state) := by
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  by_cases ht : t < (phaseBase n state).length
  · right
    rw [phaseStream,
      prependListStream_of_lt _ _ ht]
    exact mem_listRange_iff.mpr
      (List.get_mem _ ⟨t, ht⟩)
  · left
    rw [phaseStream, prependListStream, dif_neg ht]
    exact diagonalRow_mem_support
      (n + 1) (t - (phaseBase n state).length)

theorem phaseTarget_covered
    (n : ℕ) (state : EvenHistory) :
    phaseTarget n state ⊆
      closedNeighborhood realDistance
        (Set.range (phaseStream n state)) 1 := by
  intro x hx
  rcases hx with hxSupport | hxBase
  · have hrow :
        x ∈ closedNeighborhood realDistance
          (Set.range (diagonalRow (n + 1))) 1 :=
      primePairSupport_subset_row_neighborhood
        (diagonalOddPrime_prime (n + 1)).pos hxSupport
    apply inClosedNeighborhood_mono_centers
      (A := Set.range (diagonalRow (n + 1)))
      (B := Set.range (phaseStream n state)) ?_ hrow
    rintro y ⟨j, rfl⟩
    exact
      ⟨(phaseBase n state).length + j,
        by simpa [phaseStream] using
          prependListStream_add
            (phaseBase n state) (diagonalRow (n + 1)) j⟩
  · obtain ⟨i, rfl⟩ := hxBase
    intro η hη
    refine
      ⟨(phaseBase n state).get i,
        ⟨i, ?_⟩, ?_⟩
    · simpa [phaseStream] using
        prependListStream_of_lt
          (phaseBase n state) (diagonalRow (n + 1)) i.isLt
    · simp [realDistance]
      linarith

theorem phaseStream_metricPresentation
    (n : ℕ) (state : EvenHistory) :
    MetricPresentation realDistance 1
      (phaseStream n state) (phaseTarget n state) :=
  ⟨phaseStream_streamIn n state,
    phaseTarget_covered n state⟩

theorem phaseStream_eq_old
    (n : ℕ) (state : EvenHistory)
    {i : ℕ} (hi : i < state.data.length) :
    phaseStream n state i = state.data[i] := by
  have hiBase : i < (phaseBase n state).length := by
    simp [phaseBase]
    omega
  rw [phaseStream,
    prependListStream_of_lt _ _ hiBase]
  simp [phaseBase, List.get_eq_getElem, hi]

theorem phaseStream_eq_rowZero
    (n : ℕ) (state : EvenHistory) :
    phaseStream n state state.data.length =
      diagonalRow 0 n := by
  have hiBase :
      state.data.length < (phaseBase n state).length := by
    simp [phaseBase]
  rw [phaseStream,
    prependListStream_of_lt _ _ hiBase]
  simp [phaseBase, List.get_eq_getElem]

/-- One successful row phase.  New history points come only from row zero
and the currently protected row. -/
structure SuccessfulRealLinePhase
    (gen : GenLimit.Generic.Generator ℝ)
    (n : ℕ) (state : EvenHistory) where
  next : EvenHistory
  extends_history : state.data <+: next.data
  strict_growth : state.data.length < next.data.length
  output_current :
    GenLimit.Generic.output gen
        (GenLimit.Generic.historyThenFallback next.data 0)
        next.data.length ∈
      primePairSupport (diagonalOddPrime (n + 1))
  rowZero_mem : diagonalRow 0 n ∈ next.data
  new_support :
    ∀ x, x ∈ next.data → x ∉ state.data →
      x ∈ primePairSupport (diagonalOddPrime 0) ∨
      x ∈ primePairSupport (diagonalOddPrime (n + 1))

/-- The alleged generator must eventually leave the finite even history and
output inside the next prime support. -/
theorem exists_successfulRealLinePhase
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n : ℕ) (state : EvenHistory) :
    Nonempty (SuccessfulRealLinePhase gen n state) := by
  obtain ⟨T, hT⟩ :=
    hgen (phaseTarget n state)
      (phaseTarget_mem_languageClass n state)
      (phaseStream n state)
      (phaseStream_metricPresentation n state)
  let t := (phaseBase n state).length + T + 1
  have htT : T ≤ t := by
    dsimp [t]
    omega
  have htBase : (phaseBase n state).length < t := by
    dsimp [t]
    omega
  have hcorrect :
      MetricCorrectAt realDistance (1 / 2) gen
        (phaseTarget n state) (phaseStream n state) t :=
    hT t htT
  have houtCurrent :
      GenLimit.Generic.output gen (phaseStream n state) t ∈
        primePairSupport (diagonalOddPrime (n + 1)) := by
    rcases hcorrect.1 with hsupport | hbase
    · exact hsupport
    · exfalso
      obtain ⟨i, hiOutput⟩ := hbase
      have hiTime : (i : ℕ) < t :=
        i.isLt.trans htBase
      have hsample :
          GenLimit.Generic.output gen (phaseStream n state) t ∈
            GenLimit.Generic.sample (phaseStream n state) t := by
        apply GenLimit.Generic.mem_sample_iff.mpr
        refine ⟨i, hiTime, ?_⟩
        rw [phaseStream,
          prependListStream_of_lt _ _ i.isLt]
        exact hiOutput
      apply hcorrect.2
      intro η hη
      refine
        ⟨GenLimit.Generic.output gen (phaseStream n state) t,
          hsample, ?_⟩
      simp [realDistance]
      linarith
  let nextData :=
    finiteStreamPrefix (phaseStream n state) t
  have hnextEven :
      ∀ x, x ∈ nextData →
        x ∈ positiveEvenIntegers := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hi : (i : ℕ) < (phaseBase n state).length
    · rw [phaseStream,
        prependListStream_of_lt _ _ hi]
      exact phaseBase_within_positiveEven n state _
        (List.get_mem _ ⟨i, hi⟩)
    · rw [phaseStream, prependListStream, dif_neg hi]
      exact diagonalRow_mem_positiveEvenIntegers
        (n + 1) (i - (phaseBase n state).length)
  let next : EvenHistory := ⟨nextData, hnextEven⟩
  have hnextLength : next.data.length = t := by
    simp [next, nextData]
  have hagree :
      ∀ i : Fin t,
        GenLimit.Generic.historyThenFallback next.data 0 i =
          phaseStream n state i := by
    intro i
    have hiNext : (i : ℕ) < next.data.length := by
      rw [hnextLength]
      exact i.isLt
    rw [GenLimit.Generic.historyThenFallback, dif_pos hiNext]
    dsimp [next, nextData]
    simpa [finiteStreamPrefix] using
      finiteStreamPrefix_get (phaseStream n state) t i
  have houtNextAtT :
      GenLimit.Generic.output gen
          (GenLimit.Generic.historyThenFallback next.data 0) t ∈
        primePairSupport (diagonalOddPrime (n + 1)) := by
    rw [output_eq_of_eq_on_prefix gen hagree]
    exact houtCurrent
  have hextends : state.data <+: next.data := by
    rw [List.prefix_iff_getElem]
    refine ⟨?_, ?_⟩
    · rw [hnextLength]
      dsimp [t, phaseBase]
      simp
      omega
    · intro i hi
      have hiFin : i < t := by
        exact hi.trans
          (lt_trans (by simp [phaseBase]) htBase)
      have hiNext : i < next.data.length := by
        rw [hnextLength]
        exact hiFin
      have hold :
          state.data.get ⟨i, hi⟩ =
            phaseStream n state i := by
        simpa [List.get_eq_getElem] using
          (phaseStream_eq_old n state hi).symm
      have hnext :
          next.data.get ⟨i, hiNext⟩ =
            phaseStream n state i := by
        dsimp [next, nextData]
        simpa using finiteStreamPrefix_get
          (phaseStream n state) t ⟨i, hiFin⟩
      simpa [List.get_eq_getElem] using
        hold.trans hnext.symm
  have hrowZero : diagonalRow 0 n ∈ next.data := by
    dsimp [next, nextData, finiteStreamPrefix]
    have hiTime : state.data.length < t := by
      exact lt_trans
        (by simp [phaseBase])
        htBase
    exact List.mem_ofFn.mpr
      ⟨⟨state.data.length, hiTime⟩,
        phaseStream_eq_rowZero n state⟩
  have hnew :
      ∀ x, x ∈ next.data → x ∉ state.data →
        x ∈ primePairSupport (diagonalOddPrime 0) ∨
        x ∈ primePairSupport (diagonalOddPrime (n + 1)) := by
    intro x hxNext hxOld
    dsimp [next, nextData] at hxNext
    obtain ⟨i, hiEq⟩ := List.mem_ofFn.mp hxNext
    by_cases hi : (i : ℕ) < (phaseBase n state).length
    · have hiValue :
          phaseStream n state i =
            (phaseBase n state).get ⟨i, hi⟩ := by
        exact prependListStream_of_lt _ _ hi
      have hxBase :
          x ∈ phaseBase n state := by
        apply List.mem_iff_get.mpr
        exact ⟨⟨i, hi⟩,
          hiValue.symm.trans hiEq⟩
      rcases List.mem_append.mp hxBase with hxPrior | hxZero
      · exact False.elim (hxOld hxPrior)
      · left
        have hxEq : x = diagonalRow 0 n := by
          simpa using hxZero
        rw [hxEq]
        exact diagonalRow_mem_support 0 n
    · right
      have hiTail :
          phaseStream n state i =
            diagonalRow (n + 1)
              (i - (phaseBase n state).length) := by
        rw [phaseStream, prependListStream, dif_neg hi]
      rw [← hiEq, hiTail]
      exact diagonalRow_mem_support
        (n + 1) (i - (phaseBase n state).length)
  refine ⟨{
    next := next
    extends_history := hextends
    strict_growth := ?_
    output_current := ?_
    rowZero_mem := hrowZero
    new_support := hnew }⟩
  · rw [hnextLength]
    exact lt_of_lt_of_le
      (by simp [phaseBase])
      htBase.le
  · simpa [hnextLength] using houtNextAtT

/-! ## The limiting diagonal presentation -/

/-- Classical choice of one successful phase. -/
noncomputable def successfulRealLinePhase
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n : ℕ) (state : EvenHistory) :
    SuccessfulRealLinePhase gen n state :=
  Classical.choice
    (exists_successfulRealLinePhase gen hgen n state)

/-- Nested finite histories obtained by iterating the row phases. -/
noncomputable def realLineDiagonalHistory
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass) :
    ℕ → EvenHistory
  | 0 => emptyEvenHistory
  | n + 1 =>
      (successfulRealLinePhase gen hgen n
        (realLineDiagonalHistory gen hgen n)).next

theorem realLineDiagonalHistory_prefix_succ
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n : ℕ) :
    (realLineDiagonalHistory gen hgen n).data <+:
      (realLineDiagonalHistory gen hgen (n + 1)).data := by
  rw [realLineDiagonalHistory]
  exact
    (successfulRealLinePhase gen hgen n _).extends_history

theorem realLineDiagonalHistory_prefix
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    {n m : ℕ} (hnm : n ≤ m) :
    (realLineDiagonalHistory gen hgen n).data <+:
      (realLineDiagonalHistory gen hgen m).data := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
      exact ih.trans
        (realLineDiagonalHistory_prefix_succ gen hgen m)

theorem realLineDiagonalHistory_length
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n : ℕ) :
    n ≤ (realLineDiagonalHistory gen hgen n).data.length := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [realLineDiagonalHistory]
      have hgrowth :=
        (successfulRealLinePhase gen hgen n
          (realLineDiagonalHistory gen hgen n)).strict_growth
      omega

/-- Infinite stream determined by the compatible phase histories. -/
noncomputable def realLineDiagonalStream
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass) :
    GenLimit.Generic.Stream ℝ := fun k =>
  let history :=
    (realLineDiagonalHistory gen hgen (k + 1)).data
  history.get ⟨k, by
    have hlen :=
      realLineDiagonalHistory_length gen hgen (k + 1)
    exact lt_of_lt_of_le (Nat.lt_succ_self k) hlen⟩

theorem realLineDiagonalStream_eq_history_get
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n k : ℕ)
    (hk : k <
      (realLineDiagonalHistory gen hgen n).data.length) :
    realLineDiagonalStream gen hgen k =
      (realLineDiagonalHistory gen hgen n).data.get
        ⟨k, hk⟩ := by
  rw [realLineDiagonalStream]
  have hbound :
      k <
        (realLineDiagonalHistory gen hgen
          (k + 1)).data.length := by
    have hlen :=
      realLineDiagonalHistory_length gen hgen (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) n with hkn | hnk
  · exact
      (List.prefix_iff_getElem.mp
        (realLineDiagonalHistory_prefix
          gen hgen hkn)).2 k hbound
  · exact
      ((List.prefix_iff_getElem.mp
        (realLineDiagonalHistory_prefix
          gen hgen hnk)).2 k hk).symm

theorem realLineDiagonalHistory_mem_streamRange
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    {n : ℕ} {x : ℝ}
    (hx : x ∈
      (realLineDiagonalHistory gen hgen n).data) :
    x ∈ Set.range (realLineDiagonalStream gen hgen) := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  refine ⟨i, ?_⟩
  exact
    (realLineDiagonalStream_eq_history_get
      gen hgen n i i.isLt).trans hi

theorem realLineDiagonalStream_even
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (k : ℕ) :
    realLineDiagonalStream gen hgen k ∈
      positiveEvenIntegers := by
  let history :=
    realLineDiagonalHistory gen hgen (k + 1)
  have hk :
      k < history.data.length := by
    have hlen :=
      realLineDiagonalHistory_length gen hgen (k + 1)
    dsimp [history]
    omega
  rw [realLineDiagonalStream_eq_history_get
    gen hgen (k + 1) k hk]
  exact history.within _
    (List.get_mem history.data ⟨k, hk⟩)

theorem diagonalRow_zero_mem_streamRange
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n : ℕ) :
    diagonalRow 0 n ∈
      Set.range (realLineDiagonalStream gen hgen) := by
  apply realLineDiagonalHistory_mem_streamRange
    gen hgen (n := n + 1)
  rw [realLineDiagonalHistory]
  exact
    (successfulRealLinePhase gen hgen n _).rowZero_mem

theorem realLineDiagonal_sample_eq_history
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n : ℕ) :
    GenLimit.Generic.sample (realLineDiagonalStream gen hgen)
        (realLineDiagonalHistory gen hgen n).data.length =
      (realLineDiagonalHistory gen hgen n).data.toFinset := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sample_iff, List.mem_toFinset]
  constructor
  · rintro ⟨k, hk, hkx⟩
    apply List.mem_iff_get.mpr
    refine ⟨⟨k, hk⟩, ?_⟩
    exact
      (realLineDiagonalStream_eq_history_get
        gen hgen n k hk).symm.trans hkx
  · intro hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    refine ⟨i, i.isLt, ?_⟩
    exact
      (realLineDiagonalStream_eq_history_get
        gen hgen n i i.isLt).trans hi

/-- Once phase `n` has ended, later phases add no new point from its
protected prime support. -/
theorem currentSupport_stable_in_later_history
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n d : ℕ) {x : ℝ}
    (hxSupport :
      x ∈ primePairSupport (diagonalOddPrime (n + 1)))
    (hxLater :
      x ∈ (realLineDiagonalHistory gen hgen
        (n + 1 + d)).data) :
    x ∈ (realLineDiagonalHistory gen hgen
      (n + 1)).data := by
  revert hxLater
  induction d with
  | zero =>
      intro hx
      simpa using hx
  | succ d ih =>
      intro hx
      have hxNext :
          x ∈
            (successfulRealLinePhase gen hgen
              (n + 1 + d)
              (realLineDiagonalHistory gen hgen
                (n + 1 + d))).next.data := by
        simpa [realLineDiagonalHistory, Nat.add_assoc] using hx
      by_cases hxPrior :
          x ∈ (realLineDiagonalHistory gen hgen
            (n + 1 + d)).data
      · exact ih hxPrior
      · rcases
          (successfulRealLinePhase gen hgen
            (n + 1 + d)
            (realLineDiagonalHistory gen hgen
              (n + 1 + d))).new_support
              x hxNext hxPrior with hxZero | hxNew
        · exact False.elim
            ((Set.disjoint_left.mp
              (diagonalSupports_disjoint
                (show n + 1 ≠ 0 by omega)))
              hxSupport hxZero)
        · exact False.elim
            ((Set.disjoint_left.mp
              (diagonalSupports_disjoint
                (show n + 1 ≠ n + 1 + d + 1 by omega)))
              hxSupport hxNew)

theorem currentSupport_mem_history_of_mem_streamRange
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n : ℕ) {x : ℝ}
    (hxSupport :
      x ∈ primePairSupport (diagonalOddPrime (n + 1)))
    (hxRange :
      x ∈ Set.range (realLineDiagonalStream gen hgen)) :
    x ∈ (realLineDiagonalHistory gen hgen
      (n + 1)).data := by
  obtain ⟨k, hkx⟩ := hxRange
  have hkBound :
      k <
        (realLineDiagonalHistory gen hgen
          (k + 1)).data.length := by
    have hlen :=
      realLineDiagonalHistory_length gen hgen (k + 1)
    omega
  have hxHistory :
      x ∈ (realLineDiagonalHistory gen hgen
        (k + 1)).data := by
    apply List.mem_iff_get.mpr
    refine ⟨⟨k, hkBound⟩, ?_⟩
    exact
      (realLineDiagonalStream_eq_history_get
        gen hgen (k + 1) k hkBound).symm.trans hkx
  rcases le_total (k + 1) (n + 1) with hkn | hnk
  · exact
      (realLineDiagonalHistory_prefix gen hgen hkn).subset
        hxHistory
  · obtain ⟨d, hd⟩ :=
      Nat.exists_eq_add_of_le hnk
    rw [hd] at hxHistory
    exact currentSupport_stable_in_later_history
      gen hgen n d hxSupport hxHistory

/-- The limiting target uses the first odd-prime support and exactly the
positive even points revealed by the diagonal stream. -/
def realLineDiagonalTarget
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass) : Set ℝ :=
  primePairSupport (diagonalOddPrime 0) ∪
    Set.range (realLineDiagonalStream gen hgen)

theorem realLineDiagonalTarget_mem_languageClass
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass) :
    realLineDiagonalTarget gen hgen ∈ languageClass := by
  refine
    ⟨diagonalOddPrime 0,
      diagonalOddPrime_prime 0,
      diagonalOddPrime_odd 0,
      Set.range (realLineDiagonalStream gen hgen),
      ?_, rfl⟩
  rintro x ⟨k, rfl⟩
  exact realLineDiagonalStream_even gen hgen k

theorem realLineDiagonalTarget_metricPresentation
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass) :
    MetricPresentation realDistance 1
      (realLineDiagonalStream gen hgen)
      (realLineDiagonalTarget gen hgen) := by
  constructor
  · intro x hx
    obtain ⟨k, rfl⟩ := hx
    right
    exact ⟨k, rfl⟩
  · intro x hx
    rcases hx with hxSupport | hxRange
    · have hrow :
          x ∈ closedNeighborhood realDistance
            (Set.range (diagonalRow 0)) 1 :=
        primePairSupport_subset_row_neighborhood
          (diagonalOddPrime_prime 0).pos hxSupport
      apply inClosedNeighborhood_mono_centers
        (A := Set.range (diagonalRow 0))
        (B := Set.range
          (realLineDiagonalStream gen hgen)) ?_ hrow
      rintro y ⟨j, rfl⟩
      exact diagonalRow_zero_mem_streamRange
        gen hgen j
    · obtain ⟨k, rfl⟩ := hxRange
      intro η hη
      refine
        ⟨realLineDiagonalStream gen hgen k,
          ⟨k, rfl⟩, ?_⟩
      simp [realDistance]
      linarith

theorem diagonalStream_output_eq_historyFallback
    (gen : GenLimit.Generic.Generator ℝ)
    (hgen :
      IsLimitGeneratorAt realDistance 1 (1 / 2)
        gen languageClass)
    (n : ℕ) :
    GenLimit.Generic.output gen
        (realLineDiagonalStream gen hgen)
        (realLineDiagonalHistory gen hgen n).data.length =
      GenLimit.Generic.output gen
        (GenLimit.Generic.historyThenFallback
          (realLineDiagonalHistory gen hgen n).data 0)
        (realLineDiagonalHistory gen hgen n).data.length := by
  apply output_eq_of_eq_on_prefix gen
  intro i
  have hi := i.isLt
  rw [GenLimit.Generic.historyThenFallback, dif_pos hi]
  exact realLineDiagonalStream_eq_history_get
    gen hgen n i hi

/-- The source's infinite-row diagonal, specialized to its concrete
real-line class: no generator succeeds at scales `(1, 1/2)`. -/
theorem example_4_5_not_generatable_one_half :
    ¬GeneratableInLimitAt realDistance 1 (1 / 2) languageClass := by
  rintro ⟨gen, hgen⟩
  obtain ⟨T, hT⟩ :=
    hgen (realLineDiagonalTarget gen hgen)
      (realLineDiagonalTarget_mem_languageClass gen hgen)
      (realLineDiagonalStream gen hgen)
      (realLineDiagonalTarget_metricPresentation gen hgen)
  let t :=
    (realLineDiagonalHistory gen hgen (T + 1)).data.length
  have ht : T ≤ t := by
    dsimp [t]
    have hlen :=
      realLineDiagonalHistory_length gen hgen (T + 1)
    omega
  have hcorrect :
      MetricCorrectAt realDistance (1 / 2) gen
        (realLineDiagonalTarget gen hgen)
        (realLineDiagonalStream gen hgen) t :=
    hT t ht
  have hforcedFallback :
      GenLimit.Generic.output gen
          (GenLimit.Generic.historyThenFallback
            (realLineDiagonalHistory gen hgen
              (T + 1)).data 0)
          (realLineDiagonalHistory gen hgen
            (T + 1)).data.length ∈
        primePairSupport (diagonalOddPrime (T + 1)) := by
    rw [realLineDiagonalHistory]
    exact
      (successfulRealLinePhase gen hgen T _).output_current
  have hforced :
      GenLimit.Generic.output gen
          (realLineDiagonalStream gen hgen) t ∈
        primePairSupport (diagonalOddPrime (T + 1)) := by
    dsimp [t]
    rw [diagonalStream_output_eq_historyFallback
      gen hgen (T + 1)]
    exact hforcedFallback
  rcases hcorrect.1 with hzero | hstream
  · exact
      (Set.disjoint_left.mp
        (diagonalSupports_disjoint
          (show T + 1 ≠ 0 by omega)))
        hforced hzero
  · have hinHistory :
        GenLimit.Generic.output gen
            (realLineDiagonalStream gen hgen) t ∈
          (realLineDiagonalHistory gen hgen
            (T + 1)).data :=
      currentSupport_mem_history_of_mem_streamRange
        gen hgen T hforced hstream
    have hinSample :
        GenLimit.Generic.output gen
            (realLineDiagonalStream gen hgen) t ∈
          GenLimit.Generic.sample
            (realLineDiagonalStream gen hgen) t := by
      dsimp [t]
      rw [realLineDiagonal_sample_eq_history
        gen hgen (T + 1)]
      exact List.mem_toFinset.mpr hinHistory
    apply hcorrect.2
    intro η hη
    refine
      ⟨GenLimit.Generic.output gen
          (realLineDiagonalStream gen hgen) t,
        hinSample, ?_⟩
    simp [realDistance]
    linarith

/-- Negative half of Example 4.5.  A hypothetical `(1,1)` generator would,
by Theorem 4.6, also be a `(1,1/2)` generator, contradicting the checked
diagonal above. -/
theorem example_4_5_negative :
    ¬GeneratableInLimitAt realDistance 1 1 languageClass := by
  intro hgen
  exact example_4_5_not_generatable_one_half
    (theorem_4_6_limit_scale_monotonicity
      (show (1 : ℝ) ≤ 1 by rfl)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      hgen)

/-- Source-facing complete Example 4.5 threshold package. -/
theorem example_4_5_complete
    {ε : ℝ} (hεpos : 0 < ε) (hεlt : ε < 1) :
    UniformlyUnboundedSupportAt realDistance 1 languageClass ∧
      GeneratableInLimitAt realDistance ε 1 languageClass ∧
      ¬GeneratableInLimitAt realDistance 1 1 languageClass :=
  ⟨example_4_5_uus,
    example_4_5_positive hεpos hεlt,
    example_4_5_negative⟩

end

end RealLineThreshold
end GenLimit.MetricSpaces
