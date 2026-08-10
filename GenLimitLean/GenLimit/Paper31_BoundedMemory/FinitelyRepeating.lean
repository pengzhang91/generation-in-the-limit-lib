import GenLimit.Paper31_BoundedMemory.ArbitraryRepetitions
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Finite.Lattice

/-!
# Theorem 1.1: the finitely-repeating universal construction

Source: Kleinberg--Mehrotra--Saberi--Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Theorem 1.1 and Section 3.1.

The source identifies the countable universe with `ℕ`, enumerates the
language family as `L₀, L₁, ...`, and, on seeing `x`, takes the longest
prefix of length at most `x` whose languages containing `x` have infinite
intersection.  The finite-intersection envelope below is the source's
finite exceptional set `U_z`.
-/

namespace GenLimit.BoundedMemory

section PrefixConstruction

/-- `J_n(x)`: the intersection of the first `n + 1` languages that contain
the currently observed point `x`. -/
def prefixCore (langs : ℕ → Set ℕ) (n x : ℕ) : Set ℕ :=
  {y | ∀ j, j ≤ n → x ∈ langs j → y ∈ langs j}

theorem mem_prefixCore (langs : ℕ → Set ℕ) (n x : ℕ) :
    x ∈ prefixCore langs n x := by
  intro j _hj hx
  exact hx

theorem prefixCore_mono
    (langs : ℕ → Set ℕ) {m n x : ℕ} (hmn : m ≤ n) :
    prefixCore langs n x ⊆ prefixCore langs m x := by
  intro y hy j hj hx
  exact hy j (hj.trans hmn) hx

theorem prefixCore_zero_infinite
    (langs : ℕ → Set ℕ) (hL0 : (langs 0).Infinite) (x : ℕ) :
    (prefixCore langs 0 x).Infinite := by
  by_cases hx : x ∈ langs 0
  · have heq : prefixCore langs 0 x = langs 0 := by
      ext y
      simp [prefixCore, hx]
    simpa [heq] using hL0
  · have heq : prefixCore langs 0 x = Set.univ := by
      ext y
      simp [prefixCore, hx]
    rw [heq]
    exact Set.infinite_univ

/-- The source's `n(x)`, using zero-based language indices. -/
noncomputable def selectedDepth (langs : ℕ → Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun n => (prefixCore langs n x).Infinite) x

theorem selectedDepth_le (langs : ℕ → Set ℕ) (x : ℕ) :
    selectedDepth langs x ≤ x := by
  classical
  exact Nat.findGreatest_le x

theorem selectedDepth_core_infinite
    (langs : ℕ → Set ℕ) (hL0 : (langs 0).Infinite) (x : ℕ) :
    (prefixCore langs (selectedDepth langs x) x).Infinite := by
  classical
  simpa [selectedDepth] using
    (Nat.findGreatest_spec
      (P := fun n => (prefixCore langs n x).Infinite)
      (m := 0) (Nat.zero_le x)
      (prefixCore_zero_infinite langs hL0 x))

theorem le_selectedDepth_of_infinite
    (langs : ℕ → Set ℕ) {n x : ℕ} (hnx : n ≤ x)
    (hinf : (prefixCore langs n x).Infinite) :
    n ≤ selectedDepth langs x := by
  classical
  exact Nat.le_findGreatest hnx hinf

/-- The memoryless set generator from Section 3.1. -/
noncomputable def finitelyRepeatingGenerator
    (langs : ℕ → Set ℕ) : MemorylessSetGenerator ℕ :=
  fun x => prefixCore langs (selectedDepth langs x) x

theorem finitelyRepeatingGenerator_infinite
    (langs : ℕ → Set ℕ) (hInfinite : ∀ n, (langs n).Infinite) (x : ℕ) :
    (finitelyRepeatingGenerator langs x).Infinite := by
  exact selectedDepth_core_infinite langs (hInfinite 0) x

end PrefixConstruction

section FiniteEnvelope

/-- Intersection of a finite signature of language indices. -/
def indexedIntersection
    (langs : ℕ → Set ℕ) {z : ℕ} (S : Finset (Fin (z + 1))) : Set ℕ :=
  {y | ∀ i, i ∈ S → y ∈ langs i}

/-- The first-`z` signature of a point. -/
noncomputable def prefixSignature
    (langs : ℕ → Set ℕ) (z x : ℕ) : Finset (Fin (z + 1)) := by
  classical
  exact Finset.univ.filter (fun i => x ∈ langs i)

theorem prefixCore_eq_indexedIntersection
    (langs : ℕ → Set ℕ) (z x : ℕ) :
    prefixCore langs z x =
      indexedIntersection langs (prefixSignature langs z x) := by
  classical
  ext y
  constructor
  · intro hy i hi
    have hix : x ∈ langs (i : ℕ) := by
      simpa [prefixSignature] using (Finset.mem_filter.mp hi).2
    exact hy i (Nat.lt_succ_iff.mp i.isLt) hix
  · intro hy j hj hx
    have hjlt : j < z + 1 := Nat.lt_succ_iff.mpr hj
    let i : Fin (z + 1) := ⟨j, hjlt⟩
    have hi : i ∈ prefixSignature langs z x := by
      simp [prefixSignature, i, hx]
    exact hy i hi

/-- Retain an indexed intersection exactly when it is finite. -/
noncomputable def finiteIntersectionPiece
    (langs : ℕ → Set ℕ) {z : ℕ} (S : Finset (Fin (z + 1))) : Set ℕ := by
  classical
  exact if (indexedIntersection langs S).Finite then
    indexedIntersection langs S
  else
    ∅

theorem finiteIntersectionPiece_finite
    (langs : ℕ → Set ℕ) {z : ℕ} (S : Finset (Fin (z + 1))) :
    (finiteIntersectionPiece langs S).Finite := by
  classical
  simp only [finiteIntersectionPiece]
  split_ifs with h
  · exact h
  · exact Set.finite_empty

/-- The finite union of all finite intersections among the first `z + 1`
languages.  This is the source's exceptional set `U_z`. -/
noncomputable def finiteIntersectionEnvelope
    (langs : ℕ → Set ℕ) (z : ℕ) : Set ℕ :=
  ⋃ S : Finset (Fin (z + 1)), finiteIntersectionPiece langs S

theorem finiteIntersectionEnvelope_finite
    (langs : ℕ → Set ℕ) (z : ℕ) :
    (finiteIntersectionEnvelope langs z).Finite := by
  classical
  exact Set.finite_iUnion (fun S => finiteIntersectionPiece_finite langs S)

theorem mem_finiteIntersectionEnvelope_of_prefixCore_finite
    (langs : ℕ → Set ℕ) {z x : ℕ}
    (hfinite : (prefixCore langs z x).Finite) :
    x ∈ finiteIntersectionEnvelope langs z := by
  classical
  let S := prefixSignature langs z x
  have hEq :
      indexedIntersection langs S = prefixCore langs z x := by
    simpa [S] using (prefixCore_eq_indexedIntersection langs z x).symm
  have hIndexed : (indexedIntersection langs S).Finite := by
    simpa [hEq] using hfinite
  apply Set.mem_iUnion.mpr
  refine ⟨S, ?_⟩
  simp only [finiteIntersectionPiece, if_pos hIndexed]
  rw [hEq]
  exact mem_prefixCore langs z x

end FiniteEnvelope

section BadPoints

/-- Inputs from a target language on which the canonical generator is not
safe for that target. -/
def badPoints (langs : ℕ → Set ℕ) (z : ℕ) : Set ℕ :=
  {x | x ∈ langs z ∧
    ¬finitelyRepeatingGenerator langs x ⊆ langs z}

theorem badPoints_subset
    (langs : ℕ → Set ℕ) (z : ℕ) :
    badPoints langs z ⊆
      Set.Iio z ∪ finiteIntersectionEnvelope langs z := by
  classical
  intro x hx
  by_cases hxz : x < z
  · exact Set.mem_union_left _ hxz
  · apply Set.mem_union_right
    have hzx : z ≤ x := Nat.le_of_not_gt hxz
    have hCoreNotInfinite : ¬(prefixCore langs z x).Infinite := by
      intro hCoreInfinite
      have hzDepth :
          z ≤ selectedDepth langs x :=
        le_selectedDepth_of_infinite langs hzx hCoreInfinite
      have hSafe :
          finitelyRepeatingGenerator langs x ⊆ langs z := by
        intro y hy
        exact hy z hzDepth hx.1
      exact hx.2 hSafe
    exact mem_finiteIntersectionEnvelope_of_prefixCore_finite langs
      (Set.not_infinite.mp hCoreNotInfinite)

theorem badPoints_finite (langs : ℕ → Set ℕ) (z : ℕ) :
    (badPoints langs z).Finite := by
  have hIio : (Set.Iio z).Finite := by
    have hRange :
        (Set.range (fun i : Fin z => (i : ℕ))).Finite :=
      Set.finite_range _
    apply hRange.subset
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  apply Set.Finite.subset
    (hIio.union
      (finiteIntersectionEnvelope_finite langs z))
  exact badPoints_subset langs z

theorem finitelyRepeating_avoids_finite_set
    {α : Type*} {stream : ℕ → α}
    (hRepeat : FinitelyRepeating stream) {S : Set α} (hS : S.Finite) :
    ∃ T, ∀ t, T ≤ t → stream t ∉ S := by
  classical
  let times : Set ℕ := {t | stream t ∈ S}
  have hTimes : times.Finite := by
    have hUnion :
        times = ⋃ x ∈ S, {t : ℕ | stream t = x} := by
      ext t
      simp [times]
    rw [hUnion]
    exact hS.biUnion (fun x _hx => hRepeat x)
  obtain ⟨B, hB⟩ := hTimes.bddAbove
  refine ⟨B + 1, ?_⟩
  intro t ht hmem
  have htB : t ≤ B := hB hmem
  omega

end BadPoints

section TheoremOneOne

/-- The explicit Section 3.1 generator succeeds on every member of an
enumerated family of infinite languages. -/
theorem finitelyRepeatingGenerator_succeeds
    (langs : ℕ → Set ℕ) (hInfinite : ∀ n, (langs n).Infinite) :
    IsFinitelyRepeatingMemorylessGenerator
      (finitelyRepeatingGenerator langs) (Set.range langs) := by
  intro K hK stream hP hRepeat
  obtain ⟨z, rfl⟩ := hK
  obtain ⟨T, hT⟩ :=
    finitelyRepeating_avoids_finite_set hRepeat
      (badPoints_finite langs z)
  refine ⟨T, ?_⟩
  intro t ht
  have hxt : stream t ∈ langs z := by
    rw [← hP]
    exact ⟨t, rfl⟩
  have hSafe : finitelyRepeatingGenerator langs (stream t) ⊆ langs z := by
    by_contra hnot
    exact (hT t ht) ⟨hxt, hnot⟩
  exact ⟨finitelyRepeatingGenerator_infinite langs hInfinite (stream t),
    hSafe⟩

/-- Theorem 1.1 on an explicitly enumerated countable collection. -/
theorem theorem_1_1_enumerated
    (langs : ℕ → Set ℕ) (hInfinite : ∀ n, (langs n).Infinite) :
    FinitelyRepeatingMemorylessGeneratable (Set.range langs) :=
  ⟨finitelyRepeatingGenerator langs,
    finitelyRepeatingGenerator_succeeds langs hInfinite⟩

/-- Theorem 1.1: every countable collection of infinite languages over
`ℕ` has a memoryless set-based generator under finitely repeating exact
presentations. -/
theorem theorem_1_1
    (H : Set (Set ℕ))
    (hCountable : H.Countable)
    (hInfinite : ∀ K, K ∈ H → K.Infinite) :
    FinitelyRepeatingMemorylessGeneratable H := by
  classical
  by_cases hH : H.Nonempty
  · let f : ℕ → H :=
      Classical.choose (hCountable.exists_surjective hH)
    have hf : Function.Surjective f :=
      Classical.choose_spec (hCountable.exists_surjective hH)
    let langs : ℕ → Set ℕ := fun n => (f n : Set ℕ)
    have hRange : Set.range langs = H := by
      apply Set.Subset.antisymm
      · rintro K ⟨n, rfl⟩
        exact (f n).property
      · intro K hKH
        obtain ⟨n, hn⟩ := hf ⟨K, hKH⟩
        refine ⟨n, ?_⟩
        exact congrArg Subtype.val hn
    have hLangInfinite : ∀ n, (langs n).Infinite := by
      intro n
      exact hInfinite (langs n) (f n).property
    rw [← hRange]
    exact theorem_1_1_enumerated langs hLangInfinite
  · have hEmpty : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
    rw [hEmpty]
    refine ⟨fun _ => Set.univ, ?_⟩
    intro K hK
    exact (Set.notMem_empty K hK).elim

end TheoremOneOne

end GenLimit.BoundedMemory
