import GenLimit.Core
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Nth

/-!
# Finite-intersection closure for partial enumeration

Section 3.3 replaces the original family by its nonempty finite intersections.
A positive binary code records the finite set of original indices.  Finite
intersections are discarded, as stipulated in the paper, and the remaining
codes are reindexed in increasing code order.

The filtering is deliberately `noncomputable`: infinitude of an intersection
cannot in general be decided from pointwise membership oracles.  This matches
the semantic access boundary of the patient-scope machine formalized here.
-/

namespace GenLimit
namespace PartialEnumeration

/-- The original-language indices selected by a positive binary code. -/
def codeSupport (q : ℕ) : Finset ℕ := Finset.equivBitIndices q

/-- The intersection selected by a binary code.  Code zero denotes the empty
intersection, but is excluded from the transformed family below. -/
def codedIntersection (C : LanguageFamily) (q : ℕ) : Language :=
  {x | ∀ i ∈ codeSupport q, x ∈ C i}

@[simp] theorem codeSupport_two_pow (z : ℕ) :
    codeSupport (2 ^ z) = {z} := by
  simp [codeSupport, Finset.equivBitIndices_apply]

@[simp] theorem codedIntersection_two_pow (C : LanguageFamily) (z : ℕ) :
    codedIntersection C (2 ^ z) = C z := by
  ext x
  simp [codedIntersection]

theorem mem_codeSupport_lt_of_lt_two_pow {q z i : ℕ}
    (hq : q < 2 ^ z) (hi : i ∈ codeSupport q) : i < z := by
  by_contra hnot
  have hzi : z ≤ i := Nat.le_of_not_gt hnot
  have hipow : 2 ^ i ≤ q := by
    apply Nat.two_pow_le_of_mem_bitIndices
    simpa [codeSupport, Finset.equivBitIndices_apply] using hi
  have hpow : 2 ^ z ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hzi
  omega

/-- Adding a fresh high bit unions the old support with that bit. -/
theorem codeSupport_add_two_pow {q z : ℕ} (hq : q < 2 ^ z) :
    codeSupport (q + 2 ^ z) = insert z (codeSupport q) := by
  have hz : z ∉ codeSupport q := by
    intro hz
    exact (Nat.lt_irrefl z) (mem_codeSupport_lt_of_lt_two_pow hq hz)
  have hsum : q + 2 ^ z =
      ∑ i ∈ insert z (codeSupport q), 2 ^ i := by
    rw [Finset.sum_insert hz]
    simp [codeSupport, add_comm]
  apply Finset.equivBitIndices.symm.injective
  simpa [codeSupport, Finset.equivBitIndices_symm_apply] using hsum

/-- The binary-code identity used in the proof of Lemma 3.16. -/
theorem codedIntersection_add_two_pow {C : LanguageFamily} {q z : ℕ}
    (hq : q < 2 ^ z) :
    codedIntersection C (q + 2 ^ z) =
      codedIntersection C q ∩ C z := by
  ext x
  simp [codedIntersection, codeSupport_add_two_pow hq, and_comm]

/-- Positive codes whose selected intersection remains infinite. -/
def GoodCode (O : OracleFamily) (q : ℕ) : Prop :=
  q ≠ 0 ∧ (codedIntersection O.language q).Infinite

theorem goodCode_two_pow (O : OracleFamily) (z : ℕ) :
    GoodCode O (2 ^ z) := by
  refine ⟨pow_ne_zero _ (by omega), ?_⟩
  simpa using O.infinite' z

/-- There are infinitely many retained codes because every singleton
intersection is an original infinite language. -/
theorem infinite_goodCode (O : OracleFamily) :
    {q | GoodCode O q}.Infinite := by
  have hrange : Set.range (fun z : ℕ => 2 ^ z) ⊆
      {q | GoodCode O q} := by
    rintro _ ⟨z, rfl⟩
    exact goodCode_two_pow O z
  exact
    (Set.infinite_range_of_injective
      (Nat.pow_right_injective (by omega))).mono hrange

/-- The `n`th retained binary code, in increasing numeric order. -/
noncomputable def closureCode (O : OracleFamily) (n : ℕ) : ℕ :=
  Nat.nth (GoodCode O) n

/-- The transformed-family index of a retained raw binary code. -/
noncomputable def closureIndex (O : OracleFamily) (q : ℕ) : ℕ := by
  classical
  exact Nat.count (GoodCode O) q

theorem closureCode_good (O : OracleFamily) (n : ℕ) :
    GoodCode O (closureCode O n) := by
  exact Nat.nth_mem_of_infinite (infinite_goodCode O) n

theorem closureCode_strictMono (O : OracleFamily) :
    StrictMono (closureCode O) :=
  Nat.nth_strictMono (infinite_goodCode O)

theorem closureCode_closureIndex (O : OracleFamily) {q : ℕ}
    (hq : GoodCode O q) : closureCode O (closureIndex O q) = q := by
  classical
  exact Nat.nth_count hq

theorem closureIndex_closureCode (O : OracleFamily) (n : ℕ) :
    closureIndex O (closureCode O n) = n := by
  classical
  exact Nat.count_nth_of_infinite (infinite_goodCode O) n

theorem closureIndex_lt_closureIndex (O : OracleFamily) {q r : ℕ}
    (hq : GoodCode O q) (hqr : q < r) :
    closureIndex O q < closureIndex O r := by
  classical
  exact Nat.count_strict_mono hq hqr

/-- The finite-intersection closure after discarding finite intersections.
Its membership predicate is the finite conjunction of the original ones. -/
noncomputable def closure (O : OracleFamily) : OracleFamily where
  language n := codedIntersection O.language (closureCode O n)
  infinite' n := (closureCode_good O n).2
  query n x := (closureCode O n).bitIndices.all fun i => O.query i x
  query_spec n x := by
    simp only [List.all_eq_true, O.query_spec]
    simp [codedIntersection, codeSupport, Finset.equivBitIndices_apply]

@[simp] theorem closure_language (O : OracleFamily) (n : ℕ) :
    (closure O).language n =
      codedIntersection O.language (closureCode O n) := rfl

theorem closure_language_closureIndex (O : OracleFamily) {q : ℕ}
    (hq : GoodCode O q) :
    (closure O).language (closureIndex O q) =
      codedIntersection O.language q := by
  simp [closure, closureCode_closureIndex O hq]

theorem codedIntersection_subset_original
    {C : LanguageFamily} {q i : ℕ} (hi : i ∈ codeSupport q) :
    codedIntersection C q ⊆ C i := by
  intro x hx
  exact hx i hi

/-- Every code in the binary block `[2^z, 2^(z+1))` selects the original
target index `z`. -/
theorem target_mem_codeSupport_of_mem_block {q z : ℕ}
    (hlow : 2 ^ z ≤ q) (hhigh : q < 2 ^ (z + 1)) :
    z ∈ codeSupport q := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hlow
  have hr : r < 2 ^ z := by
    rw [pow_succ] at hhigh
    omega
  have hsupport := codeSupport_add_two_pow (q := r) hr
  rw [add_comm] at hsupport
  rw [hsupport]
  simp

theorem codedIntersection_subset_target_of_mem_block
    {C : LanguageFamily} {q z : ℕ}
    (hlow : 2 ^ z ≤ q) (hhigh : q < 2 ^ (z + 1)) :
    codedIntersection C q ⊆ C z :=
  codedIntersection_subset_original
    (target_mem_codeSupport_of_mem_block hlow hhigh)

end PartialEnumeration
end GenLimit
