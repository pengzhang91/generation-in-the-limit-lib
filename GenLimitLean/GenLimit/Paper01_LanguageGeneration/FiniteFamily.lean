import GenLimit.Core.ClosureDimension
import GenLimit.Core.OracleFamily
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat

/-!
# #01 Language Generation: finite-family uniform generation

This module formalizes NeurIPS result (2.2).  A finite subcollection is given
by a `Finset` of indices in the existing `OracleFamily`; no second membership
oracle is introduced.  For a fixed positive sample, the algorithm first uses
the Boolean oracle to retain precisely the consistent indices, then scans the
natural-number universe and returns successive points accepted by every
retained language and absent from the sample.

The family-dependent threshold is obtained from the finite-class closure
bound.  Above that threshold the accepted set is infinite.  Every individual
search terminates and tests only finitely many natural numbers, and every test
uses finitely many calls to `OracleFamily.query`.  The development does not
introduce a numerical query-complexity or runtime cost model.
-/

namespace GenLimit
namespace KM
namespace FiniteFamily

/-- The extensional language class represented by a finite set of indices.
Repeated extensionally equal languages are harmless. -/
def languageClass (O : OracleFamily) (members : Finset ℕ) :
    Generic.LanguageClass ℕ :=
  O.language '' (↑members : Set ℕ)

theorem languageClass_finite (O : OracleFamily) (members : Finset ℕ) :
    (languageClass O members).Finite := by
  exact members.finite_toSet.image O.language

theorem language_mem_languageClass
    (O : OracleFamily) {members : Finset ℕ} {i : ℕ}
    (hi : i ∈ members) :
    O.language i ∈ languageClass O members :=
  ⟨i, hi, rfl⟩

/-- Indices in the finite collection whose languages contain the fixed
positive sample.  This is an executable finite filter using the existing
uniform membership oracle. -/
def consistentIndices
    (O : OracleFamily) (members S : Finset ℕ) : Finset ℕ :=
  members.filter fun i ↦ O.ConsistentOnFinset S i

@[simp] theorem mem_consistentIndices
    (O : OracleFamily) {members S : Finset ℕ} {i : ℕ} :
    i ∈ consistentIndices O members S ↔
      i ∈ members ∧ (↑S : Set ℕ) ⊆ O.language i := by
  rw [consistentIndices, Finset.mem_filter, O.consistentOnFinset_iff]

/-- A universe point accepted by every sample-consistent member of the finite
collection and not already contained in the fixed sample. -/
def Accepted
    (O : OracleFamily) (members S : Finset ℕ) (x : ℕ) : Prop :=
  x ∉ S ∧
    ∀ i ∈ consistentIndices O members S, O.query i x = true

instance acceptedDecidable
    (O : OracleFamily) (members S : Finset ℕ) (x : ℕ) :
    Decidable (Accepted O members S x) := by
  unfold Accepted
  infer_instance

/-- The set searched by the fixed-sample enumerator. -/
def acceptedSet
    (O : OracleFamily) (members S : Finset ℕ) : Set ℕ :=
  {x | Accepted O members S x}

instance acceptedSetMembershipDecidable
    (O : OracleFamily) (members S : Finset ℕ) :
    DecidablePred (fun x ↦ x ∈ acceptedSet O members S) :=
  fun x ↦ acceptedDecidable O members S x

theorem target_mem_consistentIndices
    (O : OracleFamily) {members S : Finset ℕ} {z : ℕ}
    (hz : z ∈ members) (hS : (↑S : Set ℕ) ⊆ O.language z) :
    z ∈ consistentIndices O members S :=
  (mem_consistentIndices O).2 ⟨hz, hS⟩

theorem accepted_mem_target
    (O : OracleFamily) {members S : Finset ℕ} {z x : ℕ}
    (hz : z ∈ members) (hS : (↑S : Set ℕ) ⊆ O.language z)
    (hx : Accepted O members S x) :
    x ∈ O.language z := by
  apply (O.query_spec z x).mp
  exact hx.2 z (target_mem_consistentIndices O hz hS)

theorem consistent_language_mem_versionSpace
    (O : OracleFamily) {members S : Finset ℕ} {i : ℕ}
    (hi : i ∈ consistentIndices O members S) :
    O.language i ∈ Generic.versionSpace (languageClass O members) S := by
  have hi' := (mem_consistentIndices O).1 hi
  exact ⟨language_mem_languageClass O hi'.1, hi'.2⟩

/-- The positive common core outside the sample is contained in the set
recognized by the finite membership-query test. -/
theorem commonCore_diff_subset_acceptedSet
    (O : OracleFamily) (members S : Finset ℕ) :
    Generic.commonCore (languageClass O members) S \ (↑S : Set ℕ) ⊆
      acceptedSet O members S := by
  rintro x ⟨hxcore, hxS⟩
  refine ⟨hxS, ?_⟩
  intro i hi
  apply (O.query_spec i x).mpr
  exact hxcore (O.language i)
    (consistent_language_mem_versionSpace O hi)

/-- A closure-dimension bound selected once from the finite collection. -/
noncomputable def closureBound
    (O : OracleFamily) (members : Finset ℕ) : ℕ :=
  Classical.choose
    (Generic.finite_language_class_has_finite_closure_dimension
      (languageClass_finite O members))

theorem closureBound_spec
    (O : OracleFamily) (members : Finset ℕ) :
    Generic.HasClosureDimension
      (languageClass O members) (closureBound O members) :=
  Classical.choose_spec
    (Generic.finite_language_class_has_finite_closure_dimension
      (languageClass_finite O members))

/-- The sample-size threshold in result (2.2). -/
noncomputable def threshold
    (O : OracleFamily) (members : Finset ℕ) : ℕ :=
  closureBound O members + 1

/-- Above the family-dependent threshold, every fixed sample from a target
member leaves infinitely many points accepted by all consistent languages. -/
theorem acceptedSet_infinite
    (O : OracleFamily) {members S : Finset ℕ} {z : ℕ}
    (hlarge : threshold O members ≤ S.card)
    (hz : z ∈ members) (hS : (↑S : Set ℕ) ⊆ O.language z) :
    (acceptedSet O members S).Infinite := by
  have hVS :
      (Generic.versionSpace (languageClass O members) S).Nonempty :=
    ⟨O.language z, language_mem_languageClass O hz, hS⟩
  have hbound : closureBound O members < S.card := by
    simpa only [threshold, Nat.succ_eq_add_one, Nat.succ_le_iff] using hlarge
  have hcore :
      (Generic.commonCore (languageClass O members) S \ (↑S : Set ℕ)).Infinite :=
    Generic.core_diff_sample_infinite
      (closureBound_spec O members).1 S hbound hVS
  exact hcore.mono (commonCore_diff_subset_acceptedSet O members S)

/-- Enumerate the oracle-recognized accepted set in strictly increasing order.

The infinitude certificate supplies termination of each unbounded search; the
searched predicate itself is decidable from the finite sample, finite index
set, and `OracleFamily.query`. -/
def enumerateAccepted
    (O : OracleFamily) (members S : Finset ℕ)
    (hInfinite : (acceptedSet O members S).Infinite) : ℕ → ℕ
  | 0 => Nat.find hInfinite.nonempty
  | k + 1 =>
      Nat.find
        (hInfinite.exists_gt
          (enumerateAccepted O members S hInfinite k))

/-- The termination certificate carries no algorithmic choice: proof
irrelevance makes the resulting scan independent of how infinitude was
established (in particular, independent of the hidden target used in the
correctness proof). -/
theorem enumerateAccepted_proof_irrel
    (O : OracleFamily) (members S : Finset ℕ)
    (h₁ h₂ : (acceptedSet O members S).Infinite) :
    enumerateAccepted O members S h₁ =
      enumerateAccepted O members S h₂ := by
  rw [Subsingleton.elim h₁ h₂]

theorem enumerateAccepted_mem
    (O : OracleFamily) (members S : Finset ℕ)
    (hInfinite : (acceptedSet O members S).Infinite) (k : ℕ) :
    enumerateAccepted O members S hInfinite k ∈ acceptedSet O members S := by
  cases k with
  | zero =>
      exact Nat.find_spec hInfinite.nonempty
  | succ k =>
      exact
        (Nat.find_spec
          (hInfinite.exists_gt
            (enumerateAccepted O members S hInfinite k))).1

theorem enumerateAccepted_lt_succ
    (O : OracleFamily) (members S : Finset ℕ)
    (hInfinite : (acceptedSet O members S).Infinite) (k : ℕ) :
    enumerateAccepted O members S hInfinite k <
      enumerateAccepted O members S hInfinite (k + 1) := by
  exact
    (Nat.find_spec
      (hInfinite.exists_gt
        (enumerateAccepted O members S hInfinite k))).2

theorem enumerateAccepted_strictMono
    (O : OracleFamily) (members S : Finset ℕ)
    (hInfinite : (acceptedSet O members S).Infinite) :
    StrictMono (enumerateAccepted O members S hInfinite) :=
  strictMono_nat_of_lt_succ
    (enumerateAccepted_lt_succ O members S hInfinite)

/-- The fixed-sample output required by result (2.2): an injective infinite
sequence whose range lies in the target minus the supplied sample. -/
def ProducesFromSample
    (O : OracleFamily) (S : Finset ℕ) (z : ℕ)
    (output : ℕ → ℕ) : Prop :=
  Function.Injective output ∧
    Set.range output ⊆ O.language z \ (↑S : Set ℕ)

theorem enumerateAccepted_producesFromSample
    (O : OracleFamily) {members S : Finset ℕ} {z : ℕ}
    (hz : z ∈ members) (hS : (↑S : Set ℕ) ⊆ O.language z)
    (hInfinite : (acceptedSet O members S).Infinite) :
    ProducesFromSample O S z
      (enumerateAccepted O members S hInfinite) := by
  constructor
  · exact (enumerateAccepted_strictMono O members S hInfinite).injective
  · rintro x ⟨k, rfl⟩
    have hx := enumerateAccepted_mem O members S hInfinite k
    exact ⟨accepted_mem_target O hz hS hx, hx.1⟩

/-- NeurIPS result (2.2), over the paper's concrete universe `ℕ`.

For every finite subcollection there is one collection-dependent threshold.
Every fixed set of at least that many distinct examples from any target member
admits the same oracle-defined scan, which produces an infinite pairwise-
distinct sequence contained in the target minus the fixed sample. -/
theorem theorem_2_2 (O : OracleFamily) (members : Finset ℕ) :
    ∃ tC : ℕ, ∀ (S : Finset ℕ), tC ≤ S.card →
      ∀ z ∈ members, (↑S : Set ℕ) ⊆ O.language z →
        ∃ hInfinite : (acceptedSet O members S).Infinite,
          ProducesFromSample O S z
            (enumerateAccepted O members S hInfinite) := by
  refine ⟨threshold O members, ?_⟩
  intro S hlarge z hz hS
  let hInfinite := acceptedSet_infinite O hlarge hz hS
  exact ⟨hInfinite, enumerateAccepted_producesFromSample O hz hS hInfinite⟩

end FiniteFamily
end KM
end GenLimit
