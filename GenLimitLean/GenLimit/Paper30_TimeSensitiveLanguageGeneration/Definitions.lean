import GenLimit.Core.OrderedDensity
import Mathlib.Data.Finset.Image
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Time-sensitive generation: deterministic definitions

Source: Atul Ganju, Travis McVoy, Shaddin Dughmi, and Shang-Hua Teng,
*A Theory of Time-Sensitive Language Generation: Sparse Hallucination Beats
Mode Collapse*, arXiv:2605.11302v2, Sections 1.1--3 and Appendix C.

The paper's generators are randomized.  This file deliberately isolates the
pathwise, finite-prefix objects to which the probability argument is later
applied: deadlines, timely credited strings, prefix-wise credit, and distinct
hallucinated outputs.  No probability space or runtime claim is hidden in
these definitions.

All prefixes are zero-based: `Finset.range n` represents the first `n`
positions.  A deadline value `D j` therefore exposes output indices strictly
below `D j`, exactly as the source's prefix `S_{D(j)}`.
-/

namespace GenLimit.TimeSensitive

open Filter
open GenLimit.KleinbergWei

/-- A monotone nondecreasing deadline function. -/
structure Deadline where
  toFun : ℕ → ℕ
  monotone' : Monotone toFun

instance : CoeFun Deadline (fun _ => ℕ → ℕ) :=
  ⟨Deadline.toFun⟩

/-- The additional unboundedness needed for the paper's generalized inverse
`min {n : D n ≥ t}` to exist at every time. -/
def Deadline.IsUnbounded (D : Deadline) : Prop :=
  ∀ t, ∃ n, t ≤ D n

/-- The generalized inverse used throughout Sections 2--3.

Unlike the paper's bare `min` notation, the definition records the
unboundedness witness needed to make the minimum total. -/
noncomputable def Deadline.inverse
    (D : Deadline) (hD : D.IsUnbounded) (t : ℕ) : ℕ :=
  Nat.find (hD t)

theorem Deadline.le_inverse_value
    (D : Deadline) (hD : D.IsUnbounded) (t : ℕ) :
    t ≤ D (D.inverse hD t) :=
  Nat.find_spec (hD t)

theorem Deadline.inverse_min
    (D : Deadline) (hD : D.IsUnbounded) {t n : ℕ}
    (hn : t ≤ D n) :
    D.inverse hD t ≤ n :=
  Nat.find_min' (hD t) hn

theorem Deadline.inverse_mono
    (D : Deadline) (hD : D.IsUnbounded) :
    Monotone (D.inverse hD) := by
  intro s t hst
  apply Deadline.inverse_min
  exact hst.trans (Deadline.le_inverse_value D hD t)

/-! ## Generalized-inverse diagnostics -/

/-- A monotone deadline for which the paper's bare generalized inverse is
undefined at every positive time. -/
def zeroDeadline : Deadline where
  toFun := fun _ => 0
  monotone' := fun _ _ _ => le_rfl

theorem zeroDeadline_not_unbounded :
    ¬zeroDeadline.IsUnbounded := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  simp [zeroDeadline] at hn

/-- A non-strictly-monotone but unbounded deadline whose inverse hits only
even indices.  This records why a liminf argument cannot silently assume
that generalized-inverse indices range over every natural number. -/
def halfDeadline : Deadline where
  toFun := fun n => n / 2
  monotone' := fun _ _ h => Nat.div_le_div_right h

theorem halfDeadline_unbounded :
    halfDeadline.IsUnbounded := by
  intro t
  refine ⟨2 * t, ?_⟩
  simp [halfDeadline]

theorem halfDeadline_inverse
    (t : ℕ) :
    halfDeadline.inverse halfDeadline_unbounded t = 2 * t := by
  apply le_antisymm
  · apply Deadline.inverse_min
    simp [halfDeadline]
  · have hspec :=
      Deadline.le_inverse_value
        halfDeadline halfDeadline_unbounded t
    change t ≤ halfDeadline.inverse halfDeadline_unbounded t / 2 at hspec
    omega

theorem halfDeadline_inverse_even
    (t : ℕ) :
    Even (halfDeadline.inverse halfDeadline_unbounded t) := by
  rw [halfDeadline_inverse]
  exact ⟨t, by omega⟩

/-- Distinct values appearing in the first `n` positions of a sequence. -/
noncomputable def sequencePrefix
    (S : ℕ → α) (n : ℕ) : Finset α := by
  classical
  exact (Finset.range n).image S

theorem mem_sequencePrefix_iff
    (S : ℕ → α) (x : α) (n : ℕ) :
    x ∈ sequencePrefix S n ↔ ∃ k < n, S k = x := by
  classical
  simp [sequencePrefix]

theorem sequencePrefix_mono
    (S : ℕ → α) {m n : ℕ} (hmn : m ≤ n) :
    sequencePrefix S m ⊆ sequencePrefix S n := by
  classical
  intro x hx
  obtain ⟨k, hk, rfl⟩ := (mem_sequencePrefix_iff S x m).mp hx
  exact (mem_sequencePrefix_iff S (S k) n).mpr
    ⟨k, lt_of_lt_of_le hk hmn, rfl⟩

/-- The target strings among its first `i` ordered positions. -/
noncomputable def targetPrefix
    (R : ℕ → α) (i : ℕ) : Finset α :=
  sequencePrefix R i

/-- Definition 1.1's timely credited target strings: `R j` is credited only
when it occurs in the output prefix cut off by its own deadline `D j`. -/
noncomputable def timelyElements
    (S R : ℕ → α) (D : ℕ → ℕ) (i : ℕ) : Finset α := by
  classical
  exact ((Finset.range i).filter
    (fun j => R j ∈ sequencePrefix S (D j))).image R

/-- Definition 3's prefix-wise credited target strings: the common cutoff is
`F i`, rather than the individual cutoff `D j`. -/
noncomputable def prefixWiseElements
    (S R : ℕ → α) (F : ℕ → ℕ) (i : ℕ) : Finset α := by
  classical
  exact targetPrefix R i ∩ sequencePrefix S (F i)

/-- Finite element-wise timely density.  The empty prefix is assigned zero. -/
noncomputable def timelyDensity
    (S R : ℕ → α) (D : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (timelyElements S R D i).card / (i : ℝ)

/-- Definition 3: finite prefix-wise timely density. -/
noncomputable def prefixWiseDensity
    (S R : ℕ → α) (F : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (prefixWiseElements S R F i).card / (i : ℝ)

/-- Instance-level lower timely density.  The paper then infimizes this
quantity over targets, enumerations, and countable collections. -/
noncomputable def lowerTimelyDensity
    (S R : ℕ → α) (D : ℕ → ℕ) : ℝ :=
  liminf (timelyDensity S R D) atTop

/-- Definition 4's instance-level upper timely density. -/
noncomputable def upperTimelyDensity
    (S R : ℕ → α) (D : ℕ → ℕ) : ℝ :=
  limsup (timelyDensity S R D) atTop

/-- Definition 3's instance-level lower prefix-wise density. -/
noncomputable def lowerPrefixWiseDensity
    (S R : ℕ → α) (F : ℕ → ℕ) : ℝ :=
  liminf (prefixWiseDensity S R F) atTop

/-- Distinct generated values outside `L` by time `t`.  Under the paper's
fresh-output rule this is exactly `|A(E)_t \ L|`. -/
noncomputable def hallucinationCount
    (S : ℕ → α) (L : Set α) (t : ℕ) : ℕ := by
  classical
  exact ((sequencePrefix S t).filter fun x => x ∉ L).card

/-- Number of the first `i` target strings lying in an intermediate
language `L`. -/
noncomputable def targetIntersectionCount
    (R : ℕ → α) (L : Set α) (i : ℕ) : ℕ := by
  classical
  exact ((targetPrefix R i).filter fun x => x ∈ L).card

/-- Definition 1, with the limiting language's preference order made
explicit.  Indexing starts at zero instead of one. -/
structure MeasureZeroChain where
  limit : OrderedLanguage
  level : ℕ → Set ℕ
  nested : Monotone level
  union_eq : (⋃ j, level j) = limit.carrier
  sparse : ∀ j, limit.lowerDensity (level j) = 0

theorem MeasureZeroChain.level_subset_limit
    (C : MeasureZeroChain) (j : ℕ) :
    C.level j ⊆ C.limit.carrier := by
  intro x hx
  rw [← C.union_eq]
  exact Set.mem_iUnion.mpr ⟨j, hx⟩

theorem MeasureZeroChain.exists_level_of_mem
    (C : MeasureZeroChain) {x : ℕ}
    (hx : x ∈ C.limit.carrier) :
    ∃ j, x ∈ C.level j := by
  rw [← C.union_eq] at hx
  exact Set.mem_iUnion.mp hx

end GenLimit.TimeSensitive
