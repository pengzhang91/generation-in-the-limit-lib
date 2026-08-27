import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.SuccPred.Tree

/-!
# Finite least-common-ancestor chains

This file formalizes the finite rooted-tree bookkeeping isolated as
Claim 4.18 in Kleinberg--Wei,
*Validity, Sparse Holes, and Breadth in Language Generation: Banach Density,
Topology, and Geometry* (arXiv:2604.02385v2).

We use the standard order-theoretic representation of a rooted tree:
ancestors are smaller and the infimum of two vertices is their least common
ancestor.  The source's depth bound is exposed as a strictly monotone natural
rank `depth`; this avoids tying the theorem to a particular graph encoding.
-/

namespace GenLimit
namespace KleinbergWei
namespace Banach

/-- Least common ancestor of the first `n+1` vertices of a sequence. -/
def prefixLCA {Vertex : Type*} [SemilatticeInf Vertex]
    (vertices : ℕ → Vertex) : ℕ → Vertex
  | 0 => vertices 0
  | n + 1 => prefixLCA vertices n ⊓ vertices (n + 1)

@[simp] theorem prefixLCA_zero
    {Vertex : Type*} [SemilatticeInf Vertex]
    (vertices : ℕ → Vertex) :
    prefixLCA vertices 0 = vertices 0 :=
  rfl

@[simp] theorem prefixLCA_succ
    {Vertex : Type*} [SemilatticeInf Vertex]
    (vertices : ℕ → Vertex) (n : ℕ) :
    prefixLCA vertices (n + 1) =
      prefixLCA vertices n ⊓ vertices (n + 1) :=
  rfl

/-- Adding a vertex can only move the least common ancestor toward the
root. -/
theorem prefixLCA_succ_le
    {Vertex : Type*} [SemilatticeInf Vertex]
    (vertices : ℕ → Vertex) (n : ℕ) :
    prefixLCA vertices (n + 1) ≤ prefixLCA vertices n := by
  simp

/-- First conclusion of Claim 4.18: prefix least common ancestors form the
paper's monotone ancestral chain. -/
theorem claim_4_18_monotone_ancestral_chain
    {Vertex : Type*} [SemilatticeInf Vertex]
    (vertices : ℕ → Vertex) :
    Antitone (prefixLCA vertices) := by
  apply antitone_nat_of_succ_le
  exact prefixLCA_succ_le vertices

/-- Recursive number of strict changes among the first `n` transitions of
the prefix-LCA chain. -/
noncomputable def prefixLCAChangeCount
    {Vertex : Type*} [SemilatticeInf Vertex] [DecidableEq Vertex]
    (vertices : ℕ → Vertex) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      prefixLCAChangeCount vertices n +
        if prefixLCA vertices (n + 1) = prefixLCA vertices n then 0 else 1

@[simp] theorem prefixLCAChangeCount_zero
    {Vertex : Type*} [SemilatticeInf Vertex] [DecidableEq Vertex]
    (vertices : ℕ → Vertex) :
    prefixLCAChangeCount vertices 0 = 0 :=
  rfl

@[simp] theorem prefixLCAChangeCount_succ
    {Vertex : Type*} [SemilatticeInf Vertex] [DecidableEq Vertex]
    (vertices : ℕ → Vertex) (n : ℕ) :
    prefixLCAChangeCount vertices (n + 1) =
      prefixLCAChangeCount vertices n +
        if prefixLCA vertices (n + 1) = prefixLCA vertices n then 0 else 1 :=
  rfl

/-- The source's literal set `C` of indices at which the prefix LCA changes.
The zero index is excluded, so the set records transitions `i-1 → i`. -/
noncomputable def prefixLCAChangeIndices
    {Vertex : Type*} [SemilatticeInf Vertex] [DecidableEq Vertex]
    (vertices : ℕ → Vertex) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun i =>
    prefixLCA vertices i ≠ prefixLCA vertices (i - 1)

/-- The recursive counter is exactly the cardinality of the source's change
index set. -/
theorem prefixLCAChangeCount_eq_card
    {Vertex : Type*} [SemilatticeInf Vertex] [DecidableEq Vertex]
    (vertices : ℕ → Vertex) :
    ∀ n,
      prefixLCAChangeCount vertices n =
        (prefixLCAChangeIndices vertices n).card := by
  intro n
  induction n with
  | zero =>
      simp [prefixLCAChangeIndices]
  | succ n ih =>
      rw [prefixLCAChangeCount_succ, ih]
      simp only [prefixLCAChangeIndices]
      have hIcc :
          Finset.Icc 1 (n + 1) =
            insert (n + 1) (Finset.Icc 1 n) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc]
      rw [Finset.filter_insert]
      have hnotmem : n + 1 ∉ Finset.Icc 1 n := by
        simp
      by_cases hsame :
          prefixLCA vertices (n + 1) = prefixLCA vertices n
      · have hsame' :
            prefixLCA vertices n ⊓ vertices (n + 1) =
              prefixLCA vertices n := by
          simpa using hsame
        simp [hsame']
      · have hsame' :
            prefixLCA vertices n ⊓ vertices (n + 1) ≠
              prefixLCA vertices n := by
          simpa using hsame
        simp [hsame', hnotmem]

/-- Each strict movement toward the root consumes at least one unit of
depth.  This is the accounting invariant behind the second part of
Claim 4.18. -/
theorem prefixLCAChangeCount_add_depth_le
    {Vertex : Type*} [SemilatticeInf Vertex] [DecidableEq Vertex]
    (vertices : ℕ → Vertex) (depth : Vertex → ℕ)
    (hdepth : StrictMono depth) :
    ∀ n,
      prefixLCAChangeCount vertices n +
          depth (prefixLCA vertices n) ≤
        depth (vertices 0) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      by_cases hsame :
          prefixLCA vertices (n + 1) = prefixLCA vertices n
      · rw [prefixLCAChangeCount_succ, if_pos hsame, hsame,
          Nat.add_zero]
        exact ih
      · have hle :
            prefixLCA vertices (n + 1) ≤
              prefixLCA vertices n :=
          prefixLCA_succ_le vertices n
        have hlt :
            prefixLCA vertices (n + 1) <
              prefixLCA vertices n :=
          lt_of_le_of_ne hle hsame
        have hdepth_lt :
            depth (prefixLCA vertices (n + 1)) <
              depth (prefixLCA vertices n) :=
          hdepth hlt
        simp only [prefixLCAChangeCount_succ, if_neg hsame]
        omega

/-- Second conclusion of Claim 4.18: in a rooted tree of depth at most `r`,
the prefix-LCA chain changes strictly at most `r` times. -/
theorem claim_4_18_change_bound
    {Vertex : Type*} [SemilatticeInf Vertex] [DecidableEq Vertex]
    (vertices : ℕ → Vertex) (depth : Vertex → ℕ) (r : ℕ)
    (hdepth : StrictMono depth)
    (hrootDepth : depth (vertices 0) ≤ r)
    (n : ℕ) :
    prefixLCAChangeCount vertices n ≤ r := by
  have hinvariant :=
    prefixLCAChangeCount_add_depth_le vertices depth hdepth n
  omega

/-- Claim 4.18 with the source's literal cardinality `|C|`. -/
theorem claim_4_18_change_index_card_bound
    {Vertex : Type*} [SemilatticeInf Vertex] [DecidableEq Vertex]
    (vertices : ℕ → Vertex) (depth : Vertex → ℕ) (r : ℕ)
    (hdepth : StrictMono depth)
    (hrootDepth : depth (vertices 0) ≤ r)
    (n : ℕ) :
    (prefixLCAChangeIndices vertices n).card ≤ r := by
  rw [← prefixLCAChangeCount_eq_card]
  exact claim_4_18_change_bound
    vertices depth r hdepth hrootDepth n

/-- Claim 4.20: if the LCA of an ordered list of at least two vertices is
`Q`, then some adjacent pair in that ordering already has LCA `Q`.

Here the list has entries `vertices 0, ..., vertices (n + 1)`, so it always
contains at least two vertices.  Unlike Claim 4.18, this conclusion is false
for an arbitrary meet-semilattice: three sets can have empty total
intersection while every adjacent pair has nonempty intersection.  The
additional `PredOrder` and `IsPredArchimedean` instances are Mathlib's
order-theoretic rooted-tree condition.  They imply that any two ancestors of
one vertex are comparable, which is exactly the tree property used below. -/
theorem claim_4_20_adjacent_pair_lca
    {Vertex : Type*} [SemilatticeInf Vertex]
    [PredOrder Vertex] [IsPredArchimedean Vertex]
    (vertices : ℕ → Vertex) (Q : Vertex) :
    ∀ n,
      prefixLCA vertices (n + 1) = Q →
        ∃ i, i ≤ n ∧
          vertices i ⊓ vertices (i + 1) = Q := by
  intro n hglobal
  induction n with
  | zero =>
      refine ⟨0, by omega, ?_⟩
      simpa only [Nat.zero_add, prefixLCA_succ, prefixLCA_zero] using hglobal
  | succ n ih =>
      by_cases hprefix : prefixLCA vertices (n + 1) = Q
      · obtain ⟨i, hi, hpair⟩ := ih hprefix
        exact ⟨i, by omega, hpair⟩
      · refine ⟨n + 1, by omega, ?_⟩
        have hmeet :
            prefixLCA vertices (n + 1) ⊓ vertices (n + 2) = Q := by
          simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
            prefixLCA_succ] using hglobal
        have hprefix_le_last :
            prefixLCA vertices (n + 1) ≤ vertices (n + 1) := by
          rw [prefixLCA_succ]
          exact inf_le_right
        have hpair_le_last :
            vertices (n + 1) ⊓ vertices (n + 2) ≤
              vertices (n + 1) :=
          inf_le_left
        rcases le_total_of_directed hpair_le_last hprefix_le_last with
          hpair_le_prefix | hprefix_le_pair
        · apply le_antisymm
          · calc
              vertices (n + 1) ⊓ vertices (n + 2) ≤
                  prefixLCA vertices (n + 1) ⊓ vertices (n + 2) :=
                le_inf hpair_le_prefix inf_le_right
              _ = Q := hmeet
          · calc
              Q = prefixLCA vertices (n + 1) ⊓ vertices (n + 2) :=
                hmeet.symm
              _ ≤ vertices (n + 1) ⊓ vertices (n + 2) :=
                inf_le_inf_right _ hprefix_le_last
        · have hprefix_le_next :
              prefixLCA vertices (n + 1) ≤ vertices (n + 2) :=
            hprefix_le_pair.trans inf_le_right
          have hprefix_eq : prefixLCA vertices (n + 1) = Q := by
            calc
              prefixLCA vertices (n + 1) =
                  prefixLCA vertices (n + 1) ⊓ vertices (n + 2) :=
                (inf_eq_left.mpr hprefix_le_next).symm
              _ = Q := hmeet
          exact (hprefix hprefix_eq).elim

end Banach
end KleinbergWei
end GenLimit
