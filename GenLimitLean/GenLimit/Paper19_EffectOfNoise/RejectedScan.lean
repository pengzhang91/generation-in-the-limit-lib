import GenLimit.Paper19_EffectOfNoise.Separation
import Mathlib.Data.Nat.Nth

/-!
# Algorithm 1 with rejected scan iterations

Li--Zhang, *Characterizing the Effect of Noise in Language Generation in the
Limit*, arXiv:2601.21237v2, Algorithm 1.

`Separation.lean` compresses Algorithm 1 to its successful insertions.  This
module additionally transcribes the displayed infinite `for` loop.  It first
enumerates the outside-block indices increasingly as the source's
`i₀ < i₁ < ...`; each scan position then either inserts that candidate or
leaves the finite state unchanged.  Consequently rejected iterations are
represented explicitly.

This is an exact semantic transcription, not an effective runtime claim.
The source branch assumes only that certain sets are finite.  Turning those
proofs into `Finset`s, and enumerating an arbitrary infinite set increasingly,
uses classical choice.
-/

namespace GenLimit.QuantifyingNoise

/-! ## The source's increasing outside-block sequence -/

/-- The `n`th outside-block index in increasing order.  This is the source's
index `iₙ` before it renames `aₙ = s_{iₙ}`. -/
noncomputable def algorithmOutsideIndex
    (gen : GenLimit.Generic.Generator ColumnPoint) (n : ℕ) : ℕ :=
  Nat.nth (fun i => i ∈ outsideBlockIndices gen) n

theorem algorithmOutsideIndex_mem
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (n : ℕ) :
    algorithmOutsideIndex gen n ∈ outsideBlockIndices gen := by
  simpa [algorithmOutsideIndex] using
    Nat.nth_mem_of_infinite houtside n

theorem algorithmOutsideIndex_strictMono
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite) :
    StrictMono (algorithmOutsideIndex gen) := by
  simpa [algorithmOutsideIndex] using
    Nat.nth_strictMono houtside

theorem algorithmOutsideIndex_injective
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite) :
    Function.Injective (algorithmOutsideIndex gen) :=
  (algorithmOutsideIndex_strictMono gen houtside).injective

theorem algorithmOutsideIndex_range
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite) :
    Set.range (algorithmOutsideIndex gen) =
      outsideBlockIndices gen := by
  simpa [algorithmOutsideIndex] using
    Nat.range_nth_of_infinite houtside

/-! ## Literal accept/reject scan -/

/-- One iteration of Algorithm 1.  Membership in `algorithmForbidden`
is exactly the negation of the source condition
`a_i ∩ N = ∅ ∧ G(a'_i) ∉ L`, with the already chosen indices included
to make freshness explicit. -/
noncomputable def algorithmScanStep
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (chosen : Finset ℕ) (candidate : ℕ) : Finset ℕ :=
  if candidate ∉ algorithmForbidden gen hhits chosen then
    insert candidate chosen
  else
    chosen

theorem algorithmScanStep_of_accept
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (chosen : Finset ℕ) (candidate : ℕ)
    (haccept :
      candidate ∉ algorithmForbidden gen hhits chosen) :
    algorithmScanStep gen hhits chosen candidate =
      insert candidate chosen := by
  simp [algorithmScanStep, haccept]

theorem algorithmScanStep_of_reject
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (chosen : Finset ℕ) (candidate : ℕ)
    (hreject :
      candidate ∈ algorithmForbidden gen hhits chosen) :
    algorithmScanStep gen hhits chosen candidate = chosen := by
  simp [algorithmScanStep, hreject]

/-- The selected indices after the first `n` source-loop iterations. -/
noncomputable def algorithmRejectedScan
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
      algorithmScanStep gen hhits
        (algorithmRejectedScan gen hhits n)
        (algorithmOutsideIndex gen n)

theorem algorithmRejectedScan_succ
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (n : ℕ) :
    algorithmRejectedScan gen hhits (n + 1) =
      algorithmScanStep gen hhits
        (algorithmRejectedScan gen hhits n)
        (algorithmOutsideIndex gen n) := by
  rfl

/-- A source-loop position is a successful insertion exactly when its
candidate is outside the current finite forbidden set. -/
theorem algorithmRejectedScan_accepts_iff
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (n : ℕ) :
    (algorithmOutsideIndex gen n ∈
          algorithmRejectedScan gen hhits (n + 1) ∧
        algorithmOutsideIndex gen n ∉
          algorithmRejectedScan gen hhits n) ↔
      algorithmOutsideIndex gen n ∉
        algorithmForbidden gen hhits
          (algorithmRejectedScan gen hhits n) := by
  let q := algorithmOutsideIndex gen n
  let chosen := algorithmRejectedScan gen hhits n
  constructor
  · intro hnew hforbidden
    have hstep :
        algorithmRejectedScan gen hhits (n + 1) = chosen := by
      rw [algorithmRejectedScan_succ]
      exact algorithmScanStep_of_reject
        gen hhits chosen q hforbidden
    have hmem : q ∈ chosen := by
      rw [← hstep]
      exact hnew.1
    exact hnew.2 hmem
  · intro hnot
    have hnotChosen : q ∉ chosen := by
      intro hchosen
      exact hnot
        (chosen_subset_algorithmForbidden gen hhits chosen hchosen)
    have hstep :
        algorithmRejectedScan gen hhits (n + 1) =
          insert q chosen := by
      rw [algorithmRejectedScan_succ]
      exact algorithmScanStep_of_accept gen hhits chosen q hnot
    constructor
    · rw [hstep]
      exact Finset.mem_insert_self q chosen
    · exact hnotChosen

theorem algorithmRejectedScan_subset_succ
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (n : ℕ) :
    algorithmRejectedScan gen hhits n ⊆
      algorithmRejectedScan gen hhits (n + 1) := by
  intro i hi
  let q := algorithmOutsideIndex gen n
  let chosen := algorithmRejectedScan gen hhits n
  by_cases haccept :
      q ∉ algorithmForbidden gen hhits chosen
  · rw [algorithmRejectedScan_succ,
      algorithmScanStep_of_accept gen hhits chosen q haccept]
    exact Finset.mem_insert_of_mem hi
  · have hreject :
        q ∈ algorithmForbidden gen hhits chosen :=
      Classical.not_not.mp haccept
    rw [algorithmRejectedScan_succ,
      algorithmScanStep_of_reject gen hhits chosen q hreject]
    exact hi

theorem algorithmRejectedScan_mono
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    Monotone (algorithmRejectedScan gen hhits) :=
  monotone_nat_of_le_succ
    (algorithmRejectedScan_subset_succ gen hhits)

theorem algorithmForbidden_mono
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {chosen larger : Finset ℕ}
    (hsub : chosen ⊆ larger) :
    algorithmForbidden gen hhits chosen ⊆
      algorithmForbidden gen hhits larger := by
  classical
  intro q hq
  simp only [algorithmForbidden, Finset.mem_union,
    Finset.mem_image, Finset.mem_biUnion] at hq ⊢
  rcases hq with (hqChosen | ⟨i, hi, hiq⟩) |
      ⟨j, hj, hqHit⟩
  · exact Or.inl (Or.inl (hsub hqChosen))
  · exact Or.inl (Or.inr ⟨i, hsub hi, hiq⟩)
  · exact Or.inr ⟨j, hsub hj, hqHit⟩

theorem algorithmRejectedScan_mem_outside
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ∀ n i, i ∈ algorithmRejectedScan gen hhits n →
      i ∈ outsideBlockIndices gen := by
  intro n
  induction n with
  | zero =>
      intro i hi
      simp [algorithmRejectedScan] at hi
  | succ n ih =>
      intro i hi
      let q := algorithmOutsideIndex gen n
      let chosen := algorithmRejectedScan gen hhits n
      by_cases haccept :
          q ∉ algorithmForbidden gen hhits chosen
      · rw [algorithmRejectedScan_succ,
          algorithmScanStep_of_accept gen hhits chosen q haccept] at hi
        rcases Finset.mem_insert.mp hi with rfl | hiOld
        · exact algorithmOutsideIndex_mem gen houtside n
        · exact ih i hiOld
      · have hreject :
            q ∈ algorithmForbidden gen hhits chosen :=
          Classical.not_not.mp haccept
        rw [algorithmRejectedScan_succ,
          algorithmScanStep_of_reject gen hhits chosen q hreject] at hi
        exact ih i hi

/-- The source's `G(a'_i) ∉ L` invariant is preserved even across rejected
iterations. -/
theorem algorithmRejectedScan_conflictFree
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ∀ n,
      SelectionConflictFree gen
        (algorithmRejectedScan gen hhits n) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      simp [algorithmRejectedScan] at hi
  | succ n ih =>
      let chosen := algorithmRejectedScan gen hhits n
      let q := algorithmOutsideIndex gen n
      by_cases haccept :
          q ∉ algorithmForbidden gen hhits chosen
      · have hqOutside : q ∈ outsideBlockIndices gen :=
          algorithmOutsideIndex_mem gen houtside n
        rw [algorithmRejectedScan_succ,
          algorithmScanStep_of_accept gen hhits chosen q haccept]
        intro i hi j hj
        rcases Finset.mem_insert.mp hi with rfl | hiOld
        · rcases Finset.mem_insert.mp hj with rfl | hjOld
          · exact mem_outsideBlockIndices_iff.mp hqOutside
          · intro hbad
            apply haccept
            apply hit_mem_algorithmForbidden gen hhits hjOld
            exact ⟨hqOutside, hbad⟩
        · rcases Finset.mem_insert.mp hj with rfl | hjOld
          · intro hbad
            apply haccept
            have hfirst :
                (adversarialOutputColumn gen i).1 = q :=
              (adversarialBlock_mem_iff.mp hbad).1
            rw [← hfirst]
            exact outputFirst_mem_algorithmForbidden
              gen hhits hiOld
          · exact ih i hiOld j hjOld
      · have hreject :
            q ∈ algorithmForbidden gen hhits chosen :=
          Classical.not_not.mp haccept
        rw [algorithmRejectedScan_succ,
          algorithmScanStep_of_reject gen hhits chosen q hreject]
        exact ih

/-! ## The limiting accepted set and Algorithm 1's final branch -/

/-- Every index accepted at some finite scan time. -/
def algorithmRejectedScanIndices
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) : Set ℕ :=
  ⋃ n, (↑(algorithmRejectedScan gen hhits n) : Set ℕ)

theorem algorithmRejectedScanIndices_infinite
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    (algorithmRejectedScanIndices gen hhits).Infinite := by
  by_contra hnot
  have hfinite :
      (algorithmRejectedScanIndices gen hhits).Finite :=
    Set.not_infinite.mp hnot
  let all := hfinite.toFinset
  obtain ⟨q, hqOutside, hqNot⟩ :=
    houtside.exists_notMem_finset
      (algorithmForbidden gen hhits all)
  have hqRange :
      q ∈ Set.range (algorithmOutsideIndex gen) := by
    rw [algorithmOutsideIndex_range gen houtside]
    exact hqOutside
  obtain ⟨n, hn⟩ := hqRange
  have hscanSub :
      algorithmRejectedScan gen hhits n ⊆ all := by
    intro i hi
    apply hfinite.mem_toFinset.mpr
    exact Set.mem_iUnion.mpr ⟨n, hi⟩
  have hqNotCurrent :
      q ∉ algorithmForbidden gen hhits
        (algorithmRejectedScan gen hhits n) := by
    intro hqCurrent
    exact hqNot
      (algorithmForbidden_mono gen hhits hscanSub hqCurrent)
  have hcandNot :
      algorithmOutsideIndex gen n ∉
        algorithmForbidden gen hhits
          (algorithmRejectedScan gen hhits n) := by
    simpa [hn] using hqNotCurrent
  have hcandNew :=
    (algorithmRejectedScan_accepts_iff gen hhits n).2 hcandNot
  have hcandLimit :
      algorithmOutsideIndex gen n ∈
        algorithmRejectedScanIndices gen hhits :=
    Set.mem_iUnion.mpr ⟨n + 1, hcandNew.1⟩
  have hqLimit :
      q ∈ algorithmRejectedScanIndices gen hhits := by
    simpa [hn] using hcandLimit
  have hqAll : q ∈ all :=
    hfinite.mem_toFinset.mpr hqLimit
  exact hqNot
    (chosen_subset_algorithmForbidden gen hhits all hqAll)

theorem algorithmRejectedScanIndices_mem_outside
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {i : ℕ}
    (hi : i ∈ algorithmRejectedScanIndices gen hhits) :
    i ∈ outsideBlockIndices gen := by
  obtain ⟨n, hin⟩ := Set.mem_iUnion.mp hi
  exact algorithmRejectedScan_mem_outside
    gen houtside hhits n i hin

theorem algorithmRejectedScanIndices_conflictFree
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {i j : ℕ}
    (hi : i ∈ algorithmRejectedScanIndices gen hhits)
    (hj : j ∈ algorithmRejectedScanIndices gen hhits) :
    adversarialOutputColumn gen i ∉ adversarialBlock j := by
  obtain ⟨n, hin⟩ := Set.mem_iUnion.mp hi
  obtain ⟨m, hjm⟩ := Set.mem_iUnion.mp hj
  let k := max n m
  have hik :
      i ∈ algorithmRejectedScan gen hhits k :=
    algorithmRejectedScan_mono gen hhits
      (Nat.le_max_left n m) hin
  have hjk :
      j ∈ algorithmRejectedScan gen hhits k :=
    algorithmRejectedScan_mono gen hhits
      (Nat.le_max_right n m) hjm
  exact algorithmRejectedScan_conflictFree
    gen houtside hhits k i hik j hjk

/-- The literal scan's limiting target columns. -/
def algorithmRejectedScanBranchColumns
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    Set ColumnIndex :=
  {c | ∃ i,
    i ∈ algorithmRejectedScanIndices gen hhits ∧
    c ∈ adversarialBlock i}

theorem algorithmRejectedScanBranchColumns_nonempty
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    (algorithmRejectedScanBranchColumns gen hhits).Nonempty := by
  obtain ⟨i, hi⟩ :=
    (algorithmRejectedScanIndices_infinite gen houtside hhits).nonempty
  refine ⟨(i, 0), i, hi, ?_⟩
  exact adversarialBlock_mem_iff.mpr ⟨rfl, by omega⟩

theorem algorithmRejectedScanBranch_output_not_target
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {i : ℕ}
    (hi : i ∈ algorithmRejectedScanIndices gen hhits) :
    adversarialOutputColumn gen i ∉
      algorithmRejectedScanBranchColumns gen hhits := by
  intro hout
  obtain ⟨j, hj, houtBlock⟩ := hout
  exact algorithmRejectedScanIndices_conflictFree
    gen houtside hhits hi hj houtBlock

/-- The final branch of Theorem 2.17 through every accept/reject iteration of
the displayed Algorithm 1. -/
theorem algorithm_rejected_scan_branch_defeats_nonuniform
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ¬IsNonuniformGeneratorAtNoiseLevel gen columnUnionClass 1 := by
  apply infinite_full_blocks_defeat_nonuniform
    gen
    (algorithmRejectedScanIndices_infinite gen houtside hhits)
    (algorithmRejectedScanBranchColumns_nonempty
      gen houtside hhits)
  · intro i hi c hc
    exact ⟨i, hi, hc⟩
  · intro i hi
    exact algorithmRejectedScanBranch_output_not_target
      gen houtside hhits hi

/-- The complete lower bound with the literal rejected-iteration scan in its
third branch. -/
theorem columnUnionClass_defeats_every_generator_rejectedScan
    (gen : GenLimit.Generic.Generator ColumnPoint) :
    ¬IsNonuniformGeneratorAtNoiseLevel gen columnUnionClass 1 := by
  by_cases hinside : (insideBlockIndices gen).Infinite
  · exact infinite_inside_blocks_defeats_nonuniform gen hinside
  · have hinsideFinite :
        (insideBlockIndices gen).Finite :=
      Set.not_infinite.mp hinside
    have houtside : (outsideBlockIndices gen).Infinite :=
      hinsideFinite.infinite_compl
    by_cases hrepeat :
        ∃ j, (indicesHittingBlock gen j).Infinite
    · obtain ⟨j, hj⟩ := hrepeat
      exact infinite_hits_to_one_block_defeats_nonuniform gen hj
    · have hhits :
          ∀ j, (indicesHittingBlock gen j).Finite := by
        intro j
        exact Set.not_infinite.mp (fun h => hrepeat ⟨j, h⟩)
      exact algorithm_rejected_scan_branch_defeats_nonuniform
        gen houtside hhits

/-- Theorem 2.17 with Algorithm 1's rejected iterations retained. -/
theorem theorem_2_17_rejectedScan :
    UniformGeneratableAtNoiseLevel columnUnionClass 0 ∧
      ¬NonuniformGeneratableAtNoiseLevel columnUnionClass 1 := by
  refine ⟨columnUnionClass_uniform_noiseless, ?_⟩
  rintro ⟨gen, hgen⟩
  exact columnUnionClass_defeats_every_generator_rejectedScan gen hgen

end GenLimit.QuantifyingNoise
