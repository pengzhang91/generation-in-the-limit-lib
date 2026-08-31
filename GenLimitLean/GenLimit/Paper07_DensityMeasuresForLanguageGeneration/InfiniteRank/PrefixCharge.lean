import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.RunThinning
import Mathlib.Data.Nat.Nth

/-!
# From strict prefix dominance to an injective earlier charge

A dynamic argument often yields cardinal dominance in every strict prefix
before it yields an explicit matching.  This module proves that the nested
prefixes of `ℕ` make the matching canonical: send the retained position of
rank `k` to the output position of rank `k`.

The result closes the gap between a finite-prefix Hall inequality and the
`LongBadCharge` interface.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank

noncomputable local instance setMembershipDecidable (P : Set ℕ) :
    DecidablePred (fun i : ℕ => i ∈ P) :=
  Classical.decPred _

/-- `positionPrefixCount` is Mathlib's `Nat.count` for membership. -/
theorem positionPrefixCount_eq_natCount
    (P : Set ℕ) (n : ℕ) :
    positionPrefixCount P n =
      Nat.count (fun i => i ∈ P) n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

/-- Every retained position, together with all retained positions before it,
fits among output positions strictly before it. -/
def StrictPrefixDominance
    (retained output : Set ℕ) : Prop :=
  ∀ ⦃i : ℕ⦄, i ∈ retained →
    positionPrefixCount retained (i + 1) ≤
      positionPrefixCount output i

/-- Match a retained position of rank `k` to the output position of rank
`k`.  Values away from `retained` are irrelevant. -/
noncomputable def prefixDominanceCharge
    (retained output : Set ℕ) (i : ℕ) : ℕ := by
  classical
  exact
    Nat.nth (fun j => j ∈ output)
      (Nat.count (fun j => j ∈ retained) i)

theorem retainedRank_lt_outputCount
    {retained output : Set ℕ}
    (hdom : StrictPrefixDominance retained output)
    {i : ℕ} (hi : i ∈ retained) :
    Nat.count (fun j => j ∈ retained) i <
      Nat.count (fun j => j ∈ output) i := by
  classical
  have h := hdom hi
  rw [positionPrefixCount_eq_natCount,
    positionPrefixCount_eq_natCount,
    Nat.count_succ, if_pos hi] at h
  omega

theorem prefixDominanceCharge_earlier
    {retained output : Set ℕ}
    (hdom : StrictPrefixDominance retained output)
    {i : ℕ} (hi : i ∈ retained) :
    prefixDominanceCharge retained output i < i := by
  classical
  rw [prefixDominanceCharge]
  apply Nat.nth_lt_of_lt_count
  exact retainedRank_lt_outputCount hdom hi

theorem prefixDominanceCharge_mem
    {retained output : Set ℕ}
    (hdom : StrictPrefixDominance retained output)
    {i : ℕ} (hi : i ∈ retained) :
    prefixDominanceCharge retained output i ∈ output := by
  classical
  rw [prefixDominanceCharge]
  apply Nat.nth_mem
  intro hf
  exact
    (retainedRank_lt_outputCount hdom hi).trans_le
      (Nat.count_le_card hf i)

theorem prefixDominanceCharge_injOn
    {retained output : Set ℕ}
    (hdom : StrictPrefixDominance retained output) :
    Set.InjOn
      (prefixDominanceCharge retained output) retained := by
  classical
  intro i hi j hj hcharge
  rcases lt_trichotomy i j with hij | hij | hij
  · have hrank :
        Nat.count (fun k => k ∈ retained) i <
          Nat.count (fun k => k ∈ retained) j :=
      Nat.count_strict_mono hi hij
    have havailable :
        ∀ hf : {k | k ∈ output}.Finite,
          Nat.count (fun k => k ∈ retained) j <
            hf.toFinset.card := by
      intro hf
      exact
        (retainedRank_lt_outputCount hdom hj).trans_le
          (Nat.count_le_card hf j)
    have hlt :
        prefixDominanceCharge retained output i <
          prefixDominanceCharge retained output j :=
      Nat.nth_lt_nth' hrank havailable
    exact (ne_of_lt hlt hcharge).elim
  · exact hij
  · have hrank :
        Nat.count (fun k => k ∈ retained) j <
          Nat.count (fun k => k ∈ retained) i :=
      Nat.count_strict_mono hj hij
    have havailable :
        ∀ hf : {k | k ∈ output}.Finite,
          Nat.count (fun k => k ∈ retained) i <
            hf.toFinset.card := by
      intro hf
      exact
        (retainedRank_lt_outputCount hdom hi).trans_le
          (Nat.count_le_card hf i)
    have hlt :
        prefixDominanceCharge retained output j <
          prefixDominanceCharge retained output i :=
      Nat.nth_lt_nth' hrank havailable
    exact (ne_of_lt hlt hcharge.symm).elim

/-- Strict prefix dominance supplies the dynamic charge expected by
`LongBadCharge.ofRunThinning`; the static run thinning and finite-exception
accounting remain unchanged. -/
noncomputable def LongBadCharge.ofRunThinningOfPrefixDominance
    (K : OrderedLanguage) (Output Long : Language)
    (retained : Set ℕ)
    (C :
      RunThinning.Certificate
        (RunThinning.orderedPositions K Long) retained)
    (exceptions : Finset ℕ)
    (hdom :
      StrictPrefixDominance
        (retained \ (exceptions : Set ℕ))
        (RunThinning.orderedPositions K Output)) :
    LongBadCharge K Output Long :=
  LongBadCharge.ofRunThinning
    K Output Long retained C exceptions
    (prefixDominanceCharge
      (retained \ (exceptions : Set ℕ))
      (RunThinning.orderedPositions K Output))
    (fun _ hi => prefixDominanceCharge_earlier hdom hi)
    (fun _ hi => prefixDominanceCharge_mem hdom hi)
    (prefixDominanceCharge_injOn hdom)

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
