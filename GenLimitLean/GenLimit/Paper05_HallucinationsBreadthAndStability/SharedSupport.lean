import GenLimit.Paper05_HallucinationsBreadthAndStability.InfiniteCoverage
import GenLimit.Paper05_HallucinationsBreadthAndStability.IncreasingCoverage
import GenLimit.Support.PredicateLock

/-! # Stable infinite coverage when the support may contain observations -/

namespace GenLimit.BreadthCharacterizations
open GenLimit.CharikarPabbaraju

/-- Theorem 8.7 also holds for the sample-allowing predicate in the caption
of Figure 4. Lock the support on the full universe, then remove an element
of that infinite support which has not appeared in the locking history. -/
theorem theorem_8_7_sampleAllowing :
    WeakAngluinCondition coSingletonNatFamily ∧
      ¬ ∃ G, IsStableGenerator G coSingletonNatFamily ∧
        SampleAllowingInfiniteCoverage G coSingletonNatFamily := by
  refine ⟨theorem_8_7.1, ?_⟩
  rintro ⟨G,stable,coverage⟩
  have base : Generic.Presents id (coSingletonNatFamily 0) := Set.range_id
  obtain ⟨xs,U,_,lock⟩ := Angluin.exists_lockingSequence_of_converges_with_base
    (M := G) base (fun s hp ↦ by
      obtain ⟨T,hT⟩ := stable 0 s hp
      exact ⟨supportAt G s T,T, fun t ht ↦ hT t T ht le_rfl⟩)
  have locked (j : ℕ) (hx : Angluin.ListWithin xs (coSingletonNatFamily j)) :
      U ⊆ coSingletonNatFamily j ∧ U.Infinite := by
    let s := Support.exactPresentation (coSingletonNatFamily j) (coSingletonNatFamily_nonempty j)
    have hp : Generic.Presents s (coSingletonNatFamily j) := Support.exactPresentation_presents ..
    obtain ⟨T,hT⟩ := coverage j _ (Angluin.prependStream_presents hx hp)
    have good := hT (xs.length+T) (Nat.le_add_left ..)
    simpa only [supportAt, Angluin.streamPrefix_prependStream, lock _ (fun _ _ ↦ Set.mem_univ _)] using good
  obtain ⟨w,hw,hfresh⟩ := (locked 0 (fun _ _ ↦ Set.mem_univ _)).2.exists_notMem_finset xs.toFinset
  have hsub := (locked (w+1) (fun x hx ↦ by
    have : x ≠ w := fun e ↦ hfresh (e ▸ List.mem_toFinset.mpr hx)
    simpa [coSingletonNatFamily] using this)).1
  simpa [coSingletonNatFamily] using hsub hw

/-- Freeze the integer tail starting with the first observation. Any ray
containing this observation contains the entire tail. -/
def firstRay (xs : List ℤ) : Set ℤ :=
  match xs with
  | [] => Set.univ
  | x :: _ => Set.Ici x

/-- Example 8.12 with sample-allowing infinite coverage. The first
observation determines a valid infinite support for the rest of the run. -/
theorem example_8_12 :
    ¬ WeakAngluinCondition integerRayFamily ∧ IsStableGenerator firstRay integerRayFamily ∧
      SampleAllowingInfiniteCoverage firstRay integerRayFamily := by
  have freeze (s : ℕ → ℤ) (t : ℕ) (ht : 1 ≤ t) :
      supportAt firstRay s t = Set.Ici (s 0) := by
    cases t with
    | zero => omega
    | succ t => simp [supportAt,firstRay,textPrefix,List.range_succ_eq_map]
  refine ⟨proposition_8_14_sampleAllowing.1, fun i s hp ↦ ⟨1,fun t u ht hu ↦
    (freeze s t ht).trans (freeze s u hu).symm⟩, fun i s hp ↦ ⟨1,fun t ht ↦ ?_⟩⟩
  rw [freeze s t ht]
  refine ⟨?_,Set.Ici_infinite _⟩
  have hx : s 0 ∈ integerRayFamily i := hp ▸ Set.mem_range_self 0
  cases i with
  | zero => exact Set.subset_univ _
  | succ i => exact Set.Ici_subset_Ici.mpr hx

/-- The literal support of Example 8.12, the naturals minus the first
observation, can keep a word outside the target forever. Both the zero-
and one-based conventions for the naturals include the word 1. -/
theorem example_8_12_printed_support_fails :
    ∃ (z : ℕ) (s : ℕ → ℤ), Generic.Presents s (integerRayFamily z) ∧
      (1 : ℤ) ∈ (Set.range (fun n : ℕ ↦ (n : ℤ)) \ {s 0}) ∧ 1 ∉ integerRayFamily z := by
  let z := Equiv.intEquivNat 3 + 1
  have he : integerRayFamily z = Set.Ici (3 : ℤ) := by simp [z,integerRayFamily]
  have ne : (integerRayFamily z).Nonempty := by rw [he]; exact ⟨3, by simp⟩
  let s := Support.exactPresentation (integerRayFamily z) ne
  have hp : Generic.Presents s (integerRayFamily z) := Support.exactPresentation_presents ..
  have h : s 0 ∈ integerRayFamily z := hp ▸ Set.mem_range_self 0
  rw [he] at h
  change 3 ≤ s 0 at h
  refine ⟨z,s,hp,⟨⟨1,by norm_num⟩,by simpa using (by omega : (1 : ℤ) ≠ s 0)⟩,?_⟩
  rw [he]
  change ¬ (3 : ℤ) ≤ 1
  norm_num

end GenLimit.BreadthCharacterizations
