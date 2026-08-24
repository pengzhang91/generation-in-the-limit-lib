import GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.SweepGenerators
import Mathlib.Data.Set.Countable

/-!
# Hanneke--Karbasi--Mehrotra--Velegkas: the detailed EUC counterexample

Source: Steve Hanneke, Amin Karbasi, Anay Mehrotra, and Grigoris Velegkas,
*On Union-Closedness of Language Generation*, arXiv:2506.18642v1.

This module reuses the formalization of Definitions 2.6--2.7 from
`Paper02_LearningTheory.EventuallyUnboundedClosure` and formalizes detailed
Theorem 4.4.
The source sets `Σ* = ℤ`, writes `ℤ₋` for the negative integers, and takes

`ℒ = {ℤ₋ \ A | A ⊆ ℤ₋ and A is finite}`.

The class is non-uniformly generatable and fails Eventually Unbounded
Closure.  It is, however, countable.  Thus the displayed detailed Theorem 4.4
does not establish the word "uncountable" in overview Theorem 3.3; that
source-level mismatch is exposed by `cofiniteNegativeClass_countable`.
-/

namespace GenLimit.UnionClosedness

/-- The language class printed in Theorem 4.4. -/
def cofiniteNegativeClass : GenLimit.Generic.LanguageClass ℤ :=
  {L | ∃ A : Set ℤ,
    A ⊆ negativeIntegers ∧ A.Finite ∧ L = negativeIntegers \ A}

theorem negativeIntegers_mem_cofiniteNegativeClass :
    negativeIntegers ∈ cofiniteNegativeClass := by
  refine ⟨∅, Set.empty_subset _, Set.finite_empty, ?_⟩
  simp

theorem cofiniteNegativeClass_uus :
    GenLimit.Generic.UUS cofiniteNegativeClass := by
  intro L hL
  obtain ⟨A, _hAneg, hAfin, rfl⟩ := hL
  exact negativeIntegers_infinite.diff hAfin

/-- Every finite deletion of `ℤ₋` is indexed by a finite subset of a
countable set, so the detailed Theorem 4.4 class is countable. -/
theorem cofiniteNegativeClass_countable : cofiniteNegativeClass.Countable := by
  let finiteNegativeSets : Set (Set ℤ) :=
    {A | A.Finite ∧ A ⊆ negativeIntegers}
  have hfiniteNegativeSets : finiteNegativeSets.Countable := by
    simpa [finiteNegativeSets, and_comm] using
      Set.countable_setOf_finite_subset (Set.to_countable negativeIntegers)
  have himage :
      ((fun A : Set ℤ => negativeIntegers \ A) '' finiteNegativeSets).Countable :=
    hfiniteNegativeSets.image _
  apply himage.mono
  intro L hL
  obtain ⟨A, hAneg, hAfin, rfl⟩ := hL
  exact ⟨A, ⟨hAfin, hAneg⟩, rfl⟩

/-- The valid part of detailed Theorem 4.4: the displayed class is
non-uniformly generatable.  This is an immediate instance of P02's theorem
that every countable UUS class is non-uniformly generatable.

The source's stronger prose that this can be done "without samples" is not
part of the shared `NonuniformlyGeneratable` predicate and is not asserted by
this wrapper. -/
theorem cofiniteNegativeClass_nonuniformlyGeneratable :
    GenLimit.Generic.NonuniformlyGeneratable
      cofiniteNegativeClass :=
  GenLimit.LiRamanTewari.countable_classes_are_nonuniformly_generatable
    cofiniteNegativeClass_uus cofiniteNegativeClass_countable

theorem negativeCode_presents :
    GenLimit.Generic.Presents negativeCode negativeIntegers := by
  exact range_negativeCode

/-- For the Theorem 4.4 class, the common intersection of every version
space induced by a finite negative sample is exactly that sample. -/
theorem commonCore_cofiniteNegativeClass_eq
    (S : Finset ℤ) (hS : (↑S : Set ℤ) ⊆ negativeIntegers) :
    GenLimit.LiRamanTewari.commonCore cofiniteNegativeClass S =
      (↑S : Set ℤ) := by
  apply Set.Subset.antisymm
  · intro z hz
    have htargetVS :
        negativeIntegers ∈
          GenLimit.LiRamanTewari.versionSpace cofiniteNegativeClass S :=
      ⟨negativeIntegers_mem_cofiniteNegativeClass, hS⟩
    have hzneg : z ∈ negativeIntegers := hz negativeIntegers htargetVS
    by_contra hzS
    let Lz : Set ℤ := negativeIntegers \ {z}
    have hLzClass : Lz ∈ cofiniteNegativeClass := by
      refine ⟨{z}, ?_, Set.finite_singleton z, rfl⟩
      simpa only [Set.singleton_subset_iff] using hzneg
    have hSLz : (↑S : Set ℤ) ⊆ Lz := by
      intro y hy
      refine ⟨hS hy, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hyz
      subst y
      exact hzS hy
    have hLzVS :
        Lz ∈ GenLimit.LiRamanTewari.versionSpace
          cofiniteNegativeClass S := ⟨hLzClass, hSLz⟩
    have hzLz := hz Lz hLzVS
    exact hzLz.2 (by simp)
  · exact GenLimit.LiRamanTewari.sample_subset_commonCore

/-- The class has closure witnesses of every finite size. -/
theorem cofiniteNegativeClass_infiniteClosureDimension :
    GenLimit.LiRamanTewari.HasInfiniteClosureDimension
      cofiniteNegativeClass := by
  classical
  intro d
  let S : Finset ℤ := (Finset.range d).image negativeCode
  have hcard : S.card = d := by
    dsimp only [S]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i _hi j _hj hij
      exact negativeCode_injective hij
  have hS : (↑S : Set ℤ) ⊆ negativeIntegers := by
    intro z hz
    simp only [S, Finset.mem_coe, Finset.mem_image,
      Finset.mem_range] at hz
    obtain ⟨n, _hn, rfl⟩ := hz
    exact negativeCode_mem n
  refine ⟨S, hcard.ge, ?_⟩
  constructor
  · exact ⟨negativeIntegers,
      negativeIntegers_mem_cofiniteNegativeClass, hS⟩
  · change
      (GenLimit.LiRamanTewari.commonCore cofiniteNegativeClass S).Finite
    rw [commonCore_cofiniteNegativeClass_eq S hS]
    exact S.finite_toSet

/-- Contrary to the final sentence of the source proof of Theorem 4.4, the
displayed class is not uniformly generatable.  The theorem statement itself
only claims non-uniform generatability. -/
theorem cofiniteNegativeClass_not_uniformlyGeneratable :
    ¬GenLimit.Generic.UniformlyGeneratable
      cofiniteNegativeClass :=
  GenLimit.LiRamanTewari.closure_dimension_necessity
    cofiniteNegativeClass_uus
    cofiniteNegativeClass_infiniteClosureDimension

/-- The second valid part of detailed Theorem 4.4. -/
theorem cofiniteNegativeClass_not_eventuallyUnboundedClosure :
    ¬GenLimit.LiRamanTewari.EventuallyUnboundedClosure
      cofiniteNegativeClass := by
  intro hEUC
  obtain ⟨t, hinfinite⟩ :=
    hEUC negativeIntegers negativeIntegers_mem_cofiniteNegativeClass
      negativeCode negativeCode_presents
  have hsample :
      (↑(GenLimit.Generic.sample negativeCode t) : Set ℤ) ⊆
        negativeIntegers := by
    intro z hz
    obtain ⟨s, _hst, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hz
    exact negativeCode_mem s
  rw [commonCore_cofiniteNegativeClass_eq _ hsample] at hinfinite
  exact hinfinite (GenLimit.Generic.sample negativeCode t).finite_toSet

/-- Detailed Theorem 4.4, with exactly the two claims in its displayed
statement. -/
theorem theorem_4_4 :
    GenLimit.Generic.NonuniformlyGeneratable
        cofiniteNegativeClass ∧
      ¬GenLimit.LiRamanTewari.EventuallyUnboundedClosure
        cofiniteNegativeClass :=
  ⟨cofiniteNegativeClass_nonuniformlyGeneratable,
    cofiniteNegativeClass_not_eventuallyUnboundedClosure⟩

end GenLimit.UnionClosedness
