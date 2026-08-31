import GenLimit.Core.OrderedDensity
import Mathlib.Data.Nat.Find

/-!
# Ambient-order positions for the Kleinberg--Wei sequence

This file contains the ambient-order inverse and successor interface shared
by Papers #07 and #15. It is stronger than the paper-independent
`OrderedLanguage` density API: the enumeration must inherit the ambient
natural-number order.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback

/-- The target ordering is the restriction of the ambient natural-number
order.  This is the paper's universal-order convention, stronger than the
generic `OrderedLanguage` API used by earlier density definitions. -/
def InheritsAmbientOrder (K : OrderedLanguage) : Prop :=
  StrictMono K.enumeration

/-- The position of a target member in its duplicate-free ordering. -/
noncomputable def orderedPosition
    (K : OrderedLanguage) (x : ℕ) (hx : x ∈ K.carrier) : ℕ := by
  classical
  have hexists : ∃ i, K.enumeration i = x := by
    rw [← K.range_enumeration] at hx
    exact hx
  exact Nat.find hexists

theorem enumeration_orderedPosition
    (K : OrderedLanguage) (x : ℕ) (hx : x ∈ K.carrier) :
    K.enumeration (orderedPosition K x hx) = x := by
  classical
  exact Nat.find_spec (show ∃ i, K.enumeration i = x by
    rw [← K.range_enumeration] at hx
    exact hx)

/-- The successor of a carrier member in the specified ordering. -/
noncomputable def orderedSuccessor
    (K : OrderedLanguage) (x : ℕ) (hx : x ∈ K.carrier) : ℕ :=
  K.enumeration (orderedPosition K x hx + 1)

theorem orderedSuccessor_mem
    (K : OrderedLanguage) (x : ℕ) (hx : x ∈ K.carrier) :
    orderedSuccessor K x hx ∈ K.carrier := by
  rw [← K.range_enumeration]
  exact ⟨orderedPosition K x hx + 1, rfl⟩

theorem orderedSuccessor_ne
    (K : OrderedLanguage) (x : ℕ) (hx : x ∈ K.carrier) :
    orderedSuccessor K x hx ≠ x := by
  intro heq
  have :=
    K.enumeration_injective
      (heq.trans (enumeration_orderedPosition K x hx).symm)
  omega

theorem lt_orderedSuccessor
    (K : OrderedLanguage) (horder : InheritsAmbientOrder K)
    (x : ℕ) (hx : x ∈ K.carrier) :
    x < orderedSuccessor K x hx := by
  have hstep :=
    horder (Nat.lt_succ_self (orderedPosition K x hx))
  simpa [orderedSuccessor, enumeration_orderedPosition K x hx] using
    hstep

end GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback
