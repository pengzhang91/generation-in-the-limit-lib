import GenLimit.Core.GenericGeneration
import GenLimit.Support.Fresh
import GenLimit.Support.ThresholdSelection

/-!
# Small selection helpers for #02 Learning Theory

These definitions collect concrete choices repeated by several proofs in the
paper development.  They deliberately live under the paper namespace rather
than in `GenLimit.Core`: they are proof machinery, not part of the shared
semantic interface.
-/

namespace GenLimit.LiRamanTewari.Common

/-- Choose a point of an infinite set outside a finite observed sample. -/
noncomputable def freshFromInfinite
    (C : Set α) (hC : C.Infinite) (seen : Finset α) : α :=
  GenLimit.Support.freshFromInfinite C hC seen

theorem freshFromInfinite_mem
    (C : Set α) (hC : C.Infinite) (seen : Finset α) :
    freshFromInfinite C hC seen ∈ C :=
  GenLimit.Support.freshFromInfinite_mem C hC seen

theorem freshFromInfinite_not_mem
    (C : Set α) (hC : C.Infinite) (seen : Finset α) :
    freshFromInfinite C hC seen ∉ seen :=
  GenLimit.Support.freshFromInfinite_not_mem C hC seen

/-- Paper02-facing alias for the shared padded threshold. -/
abbrev paddedThreshold (threshold : ℕ → ℕ) (n : ℕ) : ℕ :=
  GenLimit.Support.paddedThreshold threshold n

/-- Paper02-facing alias for the shared eligible component set. -/
abbrev eligibleIndices (threshold : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  GenLimit.Support.eligibleIndices threshold k

theorem mem_eligibleIndices_iff
    {threshold : ℕ → ℕ} {n k : ℕ} :
    n ∈ eligibleIndices threshold k ↔ paddedThreshold threshold n ≤ k :=
  GenLimit.Support.mem_eligibleIndices_iff

/-- The largest component whose padded threshold has been reached, with the
irrelevant default `0` when no component is eligible. -/
noncomputable abbrev largestEligible
    (threshold : ℕ → ℕ) (k : ℕ) : ℕ :=
  GenLimit.Support.largestEligible threshold k

theorem largestEligible_mem
    (threshold : ℕ → ℕ) (k : ℕ)
    (h : (eligibleIndices threshold k).Nonempty) :
    largestEligible threshold k ∈ eligibleIndices threshold k :=
  GenLimit.Support.largestEligible_mem threshold k h

theorem le_largestEligible
    (threshold : ℕ → ℕ) (k n : ℕ)
    (hn : n ∈ eligibleIndices threshold k) :
    n ≤ largestEligible threshold k :=
  GenLimit.Support.le_largestEligible threshold k n hn

theorem largestEligible_threshold_le
    (threshold : ℕ → ℕ) (k : ℕ)
    (h : (eligibleIndices threshold k).Nonempty) :
    threshold (largestEligible threshold k) ≤ k :=
  GenLimit.Support.largestEligible_threshold_le threshold k h

end GenLimit.LiRamanTewari.Common
