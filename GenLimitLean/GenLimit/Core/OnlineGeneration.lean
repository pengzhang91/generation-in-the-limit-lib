import GenLimit.Core.Basic

/-!
# Paper-independent online generation predicates

The KM developments currently package their limiting guarantees around their
particular generators.  These predicates expose the shared trace-level
specifications needed for comparisons with Gold identification.
-/

namespace GenLimit

/-- Eventually every output is a target element absent from the adversary
sample observed strictly before the same time.  This matches the conclusion
of the current KM developments. -/
def FreshGeneratesInLimit
    (stream output : ℕ → ℕ) (L : Language) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    output t ∈ L ∧ output t ∉ sample stream t

/-- The stronger DenseGeneration-style conclusion: outputs are valid, avoid
the adversary announcement through their own round, and never repeat an
earlier generator output. -/
def NovelGeneratesInLimit
    (stream output : ℕ → ℕ) (L : Language) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    output t ∈ L ∧
      output t ∉ sample stream (t + 1) ∧
      ∀ s, s < t → output s ≠ output t

/-- DenseGeneration-style novelty implies the KM-style freshness property. -/
theorem NovelGeneratesInLimit.fresh
    {stream output : ℕ → ℕ} {L : Language}
    (h : NovelGeneratesInLimit stream output L) :
    FreshGeneratesInLimit stream output L := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, -⟩ := hT t ht
  refine ⟨hmem, ?_⟩
  intro hsample
  exact hfresh (sample_mono (Nat.le_succ t) hsample)

end GenLimit
