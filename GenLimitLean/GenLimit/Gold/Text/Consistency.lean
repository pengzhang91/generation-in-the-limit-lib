import GenLimit.Gold.Text.Model

/-!
# Positive compatibility of a finite Gold history

Gold learners receive an ordered list, but positive-data compatibility forgets
the order and repetition pattern: every observed value must belong to the
conjectured language.  On a stream prefix this is exactly the shared
`GenLimit.Consistent` predicate used by the KM and DenseGeneration
developments.
-/

namespace GenLimit
namespace Gold
namespace Text

/-- A positive-data history is compatible with `L` when every observation in
the history belongs to `L`. -/
def PositiveCompatible (history : List ℕ) (L : Language) : Prop :=
  ∀ u ∈ history, u ∈ L

theorem positiveCompatible_iff_toFinset_subset
    {history : List ℕ} {L : Language} :
    PositiveCompatible history L ↔
      (↑history.toFinset : Set ℕ) ⊆ L := by
  constructor
  · intro h u hu
    exact h u (by simpa using hu)
  · intro h u hu
    exact h (by simpa using hu)

/-- Compatibility of the ordered Gold prefix is exactly consistency of its
underlying finite sample. -/
theorem positiveCompatible_textPrefix_iff_consistent
    (C : LanguageFamily) (stream : ℕ → ℕ) (t i : ℕ) :
    PositiveCompatible (textPrefix stream t) (C i) ↔
      Consistent C stream t i := by
  rw [positiveCompatible_iff_toFinset_subset, textPrefix_toFinset]
  rfl

end Text
end Gold
end GenLimit
