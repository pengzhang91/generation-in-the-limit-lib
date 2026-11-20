import GenLimit.NoRegretLanguageGeneration.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Sort

namespace PredictionToGeneration

theorem uus_iff_infinite_support (H : HypothesisClass X) :
    UUS H ↔ ∀ h, H h → Set.Infinite {x | h x = true} := by
  classical
  constructor
  · intro hu h hh hf
    obtain ⟨x,hx,hpos⟩ := hu h hh hf.toFinset.toList
    exact hx (by simpa using hpos)
  · intro hi h hh xs
    obtain ⟨x,hpos,hx⟩ := (hi h hh).exists_notMem_finset xs.toFinset
    exact ⟨x, by simpa using hx, hpos⟩

end PredictionToGeneration
