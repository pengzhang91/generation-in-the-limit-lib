import GenLimit.Core.ClassGeneration
import Mathlib.Data.Set.Countable

/-!
# Indexed families and extensional language classes

Gold, Angluin, and KM use an indexed family, while #02 usually treats a class
extensionally as a set of languages.  This bridge records a chosen enumeration
without adding that representation choice to `GenLimit.Core`.
-/

namespace GenLimit.Bridge

/-- An indexed presentation of an extensional language class.  Repetitions
are allowed, exactly as in the source indexed-family models. -/
structure ClassEnumeration
    (H : GenLimit.Generic.LanguageClass α) where
  family : GenLimit.Generic.LanguageFamily α
  range_eq : Set.range family = H

namespace ClassEnumeration

/-- A nonempty countable class admits an indexed presentation.  Empty classes
are intentionally handled separately by clients, since no total `ℕ`-indexed
family has empty range. -/
noncomputable def ofCountable
    {H : GenLimit.Generic.LanguageClass α}
    (hCountable : H.Countable) (hNonempty : H.Nonempty) :
    ClassEnumeration H := by
  classical
  let hex := hCountable.exists_eq_range hNonempty
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).symm⟩

theorem family_mem
    {H : GenLimit.Generic.LanguageClass α}
    (E : ClassEnumeration H) (i : ℕ) : E.family i ∈ H := by
  exact (Set.ext_iff.mp E.range_eq (E.family i)).mp ⟨i, rfl⟩

theorem exists_index
    {H : GenLimit.Generic.LanguageClass α}
    (E : ClassEnumeration H) {L : GenLimit.Generic.Language α}
    (hL : L ∈ H) : ∃ i, E.family i = L := by
  exact (Set.ext_iff.mp E.range_eq L).mpr hL

/-- The all-languages-infinite assumption is invariant under the chosen
indexed presentation. -/
theorem uus_iff
    {H : GenLimit.Generic.LanguageClass α}
    (E : ClassEnumeration H) :
    GenLimit.Generic.UUS H ↔ ∀ i, (E.family i).Infinite := by
  constructor
  · intro hUUS i
    exact hUUS (E.family i) (E.family_mem i)
  · intro hInfinite L hL
    obtain ⟨i, rfl⟩ := E.exists_index hL
    exact hInfinite i

end ClassEnumeration
end GenLimit.Bridge
