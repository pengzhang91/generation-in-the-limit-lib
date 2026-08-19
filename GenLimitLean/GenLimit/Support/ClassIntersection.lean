import GenLimit.Core.VersionSpace

/-!
# Intersections of language classes

The intersection of every language in a class is used independently by the
noisy-example and noise/loss developments.  It lives in `Support` rather than
`Core`: the core version-space API already contains the more general
`commonCore`, while this name keeps the paper-facing statements readable.
-/

namespace GenLimit.Support

/-- The set of examples belonging to every language in `C`. -/
abbrev classIntersection
    (C : GenLimit.Generic.LanguageClass α) : GenLimit.Generic.Language α :=
  {x | ∀ L, L ∈ C → x ∈ L}

theorem classIntersection_eq_commonCore_empty
    (C : GenLimit.Generic.LanguageClass α) :
    classIntersection C = GenLimit.Generic.commonCore C ∅ := by
  ext x
  simp [classIntersection, GenLimit.Generic.commonCore,
    GenLimit.Generic.versionSpace]

theorem classIntersection_subset_of_mem
    {C : GenLimit.Generic.LanguageClass α}
    {L : GenLimit.Generic.Language α} (hL : L ∈ C) :
    classIntersection C ⊆ L := by
  intro x hx
  exact hx L hL

end GenLimit.Support
