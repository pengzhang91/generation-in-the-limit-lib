import GenLimit.Support.FiniteTellTale
import GenLimit.Paper00_LanguageIdentification.Text.Superfinite
import GenLimit.Paper15_PartialEnumeration.FullTopology

/-!
# Example: one canonical finite tell-tale API

The shared predicate lives in `GenLimit.Generic`.  Paper #0 and Paper #15
retain paper-facing abbreviations, so a proof using the canonical predicate
can be passed to either development without conversion lemmas.
-/

namespace GenLimit.Examples

theorem singleton_class_has_finite_tell_tale
    {L : Generic.Language α} {T : Finset α}
    (hTL : (↑T : Set α) ⊆ L) :
    Generic.IsFiniteTellTale ({L} : Generic.LanguageClass α) L T := by
  refine ⟨hTL, ?_⟩
  intro K hK _ _
  simpa only [Set.mem_singleton_iff] using hK

theorem canonical_tell_tale_usable_by_gold
    {C : Set GenLimit.Language} {L : GenLimit.Language} {T : Finset ℕ}
    (hT : Generic.IsFiniteTellTale C L T) :
    GenLimit.Gold.Text.IsTellTale C L T :=
  hT

theorem canonical_tell_tale_usable_by_full_topology
    {X : Set GenLimit.Language}
    {K : GenLimit.KleinbergWei.PartialEnumeration.FullTopology.Point X}
    {T : Finset ℕ}
    (hT : Generic.IsFiniteTellTale X K.1 T) :
    GenLimit.KleinbergWei.PartialEnumeration.FullTopology.IsTellTale K T :=
  hT

end GenLimit.Examples
