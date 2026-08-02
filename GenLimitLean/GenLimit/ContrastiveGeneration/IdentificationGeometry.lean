import GenLimit.ContrastiveGeneration.Geometry

/-!
# The geometric core of the contrastive-identification characterization

This file formalizes the equivalence between conditions (ii) and (iii) in
Theorem 4.7 of Li--Han--Jiang--Gao, *Contrastive Identification and Generation
in the Limit* (arXiv:2605.06211v1).  The remaining equivalence with existence
of an identifier uses the paper's infinitary learning model and Angluin
tell-tales; the theorem below is the exact set-theoretic heart of that result.
-/

namespace GenLimit
namespace ContrastiveGeneration

/-- Two supports are incomparable under inclusion. -/
def Incomparable (h g : Set α) : Prop :=
  ¬h ⊆ g ∧ ¬g ⊆ h

/-- Definition 4.5: incomparable supports overlap and cover the universe. -/
def OverlappingCover (h g : Set α) : Prop :=
  (h ∩ g).Nonempty ∧ h ∪ g = Set.univ

/-- The contrastive non-eliminability relation, represented by Proposition
4.2's exact common-crossing coverage criterion, is contained in the
positive-data superset relation. -/
def NonEliminabilityContained (𝓗 : Set (Set α)) : Prop :=
  ∀ h ∈ 𝓗, ∀ g ∈ 𝓗,
    h ⊆ commonVertices h g → h ⊆ g

/-- Every incomparable pair in the class is an overlapping cover. -/
def IncomparablePairsOverlap (𝓗 : Set (Set α)) : Prop :=
  ∀ h ∈ 𝓗, ∀ g ∈ 𝓗,
    Incomparable h g → OverlappingCover h g

theorem incomparable_hOnly_nonempty
    {h g : Set α} (hinc : Incomparable h g) :
    (hOnly h g).Nonempty := by
  by_contra hempty
  apply hinc.1
  intro x hxh
  by_contra hxg
  exact hempty ⟨x, hxh, hxg⟩

theorem incomparable_gOnly_nonempty
    {h g : Set α} (hinc : Incomparable h g) :
    (gOnly h g).Nonempty := by
  by_contra hempty
  apply hinc.2
  intro x hxg
  by_contra hxh
  exact hempty ⟨x, hxg, hxh⟩

/-- The exact geometric implication from Theorem 4.7(ii) to (iii). -/
theorem nonEliminabilityContained_implies_overlap
    {𝓗 : Set (Set α)}
    (hrel : NonEliminabilityContained 𝓗) :
    IncomparablePairsOverlap 𝓗 := by
  intro h hh g hg hinc
  have hB : (hOnly h g).Nonempty :=
    incomparable_hOnly_nonempty hinc
  have hC : (gOnly h g).Nonempty :=
    incomparable_gOnly_nonempty hinc
  constructor
  · by_contra hA
    have hcover : h ⊆ commonVertices h g :=
      (theorem_4_3 h g).2
        ⟨fun hA' => False.elim (hA hA'), fun _ => hC⟩
    exact hinc.1 (hrel h hh g hg hcover)
  · apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hD : (bothNegative h g).Nonempty := by
      refine ⟨x, ?_⟩
      exact hx
    have hcover : h ⊆ commonVertices h g :=
      (theorem_4_3 h g).2
        ⟨fun _ => hD, fun _ => hC⟩
    exact hinc.1 (hrel h hh g hg hcover)

/-- The exact geometric implication from Theorem 4.7(iii) to (ii). -/
theorem incomparableOverlap_implies_nonEliminabilityContained
    {𝓗 : Set (Set α)}
    (hoverlap : IncomparablePairsOverlap 𝓗) :
    NonEliminabilityContained 𝓗 := by
  intro h hh g hg hcover
  by_contra hnsubset
  have hB : (hOnly h g).Nonempty := by
    by_contra hempty
    apply hnsubset
    intro x hxh
    by_contra hxg
    exact hempty ⟨x, hxh, hxg⟩
  have hregions :=
    (theorem_4_3 h g).1 hcover
  have hC : (gOnly h g).Nonempty :=
    hregions.2 hB
  have hinc : Incomparable h g := by
    constructor
    · exact hnsubset
    · by_contra hgsub
      obtain ⟨x, hxg, hxh⟩ := hC
      exact hxh (hgsub hxg)
  have hover := hoverlap h hh g hg hinc
  have hD : (bothNegative h g).Nonempty :=
    hregions.1 hover.1
  obtain ⟨x, hx⟩ := hD
  have hxuniv : x ∈ h ∪ g := by
    rw [hover.2]
    trivial
  exact hx hxuniv

/-- Theorem 4.7(ii) ↔ (iii), after replacing non-eliminability by the
equivalent common-crossing coverage relation from Proposition 4.2. -/
theorem theorem_4_7_geometric_equivalence
    (𝓗 : Set (Set α)) :
    NonEliminabilityContained 𝓗 ↔
      IncomparablePairsOverlap 𝓗 :=
  ⟨nonEliminabilityContained_implies_overlap,
    incomparableOverlap_implies_nonEliminabilityContained⟩

end ContrastiveGeneration
end GenLimit
