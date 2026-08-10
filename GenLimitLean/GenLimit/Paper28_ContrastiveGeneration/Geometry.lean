import GenLimit.Core.GenericGeneration

/-!
# Common-crossing geometry for contrastive identification

This file formalizes Definition 4.1, Proposition 4.2, Theorem 4.3, and
Lemma 4.4 of Li--Han--Jiang--Gao, *Contrastive Identification and Generation
in the Limit* (arXiv:2605.06211v1).

The source observes unordered two-element sets.  We use an oriented carrier
with distinct endpoints.  All predicates below are invariant under swapping
the endpoints, so this avoids quotient bookkeeping without changing the
common-crossing graph or its vertex set.
-/

namespace GenLimit
namespace ContrastiveGeneration

/-- A two-element observation, represented by two distinct endpoints. -/
structure Edge (α : Type*) where
  left : α
  right : α
  ne : left ≠ right

/-- An edge crosses the cut determined by the support `h`. -/
def Crosses (h : Set α) (e : Edge α) : Prop :=
  (e.left ∈ h ∧ e.right ∉ h) ∨
    (e.right ∈ h ∧ e.left ∉ h)

theorem crosses_swap_iff (h : Set α) (x y : α) (hxy : x ≠ y) :
    Crosses h ⟨x, y, hxy⟩ ↔
      Crosses h ⟨y, x, Ne.symm hxy⟩ := by
  simp only [Crosses]
  tauto

/-- The common crossing graph `Γ(h,g)`. -/
def CommonCrossing (h g : Set α) (e : Edge α) : Prop :=
  Crosses h e ∧ Crosses g e

/-- Incidence with one of the two endpoints. -/
def Incident (x : α) (e : Edge α) : Prop :=
  x = e.left ∨ x = e.right

/-- The vertex set `V(Γ(h,g))`. -/
def commonVertices (h g : Set α) : Set α :=
  {x | ∃ e : Edge α, CommonCrossing h g e ∧ Incident x e}

theorem right_not_mem_of_left_mem_of_crosses
    {h : Set α} {e : Edge α}
    (hleft : e.left ∈ h) (hcross : Crosses h e) :
    e.right ∉ h := by
  rcases hcross with hcross | hcross
  · exact hcross.2
  · exact False.elim (hcross.2 hleft)

theorem right_mem_of_left_not_mem_of_crosses
    {h : Set α} {e : Edge α}
    (hleft : e.left ∉ h) (hcross : Crosses h e) :
    e.right ∈ h := by
  rcases hcross with hcross | hcross
  · exact False.elim (hleft hcross.1)
  · exact hcross.1

theorem left_not_mem_of_right_mem_of_crosses
    {h : Set α} {e : Edge α}
    (hright : e.right ∈ h) (hcross : Crosses h e) :
    e.left ∉ h := by
  rcases hcross with hcross | hcross
  · exact False.elim (hcross.2 hright)
  · exact hcross.2

theorem left_mem_of_right_not_mem_of_crosses
    {h : Set α} {e : Edge α}
    (hright : e.right ∉ h) (hcross : Crosses h e) :
    e.left ∈ h := by
  rcases hcross with hcross | hcross
  · exact hcross.1
  · exact False.elim (hright hcross.1)

/-- The four regions from Theorem 4.3. -/
def bothPositive (h g : Set α) : Set α := h ∩ g
def hOnly (h g : Set α) : Set α := h \ g
def gOnly (h g : Set α) : Set α := g \ h
def bothNegative (h g : Set α) : Set α := (h ∪ g)ᶜ

/-- Theorem 4.3 at the common-crossing coverage level. -/
theorem theorem_4_3
    (h g : Set α) :
    h ⊆ commonVertices h g ↔
      ((bothPositive h g).Nonempty → (bothNegative h g).Nonempty) ∧
      ((hOnly h g).Nonempty → (gOnly h g).Nonempty) := by
  constructor
  · intro hcover
    constructor
    · rintro ⟨x, hxh, hxg⟩
      obtain ⟨e, hecross, hxe⟩ := hcover hxh
      rcases hxe with rfl | rfl
      · refine ⟨e.right, ?_⟩
        intro hy
        rcases hy with hy | hy
        · exact right_not_mem_of_left_mem_of_crosses hxh hecross.1 hy
        · exact right_not_mem_of_left_mem_of_crosses hxg hecross.2 hy
      · refine ⟨e.left, ?_⟩
        intro hy
        rcases hy with hy | hy
        · exact left_not_mem_of_right_mem_of_crosses hxh hecross.1 hy
        · exact left_not_mem_of_right_mem_of_crosses hxg hecross.2 hy
    · rintro ⟨x, hxh, hxg⟩
      obtain ⟨e, hecross, hxe⟩ := hcover hxh
      rcases hxe with rfl | rfl
      · refine ⟨e.right, ?_, ?_⟩
        · exact right_mem_of_left_not_mem_of_crosses hxg hecross.2
        · exact right_not_mem_of_left_mem_of_crosses hxh hecross.1
      · refine ⟨e.left, ?_, ?_⟩
        · exact left_mem_of_right_not_mem_of_crosses hxg hecross.2
        · exact left_not_mem_of_right_mem_of_crosses hxh hecross.1
  · rintro ⟨hAD, hBC⟩ x hxh
    by_cases hxg : x ∈ g
    · obtain ⟨y, hy⟩ := hAD ⟨x, hxh, hxg⟩
      have hyh : y ∉ h := fun h => hy (Or.inl h)
      have hyg : y ∉ g := fun h => hy (Or.inr h)
      have hxy : x ≠ y := by
        intro h
        subst y
        exact hyh hxh
      let e : Edge α := ⟨x, y, hxy⟩
      refine ⟨e, ?_, Or.inl rfl⟩
      exact
        ⟨Or.inl ⟨hxh, hyh⟩,
          Or.inl ⟨hxg, hyg⟩⟩
    · obtain ⟨y, hyg, hyh⟩ := hBC ⟨x, hxh, hxg⟩
      have hxy : x ≠ y := by
        intro h
        subst y
        exact hxg hyg
      let e : Edge α := ⟨x, y, hxy⟩
      refine ⟨e, ?_, Or.inl rfl⟩
      exact
        ⟨Or.inl ⟨hxh, hyh⟩,
          Or.inr ⟨hyg, hxg⟩⟩

/-- A valid contrastive presentation: every observed pair crosses the
target cut and every positive target point appears as an endpoint. -/
def IsContrastivePresentation
    (stream : ℕ → Edge α) (h : Set α) : Prop :=
  (∀ n, Crosses h (stream n)) ∧
    h ⊆ {x | ∃ n, Incident x (stream n)}

/-- Definition 4.1, non-eliminability direction: there is a valid
presentation for `h` every one of whose pairs also crosses `g`. -/
def NotEliminableFrom (g h : Set α) : Prop :=
  ∃ stream : ℕ → Edge α,
    IsContrastivePresentation stream h ∧
      ∀ n, Crosses g (stream n)

noncomputable def coveringEdge
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x : α) (hx : x ∈ h) : Edge α :=
  Classical.choose (hcover hx)

theorem coveringEdge_spec
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x : α) (hx : x ∈ h) :
    CommonCrossing h g (coveringEdge hcover x hx) ∧
      Incident x (coveringEdge hcover x hx) :=
  Classical.choose_spec (hcover hx)

noncomputable def presentationFromCoverage
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) : ℕ → Edge α := by
  classical
  exact fun n =>
    if hx : enumeration n ∈ h then
        coveringEdge hcover (enumeration n) hx
      else
        coveringEdge hcover x₀ hx₀

theorem presentationFromCoverage_common
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) (n : ℕ) :
    CommonCrossing h g
      (presentationFromCoverage hcover x₀ hx₀ enumeration n) := by
  by_cases hx : enumeration n ∈ h
  · simpa [presentationFromCoverage, hx] using
      (coveringEdge_spec hcover (enumeration n) hx).1
  · simpa [presentationFromCoverage, hx] using
      (coveringEdge_spec hcover x₀ hx₀).1

theorem presentationFromCoverage_covers
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α)
    (henum : h ⊆ Set.range enumeration) :
    h ⊆
      {x | ∃ n,
        Incident x
          (presentationFromCoverage hcover x₀ hx₀ enumeration n)} := by
  intro x hx
  obtain ⟨n, rfl⟩ := henum hx
  refine ⟨n, ?_⟩
  simpa [presentationFromCoverage, hx] using
    (coveringEdge_spec hcover (enumeration n) hx).2

/-- Proposition 4.2.  The explicit enumeration hypothesis is the paper's
countability/list-and-repeat convention for the positive support. -/
theorem proposition_4_2
    {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) (henum : h ⊆ Set.range enumeration) :
    NotEliminableFrom g h ↔ h ⊆ commonVertices h g := by
  constructor
  · rintro ⟨stream, hstream, hg⟩ x hx
    obtain ⟨n, hincident⟩ := hstream.2 hx
    exact ⟨stream n, ⟨hstream.1 n, hg n⟩, hincident⟩
  · intro hcover
    let stream :=
      presentationFromCoverage hcover x₀ hx₀ enumeration
    refine ⟨stream, ⟨?_, ?_⟩, ?_⟩
    · intro n
      exact (presentationFromCoverage_common
        hcover x₀ hx₀ enumeration n).1
    · exact presentationFromCoverage_covers
        hcover x₀ hx₀ enumeration henum
    · intro n
      exact (presentationFromCoverage_common
        hcover x₀ hx₀ enumeration n).2

/-- A single stream valid for both hypotheses. -/
def AdmitCommonPresentation (h g : Set α) : Prop :=
  ∃ stream : ℕ → Edge α,
    IsContrastivePresentation stream h ∧
      IsContrastivePresentation stream g

noncomputable def unionCoveringEdge
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x : α) (hx : x ∈ h ∪ g) : Edge α :=
  Classical.choose (hcover hx)

theorem unionCoveringEdge_spec
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x : α) (hx : x ∈ h ∪ g) :
    CommonCrossing h g (unionCoveringEdge hcover x hx) ∧
      Incident x (unionCoveringEdge hcover x hx) :=
  Classical.choose_spec (hcover hx)

noncomputable def commonPresentationFromCoverage
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α) : ℕ → Edge α := by
  classical
  exact fun n =>
    if hx : enumeration n ∈ h ∪ g then
        unionCoveringEdge hcover (enumeration n) hx
      else
        unionCoveringEdge hcover x₀ hx₀

theorem commonPresentationFromCoverage_common
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α) (n : ℕ) :
    CommonCrossing h g
      (commonPresentationFromCoverage hcover x₀ hx₀ enumeration n) := by
  by_cases hx : enumeration n ∈ h ∪ g
  · simpa [commonPresentationFromCoverage, hx] using
      (unionCoveringEdge_spec hcover (enumeration n) hx).1
  · simpa [commonPresentationFromCoverage, hx] using
      (unionCoveringEdge_spec hcover x₀ hx₀).1

theorem commonPresentationFromCoverage_covers
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α)
    (henum : h ∪ g ⊆ Set.range enumeration) :
    h ∪ g ⊆
      {x | ∃ n,
        Incident x
          (commonPresentationFromCoverage hcover x₀ hx₀ enumeration n)} := by
  intro x hx
  obtain ⟨n, rfl⟩ := henum hx
  refine ⟨n, ?_⟩
  simpa [commonPresentationFromCoverage, hx] using
    (unionCoveringEdge_spec hcover (enumeration n) hx).2

/-- Lemma 4.4.  The enumeration covers the union of the two supports, which
is automatic under the paper's countable-space assumption. -/
theorem lemma_4_4
    {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α)
    (henum : h ∪ g ⊆ Set.range enumeration) :
    AdmitCommonPresentation h g ↔
      h ∪ g ⊆ commonVertices h g := by
  constructor
  · rintro ⟨stream, hh, hg⟩ x hx
    rcases hx with hx | hx
    · obtain ⟨n, hincident⟩ := hh.2 hx
      exact ⟨stream n, ⟨hh.1 n, hg.1 n⟩, hincident⟩
    · obtain ⟨n, hincident⟩ := hg.2 hx
      exact ⟨stream n, ⟨hh.1 n, hg.1 n⟩, hincident⟩
  · intro hcover
    let stream : ℕ → Edge α :=
      commonPresentationFromCoverage hcover x₀ hx₀ enumeration
    have hstreamCommon : ∀ n, CommonCrossing h g (stream n) := by
      intro n
      exact commonPresentationFromCoverage_common
        hcover x₀ hx₀ enumeration n
    have hstreamCovers :
        h ∪ g ⊆ {x | ∃ n, Incident x (stream n)} := by
      exact commonPresentationFromCoverage_covers
        hcover x₀ hx₀ enumeration henum
    refine ⟨stream, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact fun n => (hstreamCommon n).1
    · exact fun x hx => hstreamCovers (Or.inl hx)
    · exact fun n => (hstreamCommon n).2
    · exact fun x hx => hstreamCovers (Or.inr hx)

end ContrastiveGeneration
end GenLimit
