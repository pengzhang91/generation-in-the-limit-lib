import GenLimit.Paper28_ContrastiveGeneration.GenerationCores
import Mathlib.Data.Finset.Card

/-!
# #28 Contrastive Generation: closure dimension

This file formalizes Definitions 5.1--5.3 and Theorem 5.4 of
Li--Han--Jiang--Gao, *Contrastive Identification and Generation in the
Limit* (arXiv:2605.06211v1).

Unlike the oriented implementation carrier `Edge`, the finite-edge carrier
below stores the unordered two-element vertex set itself.  Thus observing
`{x,y}` and later observing `{y,x}` never increases the distinct-edge count.
The theorem is stated with a finite cardinal bound rather than an extended
natural supremum:

`ContrastiveClosureDimensionAtMost 𝓗 d`

means exactly that every finite hollow edge set has at most `d` members.
This is equivalent to `CΔ(𝓗) ≤ d` and avoids hiding the empty-supremum
convention inside an encoding of `ℕ ∪ {∞}`.
-/

namespace GenLimit
namespace ContrastiveGeneration

/-- An unordered two-element edge, represented by its vertex finset. -/
structure UnorderedEdge (α : Type*) where
  vertices : Finset α
  card_eq_two : vertices.card = 2

theorem UnorderedEdge.ext
    {p q : UnorderedEdge α} (h : p.vertices = q.vertices) :
    p = q := by
  cases p
  cases q
  simp_all

/-- Forget the orientation of the implementation carrier `Edge`. -/
noncomputable def Edge.unordered (e : Edge α) : UnorderedEdge α := by
  classical
  exact ⟨{e.left, e.right}, Finset.card_pair e.ne⟩

/-- An unordered edge crosses a support when one of its two vertices is
positive and the other is negative. -/
def UnorderedCrosses (h : Set α) (p : UnorderedEdge α) : Prop :=
  ∃ x, x ∈ p.vertices ∧ x ∈ h ∧
    ∃ y, y ∈ p.vertices ∧ y ∉ h

theorem unorderedCrosses_edge_iff
    (h : Set α) (e : Edge α) :
    UnorderedCrosses h e.unordered ↔ Crosses h e := by
  classical
  constructor
  · rintro ⟨x, hx, hxh, y, hy, hyh⟩
    simp only [Edge.unordered, Finset.mem_insert,
      Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;>
      rcases hy with rfl | rfl
    · exact False.elim (hyh hxh)
    · exact Or.inl ⟨hxh, hyh⟩
    · exact Or.inr ⟨hxh, hyh⟩
    · exact False.elim (hyh hxh)
  · intro hcross
    rcases hcross with hcross | hcross
    · exact
        ⟨e.left, by simp [Edge.unordered], hcross.1,
          e.right, by simp [Edge.unordered], hcross.2⟩
    · exact
        ⟨e.right, by simp [Edge.unordered], hcross.1,
          e.left, by simp [Edge.unordered], hcross.2⟩

theorem exists_orientation (p : UnorderedEdge α) :
    ∃ e : Edge α, e.unordered = p := by
  classical
  obtain ⟨x, y, hxy, hp⟩ :=
    Finset.card_eq_two.mp p.card_eq_two
  refine ⟨⟨x, y, hxy⟩, ?_⟩
  apply UnorderedEdge.ext
  simpa [Edge.unordered] using hp.symm

/-- A fixed orientation of an unordered edge.  Its choice is never observed
by any theorem statement. -/
noncomputable def UnorderedEdge.orient
    (p : UnorderedEdge α) : Edge α :=
  Classical.choose (exists_orientation p)

theorem UnorderedEdge.orient_unordered
    (p : UnorderedEdge α) :
    p.orient.unordered = p :=
  Classical.choose_spec (exists_orientation p)

theorem unorderedCrosses_orient_iff
    (h : Set α) (p : UnorderedEdge α) :
    Crosses h p.orient ↔ UnorderedCrosses h p := by
  rw [← unorderedCrosses_edge_iff h p.orient,
    p.orient_unordered]

/-- The orientation-invariant set of distinct pairs in a finite history. -/
noncomputable def distinctUnorderedEdges
    {t : ℕ} (history : Fin t → Edge α) :
    Finset (UnorderedEdge α) := by
  classical
  exact Finset.univ.image (fun i => (history i).unordered)

/-- The vertices incident to a finite unordered edge set. -/
def unorderedVertices
    (E : Finset (UnorderedEdge α)) : Set α :=
  {x | ∃ p, p ∈ E ∧ x ∈ p.vertices}

theorem seenPrefix_eq_unorderedVertices
    {t : ℕ} (history : Fin t → Edge α) :
    seenPrefix history =
      unorderedVertices (distinctUnorderedEdges history) := by
  classical
  ext x
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨(history i).unordered, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · rcases hi with rfl | rfl <;>
        simp [Edge.unordered]
  · rintro ⟨p, hp, hxp⟩
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hp
    simp only [Edge.unordered, Finset.mem_insert,
      Finset.mem_singleton] at hxp
    rcases hxp with hxp | hxp
    · exact ⟨i, Or.inl hxp⟩
    · exact ⟨i, Or.inr hxp⟩

/-- Definition 5.1's edge-induced version space for a finite unordered edge
set. -/
def unorderedVersionSpace
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) :
    Set (Set α) :=
  {h | h ∈ 𝓗 ∧ ∀ p, p ∈ E → UnorderedCrosses h p}

/-- Definition 5.1's edge-induced closure, with the paper's empty-version
space convention. -/
noncomputable def unorderedClosure
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) :
    Set α := by
  classical
  exact
    if (unorderedVersionSpace 𝓗 E).Nonempty then
      {x | ∀ h, h ∈ unorderedVersionSpace 𝓗 E → x ∈ h}
    else
      ∅

theorem unorderedClosure_subset_version
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    {h : Set α} (hh : h ∈ unorderedVersionSpace 𝓗 E) :
    unorderedClosure 𝓗 E ⊆ h := by
  have hnonempty : (unorderedVersionSpace 𝓗 E).Nonempty :=
    ⟨h, hh⟩
  simp only [unorderedClosure, if_pos hnonempty]
  intro x hx
  exact hx h hh

/-- Definition 5.3: all currently forced positives are already incident to
the observed finite edge set. -/
def IsContrastivelyHollow
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) : Prop :=
  (unorderedVersionSpace 𝓗 E).Nonempty ∧
    unorderedClosure 𝓗 E ⊆ unorderedVertices E

/-- The finite-bound form of `CΔ(𝓗) ≤ d`. -/
def ContrastiveClosureDimensionAtMost
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ∀ E : Finset (UnorderedEdge α),
    IsContrastivelyHollow 𝓗 E → E.card ≤ d

/-- Finiteness of the contrastive closure dimension. -/
def FiniteContrastiveClosureDimension
    (𝓗 : Set (Set α)) : Prop :=
  ∃ d, ContrastiveClosureDimensionAtMost 𝓗 d

/-- The finite value `CΔ(𝓗)=d`, represented as the least natural upper
bound on cardinalities of hollow edge sets.  This includes the source's
empty-supremum value `0` without requiring a hollow witness of size zero. -/
def ContrastiveClosureDimensionEquals
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ContrastiveClosureDimensionAtMost 𝓗 d ∧
    ∀ b, ContrastiveClosureDimensionAtMost 𝓗 b → d ≤ b

/-- Definition 5.2 at one distinct-edge threshold, written directly for all
finite crossing prefixes.  This is equivalent to quantifying over prefixes
of crossing-edge streams, since a finite crossing prefix can be continued by
repeating any one crossing edge whenever the threshold is met. -/
def UniformlyContrastivelyGeneratesAt
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α))
    (d : ℕ) : Prop :=
  ∀ h, h ∈ 𝓗 → ∀ t, ∀ history : Fin t → Edge α,
    (∀ i, Crosses h (history i)) →
    d ≤ (distinctUnorderedEdges history).card →
      G t history ∈ h ∧ G t history ∉ seenPrefix history

/-- Existence of a uniform generator at one distinct-edge threshold. -/
def UniformlyContrastivelyGeneratableAt
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ∃ G : ContrastiveGenerator α,
    UniformlyContrastivelyGeneratesAt G 𝓗 d

/-- Existence of a uniform contrastive generator at some finite
distinct-edge threshold. -/
def UniformlyContrastivelyGeneratable
    (𝓗 : Set (Set α)) : Prop :=
  ∃ d, UniformlyContrastivelyGeneratableAt 𝓗 d

/-- `d` is the least *positive* distinct-edge threshold at which uniform
generation is possible.  Positive thresholds match the source's round
convention and remove the otherwise vacuous distinction between thresholds
zero and one when prefixes start after the first observation. -/
def IsLeastPositiveUniformThreshold
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  0 < d ∧
    UniformlyContrastivelyGeneratableAt 𝓗 d ∧
    ∀ k, 0 < k →
      UniformlyContrastivelyGeneratableAt 𝓗 k → d ≤ k

theorem uniformThreshold_mono
    {G : ContrastiveGenerator α} {𝓗 : Set (Set α)}
    {d d' : ℕ} (hdd' : d ≤ d')
    (hG : UniformlyContrastivelyGeneratesAt G 𝓗 d) :
    UniformlyContrastivelyGeneratesAt G 𝓗 d' := by
  intro h hh t history hcross hcard
  exact hG h hh t history hcross (hdd'.trans hcard)

/-- The closure-based generator in the sufficiency proof of Theorem 5.4. -/
noncomputable def closureDimensionGenerator
    [Nonempty α] (𝓗 : Set (Set α)) :
    ContrastiveGenerator α := by
  classical
  exact fun _t history =>
    let E := distinctUnorderedEdges history
    if hex :
        ∃ x, x ∈ unorderedClosure 𝓗 E ∧
          x ∉ unorderedVertices E then
      Classical.choose hex
    else
      Classical.choice inferInstance

theorem closureDimensionGenerator_spec
    [Nonempty α] {𝓗 : Set (Set α)}
    {t : ℕ} {history : Fin t → Edge α}
    (hex :
      ∃ x,
        x ∈ unorderedClosure 𝓗 (distinctUnorderedEdges history) ∧
        x ∉ unorderedVertices (distinctUnorderedEdges history)) :
    closureDimensionGenerator 𝓗 t history ∈
        unorderedClosure 𝓗 (distinctUnorderedEdges history) ∧
      closureDimensionGenerator 𝓗 t history ∉
        unorderedVertices (distinctUnorderedEdges history) := by
  simpa [closureDimensionGenerator, hex] using
    Classical.choose_spec hex

theorem finite_history_target_in_version
    {𝓗 : Set (Set α)} {h : Set α} (hh : h ∈ 𝓗)
    {t : ℕ} {history : Fin t → Edge α}
    (hcross : ∀ i, Crosses h (history i)) :
    h ∈ unorderedVersionSpace 𝓗
      (distinctUnorderedEdges history) := by
  classical
  constructor
  · exact hh
  · intro p hp
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hp
    exact
      (unorderedCrosses_edge_iff h (history i)).2
        (hcross i)

theorem fresh_closure_point_of_dimension_bound
    {𝓗 : Set (Set α)} {d t : ℕ}
    {history : Fin t → Edge α}
    (hbound : ContrastiveClosureDimensionAtMost 𝓗 d)
    (hnonempty :
      (unorderedVersionSpace 𝓗
        (distinctUnorderedEdges history)).Nonempty)
    (hcard : d + 1 ≤ (distinctUnorderedEdges history).card) :
    ∃ x,
      x ∈ unorderedClosure 𝓗
          (distinctUnorderedEdges history) ∧
        x ∉ unorderedVertices
          (distinctUnorderedEdges history) := by
  by_contra h
  push_neg at h
  have hsubset :
      unorderedClosure 𝓗 (distinctUnorderedEdges history) ⊆
        unorderedVertices (distinctUnorderedEdges history) := by
    intro x hx
    exact h x hx
  have hle :=
    hbound (distinctUnorderedEdges history)
      ⟨hnonempty, hsubset⟩
  omega

theorem dimensionBound_suffices
    [Nonempty α] {𝓗 : Set (Set α)} {d : ℕ}
    (hbound : ContrastiveClosureDimensionAtMost 𝓗 d) :
    UniformlyContrastivelyGeneratesAt
      (closureDimensionGenerator 𝓗) 𝓗 (d + 1) := by
  intro h hh t history hcross hcard
  have hhVersion :=
    finite_history_target_in_version hh hcross
  have hnonempty :
      (unorderedVersionSpace 𝓗
        (distinctUnorderedEdges history)).Nonempty :=
    ⟨h, hhVersion⟩
  have hfresh :=
    fresh_closure_point_of_dimension_bound
      hbound hnonempty hcard
  have hspec :=
    closureDimensionGenerator_spec hfresh
  constructor
  · exact unorderedClosure_subset_version hhVersion hspec.1
  · rw [seenPrefix_eq_unorderedVertices]
    exact hspec.2

theorem enumerate_unordered_edges_exactly
    (E : Finset (UnorderedEdge α)) :
    distinctUnorderedEdges
        (fun i : Fin E.card =>
          ((E.equivFin.symm i).1).orient) = E := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨i, _hi, hpi⟩ := Finset.mem_image.mp hp
    have horient :=
      ((E.equivFin.symm i).1).orient_unordered
    have hpq :
        p = (E.equivFin.symm i).1 :=
      hpi.symm.trans horient
    rw [hpq]
    exact (E.equivFin.symm i).2
  · intro hp
    let q : E := ⟨p, hp⟩
    let i : Fin E.card := E.equivFin q
    refine Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, ?_⟩
    change ((E.equivFin.symm i).1).orient.unordered = p
    rw [UnorderedEdge.orient_unordered]
    change (E.equivFin.symm (E.equivFin q)).1 = p
    simp [q]

theorem orientation_history_crosses
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    {h : Set α} (hh : h ∈ unorderedVersionSpace 𝓗 E) :
    ∀ i : Fin E.card,
      Crosses h ((E.equivFin.symm i).1).orient := by
  intro i
  rw [unorderedCrosses_orient_iff]
  exact hh.2 _ (E.equivFin.symm i).2

theorem hollow_obstructs_generator
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    (hollow : IsContrastivelyHollow 𝓗 E)
    {G : ContrastiveGenerator α} {d : ℕ}
    (hcard : d ≤ E.card) :
    ¬UniformlyContrastivelyGeneratesAt G 𝓗 d := by
  classical
  intro hG
  let history : Fin E.card → Edge α :=
    fun i => ((E.equivFin.symm i).1).orient
  have hhistory :
      distinctUnorderedEdges history = E := by
    simpa [history] using enumerate_unordered_edges_exactly E
  let x := G E.card history
  by_cases hxV : x ∈ unorderedVertices E
  · obtain ⟨h, hh⟩ := hollow.1
    have hcorrect :=
      hG h hh.1 E.card history
        (by
          intro i
          exact orientation_history_crosses hh i)
        (by simpa [hhistory] using hcard)
    have hxSeen : x ∈ seenPrefix history := by
      rw [seenPrefix_eq_unorderedVertices, hhistory]
      exact hxV
    exact hcorrect.2 hxSeen
  · have hxClosure : x ∉ unorderedClosure 𝓗 E := by
      intro hx
      exact hxV (hollow.2 hx)
    have hversionNonempty :
        (unorderedVersionSpace 𝓗 E).Nonempty :=
      hollow.1
    have hex :
        ∃ h, h ∈ unorderedVersionSpace 𝓗 E ∧ x ∉ h := by
      have hex' :
          ∃ h, ∃ _hh : h ∈ unorderedVersionSpace 𝓗 E,
            x ∉ h := by
        simpa only [unorderedClosure, if_pos hversionNonempty,
          Set.mem_setOf_eq, not_forall] using hxClosure
      obtain ⟨h, hh, hxh⟩ := hex'
      exact ⟨h, hh, hxh⟩
    obtain ⟨h, hh, hxh⟩ := hex
    have hcorrect :=
      hG h hh.1 E.card history
        (by
          intro i
          exact orientation_history_crosses hh i)
        (by simpa [hhistory] using hcard)
    exact hxh hcorrect.1

theorem generator_implies_dimension_bound
    {𝓗 : Set (Set α)} {d : ℕ}
    {G : ContrastiveGenerator α}
    (hG : UniformlyContrastivelyGeneratesAt G 𝓗 (d + 1)) :
    ContrastiveClosureDimensionAtMost 𝓗 d := by
  intro E hollow
  by_contra hnot
  have hcard : d + 1 ≤ E.card :=
    Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnot)
  exact (hollow_obstructs_generator hollow hcard) hG

/-- Theorem 5.4, exact quantitative finite-bound form: a uniform generator
works after `d+1` distinct unordered edges exactly when every hollow edge set
has cardinality at most `d`. -/
theorem theorem_5_4_quantitative
    [Nonempty α] (𝓗 : Set (Set α)) (d : ℕ) :
    UniformlyContrastivelyGeneratableAt 𝓗 (d + 1) ↔
      ContrastiveClosureDimensionAtMost 𝓗 d := by
  constructor
  · rintro ⟨G, hG⟩
    exact generator_implies_dimension_bound hG
  · intro hbound
    exact ⟨closureDimensionGenerator 𝓗,
      dimensionBound_suffices hbound⟩

/-- Theorem 5.4, qualitative form: uniform contrastive generation is
equivalent to finiteness of the contrastive closure dimension. -/
theorem theorem_5_4
    [Nonempty α] (𝓗 : Set (Set α)) :
    UniformlyContrastivelyGeneratable 𝓗 ↔
      FiniteContrastiveClosureDimension 𝓗 := by
  constructor
  · rintro ⟨d, G, hG⟩
    have hG' :
        UniformlyContrastivelyGeneratesAt G 𝓗 (d + 1) :=
      uniformThreshold_mono (G := G) (Nat.le_succ d) hG
    exact ⟨d, generator_implies_dimension_bound hG'⟩
  · rintro ⟨d, hbound⟩
    exact ⟨d + 1, closureDimensionGenerator 𝓗,
      dimensionBound_suffices hbound⟩

/-- Theorem 5.4's sharp sample-complexity statement.  If the finite closure
dimension has exact value `d`, then `d+1` is the least positive
distinct-edge threshold for a uniform contrastive generator. -/
theorem theorem_5_4_sharp_sample_complexity
    [Nonempty α] {𝓗 : Set (Set α)} {d : ℕ}
    (hdim : ContrastiveClosureDimensionEquals 𝓗 d) :
    IsLeastPositiveUniformThreshold 𝓗 (d + 1) := by
  constructor
  · omega
  constructor
  · exact
      (theorem_5_4_quantitative 𝓗 d).2 hdim.1
  · intro k hk hgen
    obtain ⟨b, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hbound :
        ContrastiveClosureDimensionAtMost 𝓗 b :=
      (theorem_5_4_quantitative 𝓗 b).1 hgen
    exact Nat.add_le_add_right (hdim.2 b hbound) 1

/-- The lower-bound half of the source's sharpness claim.  Any hollow set
of `d` distinct unordered edges rules out sample complexity `d`. -/
theorem hollow_cardinality_lower_bound
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    (hollow : IsContrastivelyHollow 𝓗 E) :
    ¬UniformlyContrastivelyGeneratableAt 𝓗 E.card := by
  rintro ⟨G, hG⟩
  exact (hollow_obstructs_generator hollow le_rfl) hG

end ContrastiveGeneration
end GenLimit
