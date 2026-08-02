import GenLimit.ContrastiveGeneration.Hierarchy

/-!
# Disjoint-support hierarchy witness

This file formalizes the disjoint-support witness used in Theorems 5.13 and
5.14 of Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*
(arXiv:2605.06211v1).

The even and odd natural numbers are individually identifiable from the first
positive text example.  The edge stream `{2n,2n+1}` is simultaneously a valid
contrastive presentation for both, while their intersection is empty.
Proposition 5.12 therefore rules out contrastive generation.
-/

namespace GenLimit
namespace ContrastiveGeneration

/-- The even support. -/
def evenSupport : Set ℕ := Set.range (fun n => 2 * n)

/-- The odd support. -/
def oddSupport : Set ℕ := Set.range (fun n => 2 * n + 1)

theorem evenSupport_infinite : evenSupport.Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  change 2 * m = 2 * n at h
  omega

theorem oddSupport_infinite : oddSupport.Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  change 2 * m + 1 = 2 * n + 1 at h
  omega

theorem evenSupport_disjoint_oddSupport :
    Disjoint evenSupport oddSupport := by
  rw [Set.disjoint_left]
  intro x hxEven hxOdd
  obtain ⟨m, rfl⟩ := hxEven
  obtain ⟨n, hn⟩ := hxOdd
  change 2 * n + 1 = 2 * m at hn
  omega

/-- Two distinct indexed supports, with harmless repetitions of the odd
support after index one. -/
def disjointFamily : Generic.LanguageFamily ℕ
  | 0 => evenSupport
  | _ + 1 => oddSupport

theorem disjointFamily_infinite (i : ℕ) :
    (disjointFamily i).Infinite := by
  cases i with
  | zero => exact evenSupport_infinite
  | succ _ => exact oddSupport_infinite

/-- The common contrastive stream pairing the `n`-th even and odd points. -/
def disjointPairStream (n : ℕ) : Edge ℕ :=
  ⟨2 * n, 2 * n + 1, by omega⟩

theorem disjointPairStream_crosses_even (n : ℕ) :
    Crosses evenSupport (disjointPairStream n) := by
  left
  constructor
  · exact ⟨n, rfl⟩
  · intro h
    obtain ⟨m, hm⟩ := h
    change 2 * m = 2 * n + 1 at hm
    omega

theorem disjointPairStream_crosses_odd (n : ℕ) :
    Crosses oddSupport (disjointPairStream n) := by
  right
  constructor
  · exact ⟨n, rfl⟩
  · intro h
    obtain ⟨m, hm⟩ := h
    change 2 * m + 1 = 2 * n at hm
    omega

theorem disjointPairStream_presents_even :
    IsContrastivePresentation disjointPairStream evenSupport := by
  constructor
  · exact disjointPairStream_crosses_even
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n, Or.inl rfl⟩

theorem disjointPairStream_presents_odd :
    IsContrastivePresentation disjointPairStream oddSupport := by
  constructor
  · exact disjointPairStream_crosses_odd
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n, Or.inr rfl⟩

/-- A first-example text identifier for the disjoint family. -/
noncomputable def disjointTextIdentifier :
    GenLimit.Angluin.SemanticIdentifier ℕ := by
  classical
  exact fun t history =>
    if ht : t = 0 then 0
    else if history ⟨0, Nat.pos_of_ne_zero ht⟩ ∈ evenSupport then 0
    else 1

theorem disjointTextIdentifier_identifies :
    GenLimit.Angluin.SemanticallyIdentifies
      disjointTextIdentifier disjointFamily := by
  intro z stream hP
  have hfirst : stream 0 ∈ disjointFamily z := by
    rw [← hP]
    exact ⟨0, rfl⟩
  cases z with
  | zero =>
      refine ⟨0, rfl, 1, ?_⟩
      intro t ht
      have ht0 : t ≠ 0 := by omega
      simp only [GenLimit.Angluin.identifierOutput,
        disjointTextIdentifier, dif_neg ht0]
      rw [if_pos]
      simpa [disjointFamily] using hfirst
  | succ z =>
      refine ⟨1, rfl, 1, ?_⟩
      intro t ht
      have ht0 : t ≠ 0 := by omega
      simp only [GenLimit.Angluin.identifierOutput,
        disjointTextIdentifier, dif_neg ht0]
      rw [if_neg]
      intro heven
      exact Set.disjoint_left.mp evenSupport_disjoint_oddSupport
        heven (by simpa [disjointFamily] using hfirst)

theorem disjoint_textIdentifiable :
    TextIdentifiable disjointFamily :=
  ⟨disjointTextIdentifier, disjointTextIdentifier_identifies⟩

theorem disjoint_not_contrastivelyGeneratable :
    ¬ContrastivelyGeneratable (Set.range disjointFamily) := by
  classical
  let family : Finset (Set ℕ) := {evenSupport, oddSupport}
  let core : Finset ℕ := ∅
  apply proposition_5_12
      (𝓗 := Set.range disjointFamily)
      (family := family) (core := core)
      (stream := disjointPairStream)
  · simp [family]
  · intro h hh
    simp only [family, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · intro h hh
    simp only [family, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact disjointPairStream_presents_even
    · exact disjointPairStream_presents_odd
  · intro x
    constructor
    · simp [core]
    · intro hboth
      have heven : x ∈ evenSupport :=
        hboth evenSupport (by simp [family])
      have hodd : x ∈ oddSupport :=
        hboth oddSupport (by simp [family])
      exact
        False.elim
          (Set.disjoint_left.mp evenSupport_disjoint_oddSupport
            heven hodd)

/-- The other half of Theorem 5.14, together with the strict
`CtrGen ⊂ TxtGen` witness used in Theorem 5.13. -/
theorem theorem_5_13_5_14_disjoint_witness :
    TextIdentifiable disjointFamily ∧
      GenLimit.Generic.GeneratableInLimit
        (Set.range disjointFamily) ∧
      ¬ContrastivelyGeneratable (Set.range disjointFamily) := by
  refine ⟨disjoint_textIdentifiable, ?_,
    disjoint_not_contrastivelyGeneratable⟩
  exact textIdentification_implies_generation
    disjointFamily disjointFamily_infinite
    disjoint_textIdentifiable

end ContrastiveGeneration
end GenLimit
