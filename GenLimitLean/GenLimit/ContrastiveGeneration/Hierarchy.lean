import GenLimit.ContrastiveGeneration.IdentifierCharacterization
import GenLimit.ContrastiveGeneration.NonuniformClosure
import GenLimit.Core.IdentificationGeneration
import Mathlib.Data.Set.Finite.Basic

/-!
# The clean contrastive hierarchy

This file formalizes the deterministic semantic content of Proposition 5.12
and Theorems 5.13--5.14 of Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*
(arXiv:2605.06211v1).

The paper states the hierarchy at the level of collections of countable UUS
classes.  We expose its mathematical content as:

* the general inclusions from contrastive identification to contrastive
  generation and to text identification;
* the finite-family common-presentation obstruction;
* a disjoint-support class in text identification but not contrastive
  generation; and
* the punctured-support class in contrastive generation but not text
  identification.

The text-identification negative result uses a semantic version of Angluin's
locking-sequence necessity argument.  It does not introduce an effectivity
claim.
-/

namespace GenLimit
namespace ContrastiveGeneration

open GenLimit.Generic

/-! ## Identification implies generation -/

/-- Select a point in the language currently named by a contrastive
identifier, outside the observed vertices. -/
noncomputable def freshFromContrastiveGuess
    (F : Generic.LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (I : ContrastiveIdentifier α) : ContrastiveGenerator α := by
  classical
  exact fun t history =>
    Classical.choose
      ((hInfinite (I t history)).exists_notMem_finite
        (seenPrefix_finite history))

theorem freshFromContrastiveGuess_spec
    (F : Generic.LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (I : ContrastiveIdentifier α) {t : ℕ}
    (history : Fin t → Edge α) :
    freshFromContrastiveGuess F hInfinite I t history ∈
        F (I t history) ∧
      freshFromContrastiveGuess F hInfinite I t history ∉
        seenPrefix history := by
  exact
    Classical.choose_spec
      ((hInfinite (I t history)).exists_notMem_finite
        (seenPrefix_finite history))

/-- The first inclusion used in Theorem 5.13:
contrastive identification of a UUS indexed family implies contrastive
generation of its range. -/
theorem contrastiveIdentification_implies_generation
    (F : Generic.LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite) :
    ContrastivelyIdentifiable F →
      ContrastivelyGeneratable (Set.range F) := by
  rintro ⟨I, hI⟩
  refine ⟨freshFromContrastiveGuess F hInfinite I, ?_⟩
  intro h hh stream hstream
  obtain ⟨z, rfl⟩ := hh
  obtain ⟨j, hj, T, hT⟩ := hI z stream hstream
  refine ⟨T, ?_⟩
  intro t ht
  have hguess :
      I t (streamPrefix stream t) = j := hT t ht
  have hspec :=
    freshFromContrastiveGuess_spec
      F hInfinite I (streamPrefix stream t)
  constructor
  · rw [hguess, hj] at hspec
    exact hspec.1
  · exact hspec.2

/-! ## Text identification implies text generation -/

/-- Select a fresh point from the language currently named by a text
identifier. -/
noncomputable def freshFromTextGuess
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite)
    (M : GenLimit.Angluin.SemanticIdentifier α) :
    Generic.Generator α :=
  Generic.freshFromIndexGuess F hInfinite M

theorem freshFromTextGuess_spec
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite)
    (M : GenLimit.Angluin.SemanticIdentifier α)
    {t : ℕ} (history : Fin t → α) :
    freshFromTextGuess F hInfinite M t history ∈ F (M t history) ∧
      freshFromTextGuess F hInfinite M t history ∉
        Generic.sequenceSample history := by
  exact Generic.freshFromIndexGuess_spec F hInfinite M history

/-- The second elementary inclusion used in Theorem 5.13:
text identification of a UUS family implies text generation. -/
theorem textIdentification_implies_generation
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    TextIdentifiable F →
      GenLimit.Generic.GeneratableInLimit (Set.range F) := by
  rintro ⟨M, hM⟩
  exact
    Generic.stabilizingIndexIdentifier_implies_generatableInLimit
      F hInfinite M hM

/-! ## A semantic Angluin necessity bridge -/

/-- View a finite-history semantic identifier as a list identifier. -/
def listIdentifierOfSemantic
    (M : GenLimit.Angluin.SemanticIdentifier ℕ) :
    List ℕ → ℕ :=
  GenLimit.Angluin.listIdentifierOf M

theorem listIdentifierOfSemantic_prefix
    (M : GenLimit.Angluin.SemanticIdentifier ℕ)
    (stream : Stream ℕ) (t : ℕ) :
    listIdentifierOfSemantic M
        (GenLimit.Angluin.streamPrefix stream t) =
      GenLimit.Angluin.identifierOutput M stream t := by
  exact GenLimit.Angluin.listIdentifierOf_streamPrefix M stream t

/-- Semantic text identification over `ℕ` implies Angluin's finite
tell-tale condition.  This is the noneffective locking-sequence argument;
it makes no recursive-enumerability assertion. -/
theorem semanticIdentification_implies_conditionTwo
    (F : Generic.LanguageFamily ℕ)
    (_hNonempty : GenLimit.Angluin.AllNonempty F)
    (hIdentifiable :
      ∃ M : GenLimit.Angluin.SemanticIdentifier ℕ,
        GenLimit.Angluin.SemanticallyIdentifies M F) :
    GenLimit.Angluin.ConditionTwo F := by
  exact GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable F hIdentifiable

/-! ## Proposition 5.12: finite-family obstruction -/

/-- A single contrastive stream is valid for every support in a finite
family. -/
def IsSharedPresentation
    (stream : ℕ → Edge α) (family : Finset (Set α)) : Prop :=
  ∀ h, h ∈ family → IsContrastivePresentation stream h

/-- `core` is exactly the intersection of the finite family. -/
def IsFiniteFamilyIntersection
    (family : Finset (Set α)) (core : Finset α) : Prop :=
  ∀ x, x ∈ core ↔ ∀ h, h ∈ family → x ∈ h

/-- Proposition 5.12 in a finite-core form.  The explicit finset `core`
avoids encoding the cardinality of an arbitrary set intersection: its
specification says exactly that it is the family intersection. -/
theorem proposition_5_12
    {𝓗 : Set (Set α)} {family : Finset (Set α)}
    {core : Finset α} {stream : ℕ → Edge α}
    (hfamilyNonempty : family.Nonempty)
    (hfamilyClass : ∀ h, h ∈ family → h ∈ 𝓗)
    (hshared : IsSharedPresentation stream family)
    (hcore : IsFiniteFamilyIntersection family core) :
    ¬ContrastivelyGeneratable 𝓗 := by
  classical
  rintro ⟨G, hG⟩
  choose threshold hthreshold using
    fun h : {h // h ∈ family} =>
      hG h.1 (hfamilyClass h.1 h.2) stream
        (hshared h.1 h.2)
  let allThresholds : Finset ℕ :=
    family.attach.image threshold
  let Tgen : ℕ :=
    if hne : allThresholds.Nonempty then
      allThresholds.max' hne
    else 0
  have hTgen :
      ∀ h, h ∈ family → ∀ t, Tgen ≤ t →
        generatorOutput G stream t ∈ h ∧
          generatorOutput G stream t ∉
            seenPrefix (streamPrefix stream t) := by
    intro h hh t ht
    let hs : {g // g ∈ family} := ⟨h, hh⟩
    have hmem : threshold hs ∈ allThresholds := by
      exact Finset.mem_image.mpr ⟨hs, Finset.mem_attach _ _, rfl⟩
    have hne : allThresholds.Nonempty := ⟨threshold hs, hmem⟩
    have hle : threshold hs ≤ Tgen := by
      simp only [Tgen, dif_pos hne]
      exact Finset.le_max' _ _ hmem
    exact hthreshold hs t (hle.trans ht)
  obtain ⟨h₀, hh₀⟩ := hfamilyNonempty
  have hcoreSubset : (↑core : Set α) ⊆ h₀ := by
    intro x hx
    exact (hcore x).mp hx h₀ hh₀
  obtain ⟨Tseen, hTseen⟩ :=
    finite_vertices_eventually_seen
      (hshared h₀ hh₀) core hcoreSubset
  let t := max Tgen Tseen
  let out := generatorOutput G stream t
  have houtFamily :
      ∀ h, h ∈ family → out ∈ h := by
    intro h hh
    exact
      (hTgen h hh t (Nat.le_max_left _ _)).1
  have houtCore : out ∈ core :=
    (hcore out).mpr houtFamily
  have houtSeen :
      out ∈ seenPrefix (streamPrefix stream t) :=
    hTseen t (Nat.le_max_right _ _) houtCore
  exact
    (hTgen h₀ hh₀ t (Nat.le_max_left _ _)).2 houtSeen

/-! ## The punctured-support witness -/

/-- The even spine used by the punctured-support hierarchy witness. -/
def puncturedCore (m : ℕ) : ℕ := 2 * m

theorem puncturedCore_injective : Function.Injective puncturedCore := by
  intro m n h
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

/-- `h∞` is the even spine; `h(m+1)` removes its `m`-th point. -/
def puncturedFamily : Generic.LanguageFamily ℕ
  | 0 => Set.range puncturedCore
  | m + 1 => Set.range puncturedCore \ {puncturedCore m}

theorem puncturedFamily_nonempty :
    GenLimit.Angluin.AllNonempty puncturedFamily := by
  intro i
  cases i with
  | zero =>
      exact ⟨puncturedCore 0, ⟨0, rfl⟩⟩
  | succ m =>
      refine ⟨puncturedCore (m + 1), ?_⟩
      constructor
      · exact ⟨m + 1, rfl⟩
      · simp only [Set.mem_singleton_iff]
        intro h
        have hmn := puncturedCore_injective h
        omega

theorem puncturedCore_eventual :
    IsEventualCore (Set.range puncturedFamily) puncturedCore := by
  constructor
  · exact puncturedCore_injective
  · intro h hh
    obtain ⟨i, rfl⟩ := hh
    cases i with
    | zero =>
        simp [puncturedFamily]
    | succ m =>
        have heq :
            {n : ℕ | puncturedCore n ∉ puncturedFamily (m + 1)} =
              {m} := by
          ext n
          simp only [puncturedFamily, Set.mem_diff,
            Set.mem_range, Set.mem_singleton_iff, Set.mem_setOf_eq]
          constructor
          · intro hn
            have hne : puncturedCore n = puncturedCore m := by
              by_contra hne
              exact hn ⟨⟨n, rfl⟩, hne⟩
            exact puncturedCore_injective hne
          · rintro rfl ⟨_hrange, hne⟩
            exact hne rfl
        rw [heq]
        exact Set.finite_singleton m

/-- The punctured-support class belongs to contrastive generation by
Proposition 5.11. -/
theorem punctured_contrastivelyGeneratable :
    ContrastivelyGeneratable (Set.range puncturedFamily) :=
  proposition_5_11
    (Set.range puncturedFamily) puncturedCore puncturedCore_eventual

theorem punctured_no_tellTale_at_zero
    (T : Finset ℕ)
    (hT : GenLimit.Angluin.IsTellTale puncturedFamily 0 T) :
    False := by
  classical
  have hcoreInfinite : (Set.range puncturedCore).Infinite :=
    Set.infinite_range_of_injective puncturedCore_injective
  obtain ⟨x, hxrange, hxT⟩ :=
    hcoreInfinite.exists_notMem_finset T
  obtain ⟨m, rfl⟩ := hxrange
  have hTsub :
      (↑T : Set ℕ) ⊆ puncturedFamily (m + 1) := by
    intro y hy
    have hycore : y ∈ Set.range puncturedCore :=
      hT.1 hy
    constructor
    · exact hycore
    · intro hyeq
      subst y
      exact hxT hy
  have hproperSubset :
      puncturedFamily (m + 1) ⊆ puncturedFamily 0 := by
    intro y hy
    exact hy.1
  have hreverse :
      puncturedFamily 0 ⊆ puncturedFamily (m + 1) :=
    hT.2 (m + 1) hTsub hproperSubset
  have hcenter : puncturedCore m ∈ puncturedFamily 0 :=
    ⟨m, rfl⟩
  exact (hreverse hcenter).2 rfl

theorem punctured_not_conditionTwo :
    ¬GenLimit.Angluin.ConditionTwo puncturedFamily := by
  intro h
  obtain ⟨T, hT⟩ := h 0
  exact punctured_no_tellTale_at_zero T hT

/-- One half of Theorem 5.14: the punctured class is contrastively
generatable but not text-identifiable. -/
theorem punctured_not_textIdentifiable :
    ¬TextIdentifiable puncturedFamily := by
  intro hText
  exact punctured_not_conditionTwo
    (semanticIdentification_implies_conditionTwo
      puncturedFamily puncturedFamily_nonempty hText)

/-- A theorem-level witness for
`CtrGen ⊄ TxtId` and for strictness of `CtrId ⊂ CtrGen`. -/
theorem theorem_5_13_5_14_punctured_witness :
    ContrastivelyGeneratable (Set.range puncturedFamily) ∧
      ¬TextIdentifiable puncturedFamily ∧
      ¬ContrastivelyIdentifiable puncturedFamily := by
  refine
    ⟨punctured_contrastivelyGeneratable,
      punctured_not_textIdentifiable, ?_⟩
  intro hCtr
  apply punctured_not_textIdentifiable
  apply (lemma_4_6_inclusion puncturedFamily ?_) hCtr
  intro i
  cases i with
  | zero =>
      constructor
      · exact puncturedFamily_nonempty 0
      · refine ⟨1, ?_⟩
        simp only [puncturedFamily, Set.mem_compl_iff, Set.mem_range,
          puncturedCore]
        omega
  | succ m =>
      constructor
      · exact puncturedFamily_nonempty (m + 1)
      · refine ⟨2 * m + 1, ?_⟩
        simp only [puncturedFamily, Set.mem_compl_iff,
          Set.mem_diff, Set.mem_range, Set.mem_singleton_iff,
          puncturedCore]
        intro h
        obtain ⟨n, hn⟩ := h.1
        omega

end ContrastiveGeneration
end GenLimit
