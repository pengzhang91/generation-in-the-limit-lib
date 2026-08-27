import GenLimit.Paper15_PartialEnumeration.FullTextIdentification
import GenLimit.Paper15_PartialEnumeration.SeparationHierarchy

/-!
# Causal separation in the full-enumeration model

Paper 15 describes a learner as "knowing" that one of two candidates is not
the target.  In a positive-text model, the honest finite witness for this
knowledge is an observed datum outside that candidate.  The definitions below
make that evidence explicit and depend only on the current finite history.

The equivalence with `T₁` is stated for exact full texts.  This qualification
is essential: an arbitrary partial text can permanently omit the finite
witness separating two incomparable languages.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration
namespace FullTopology

/-- A finite positive history refutes `L` when it already contains a datum
outside `L`.  This is a causal, check-at-the-current-history notion. -/
def RefutedByHistory (history : List ℕ) (L : Language) : Prop :=
  ∃ x, x ∈ history ∧ x ∉ L

theorem refutedByHistory_mono
    {history extension : List ℕ} {L : Language}
    (h : RefutedByHistory history L) :
    RefutedByHistory (history ++ extension) L := by
  obtain ⟨x, hxHistory, hxL⟩ := h
  exact ⟨x, List.mem_append_left _ hxHistory, hxL⟩

/-- Every exact full text of `K` eventually supplies finite positive evidence
refuting `L`. -/
def SeparatesFromFullText
    {X : Set Language} (K L : Point X) : Prop :=
  ∀ stream : ℕ → ℕ, Presents stream K.1 →
    ∃ T, ∀ t, T ≤ t →
      RefutedByHistory (textPrefix stream t) L.1

/-- On a presentable target, causal separation from every exact full text is
equivalent to failure of language containment. -/
theorem separatesFromFullText_iff_not_subset
    {X : Set Language} {K L : Point X}
    (hK : K.1.Nonempty) :
    SeparatesFromFullText K L ↔ ¬ K.1 ⊆ L.1 := by
  constructor
  · intro hSeparates hKL
    obtain ⟨stream, hP⟩ :=
      Angluin.exists_presentation_of_nonempty hK
    obtain ⟨T, hT⟩ := hSeparates stream hP
    obtain ⟨x, hxPrefix, hxL⟩ := hT T le_rfl
    rw [mem_textPrefix_iff] at hxPrefix
    obtain ⟨s, _hsT, hsx⟩ := hxPrefix
    apply hxL
    apply hKL
    rw [← hP]
    exact ⟨s, hsx⟩
  · intro hNotSubset stream hP
    obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp hNotSubset
    rw [← hP] at hxK
    obtain ⟨s, hsx⟩ := hxK
    refine ⟨s + 1, ?_⟩
    intro t ht
    refine ⟨x, ?_, hxL⟩
    rw [mem_textPrefix_iff]
    exact ⟨s, lt_of_lt_of_le (Nat.lt_succ_self s) ht, hsx⟩

/-- The paper's standing presentability hypothesis, weakened from "every
language is infinite" to the exact condition needed here. -/
def AllNonempty (X : Set Language) : Prop :=
  ∀ K : Point X, K.1.Nonempty

/-- Pairwise separation in the limit using only finite positive evidence from
exact full texts.  Quantifying over ordered pairs supplies both directions of
separation. -/
def SeparatedInLimit (X : Set Language) : Prop :=
  ∀ K L : Point X, K ≠ L → SeparatesFromFullText K L

/-- Full-text separation is exactly the inclusion-antichain property. -/
theorem separatedInLimit_iff_inclusionAntichain
    {X : Set Language} (hNonempty : AllNonempty X) :
    SeparatedInLimit X ↔ InclusionAntichain X := by
  constructor
  · intro hSeparated K L hKL
    by_contra hNe
    have hNotSubset : ¬ K.1 ⊆ L.1 :=
      (separatesFromFullText_iff_not_subset (hNonempty K)).mp
        (hSeparated K L hNe)
    exact hNotSubset hKL
  · intro hAntichain K L hNe
    apply
      (separatesFromFullText_iff_not_subset (hNonempty K)).mpr
    intro hKL
    exact hNe (hAntichain K L hKL)

/-- Paper 15, Corollary 4.10, for the well-posed exact-full-text reading of
separation in the limit. -/
theorem corollary_4_10_fullText
    {X : Set Language} (hNonempty : AllNonempty X) :
    SeparatedInLimit X ↔ TOneSpace X := by
  exact (separatedInLimit_iff_inclusionAntichain hNonempty).trans
    (tOneSpace_iff_inclusionAntichain X).symm

/-- Paper 15, Corollary 4.11: full-text separation is possible exactly when
no two distinct class languages are comparable by inclusion. -/
theorem corollary_4_11_fullText
    {X : Set Language} (hNonempty : AllNonempty X) :
    SeparatedInLimit X ↔
      ∀ K L : Point X, K.1 ⊆ L.1 → K = L :=
  separatedInLimit_iff_inclusionAntichain hNonempty

/-- The source's observation that separation in the limit implies
identification in the limit, now as a theorem about an actual causal text
learner. -/
theorem separatedInLimit_implies_identifiableOnFullTexts
    {X : Set Language}
    (hCountable : X.Countable)
    (hLanguagesNonempty : AllNonempty X)
    (hSeparated : SeparatedInLimit X) :
    IdentifiableOnFullTexts X := by
  apply (theorem_4_9_fullText X (fun L hLX => hLanguagesNonempty ⟨L, hLX⟩)).mpr
  refine ⟨hCountable, ?_⟩
  apply tOneSpace_implies_tdSpace
  exact (corollary_4_10_fullText hLanguagesNonempty).mp hSeparated

end FullTopology
end PartialEnumeration
end KleinbergWei
end GenLimit
