import GenLimit.Paper00_LanguageIdentification.Text.Consistency
import GenLimit.Core.TargetStability
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

/-!
# Identification by enumeration from positive text

For an indexed family `C`, positive evidence can establish only that the
presented target is contained in a conjectured language.  Accordingly, the
canonical limit of the least-compatible enumeration learner is the least
index whose language contains the target, rather than necessarily an index
for the target itself.

The learner searches only the finite index scope determined by the length of
the ordered history.  Its fallback makes it total before that scope contains
any compatible candidate.  The definition is semantic and noncomputable:
membership in an arbitrary `Language = Set ℕ` is not supplied with a decision
procedure.
-/

namespace GenLimit
namespace Gold
namespace Text

/-- The least index whose language contains `C z`.  Such an index always
exists, since `z` itself is one. -/
noncomputable def leastCover (C : LanguageFamily) (z : ℕ) : ℕ :=
  by
    classical
    exact Nat.find
      (show ∃ i, C z ⊆ C i from ⟨z, Set.Subset.rfl⟩)

theorem leastCover_spec (C : LanguageFamily) (z : ℕ) :
    C z ⊆ C (leastCover C z) := by
  classical
  exact Nat.find_spec (show ∃ i, C z ⊆ C i from ⟨z, Set.Subset.rfl⟩)

theorem leastCover_minimal
    (C : LanguageFamily) (z i : ℕ) (hi : C z ⊆ C i) :
    leastCover C z ≤ i := by
  classical
  exact Nat.find_min' (show ∃ j, C z ⊆ C j from ⟨z, Set.Subset.rfl⟩) hi

theorem leastCover_le (C : LanguageFamily) (z : ℕ) :
    leastCover C z ≤ z := by
  exact leastCover_minimal C z z Set.Subset.rfl

theorem not_target_subset_of_lt_leastCover
    (C : LanguageFamily) (z i : ℕ) (hi : i < leastCover C z) :
    ¬ C z ⊆ C i := by
  intro hsub
  exact (Nat.not_le_of_lt hi) (leastCover_minimal C z i hsub)

/-- Indices in the currently visible finite scope whose languages contain
every positive datum in the ordered history. -/
noncomputable def compatibleIndices
    (C : LanguageFamily) (history : List ℕ) : Finset ℕ := by
  classical
  exact (Finset.range history.length).filter
    (fun i => PositiveCompatible history (C i))

@[simp] theorem mem_compatibleIndices
    {C : LanguageFamily} {history : List ℕ} {i : ℕ} :
    i ∈ compatibleIndices C history ↔
      i < history.length ∧ PositiveCompatible history (C i) := by
  classical
  simp [compatibleIndices]

/-- The least positive-compatible index below the history length.  The
fallback is returned only when this finite candidate set is empty. -/
noncomputable def enumerationLearnerWithFallback
    (C : LanguageFamily) (fallback : ℕ) : TextLearner ℕ := by
  classical
  intro history
  let candidates := compatibleIndices C history
  exact if h : candidates.Nonempty then candidates.min' h else fallback

/-- The canonical totalized enumeration learner, using index `0` as its
irrelevant early-stage fallback. -/
noncomputable def enumerationLearner
    (C : LanguageFamily) : TextLearner ℕ :=
  enumerationLearnerWithFallback C 0

theorem enumerationLearnerWithFallback_eq_min'
    {C : LanguageFamily} {fallback : ℕ} {history : List ℕ}
    (hne : (compatibleIndices C history).Nonempty) :
    enumerationLearnerWithFallback C fallback history =
      (compatibleIndices C history).min' hne := by
  classical
  simp only [enumerationLearnerWithFallback]
  rw [dif_pos hne]

theorem enumerationLearnerWithFallback_mem
    {C : LanguageFamily} {fallback : ℕ} {history : List ℕ}
    (hne : (compatibleIndices C history).Nonempty) :
    enumerationLearnerWithFallback C fallback history ∈
      compatibleIndices C history := by
  rw [enumerationLearnerWithFallback_eq_min' hne]
  exact Finset.min'_mem _ _

theorem enumerationLearnerWithFallback_le
    {C : LanguageFamily} {fallback : ℕ} {history : List ℕ} {i : ℕ}
    (hi : i ∈ compatibleIndices C history) :
    enumerationLearnerWithFallback C fallback history ≤ i := by
  have hne : (compatibleIndices C history).Nonempty := ⟨i, hi⟩
  rw [enumerationLearnerWithFallback_eq_min' hne]
  exact Finset.min'_le _ _ hi

/-- On every exact presentation, the bounded least-compatible learner
eventually stabilizes to the least indexed language containing the target. -/
theorem enumerationLearnerWithFallback_stabilizesTo_leastCover
    {C : LanguageFamily} {stream : ℕ → ℕ} {z fallback : ℕ}
    (hP : Presents stream (C z)) :
    StabilizesTo
      (fun t =>
        enumerationLearnerWithFallback C fallback (textPrefix stream t))
      (leastCover C z) := by
  classical
  let k := leastCover C z
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_target_subset hP (k + 1)
  refine ⟨max T (k + 1), ?_⟩
  intro t ht
  have hTt : T ≤ t := le_trans (Nat.le_max_left T (k + 1)) ht
  have hkt : k < t := lt_of_lt_of_le (Nat.lt_succ_self k)
    (le_trans (Nat.le_max_right T (k + 1)) ht)
  have hkcon : Consistent C stream t k :=
    consistent_of_target_subset hP (leastCover_spec C z)
  have hkcompat :
      PositiveCompatible (textPrefix stream t) (C k) :=
    (positiveCompatible_textPrefix_iff_consistent C stream t k).2 hkcon
  have hkmem :
      k ∈ compatibleIndices C (textPrefix stream t) := by
    rw [mem_compatibleIndices]
    exact ⟨by simpa using hkt, hkcompat⟩
  have hne :
      (compatibleIndices C (textPrefix stream t)).Nonempty :=
    ⟨k, hkmem⟩
  let n :=
    enumerationLearnerWithFallback C fallback (textPrefix stream t)
  have hnmem :
      n ∈ compatibleIndices C (textPrefix stream t) := by
    exact enumerationLearnerWithFallback_mem hne
  have hnk : n ≤ k := by
    exact enumerationLearnerWithFallback_le hkmem
  have hncon : Consistent C stream t n := by
    have hncompat :
        PositiveCompatible (textPrefix stream t) (C n) :=
      (mem_compatibleIndices.mp hnmem).2
    exact
      (positiveCompatible_textPrefix_iff_consistent C stream t n).1
        hncompat
  have hnsub : C z ⊆ C n := by
    exact (hT t hTt n (Nat.lt_succ_of_le hnk)).1 hncon
  have hkn : k ≤ n := by
    exact leastCover_minimal C z n hnsub
  exact Nat.le_antisymm hnk hkn

theorem enumerationLearner_stabilizesTo_leastCover
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    StabilizesTo
      (fun t => enumerationLearner C (textPrefix stream t))
      (leastCover C z) := by
  exact enumerationLearnerWithFallback_stabilizesTo_leastCover
    (fallback := 0) hP

/-- If the least containing candidate denotes the target itself, enumeration
identifies that target on the given text. -/
theorem enumerationLearner_identifiesOnText
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hcover : C (leastCover C z) = C z) :
    IdentifiesOnText (familyNaming C) (enumerationLearner C)
      stream (C z) := by
  exact ⟨leastCover C z, hcover,
    enumerationLearner_stabilizesTo_leastCover hP⟩

/-- An indexed family is inclusion-antichain-like when containment between
two indexed languages forces extensional equality.  Repeated languages remain
allowed. -/
def IsInclusionAntichain (C : LanguageFamily) : Prop :=
  ∀ i j, C i ⊆ C j → C i = C j

theorem leastCover_language_eq_of_isInclusionAntichain
    {C : LanguageFamily} (hC : IsInclusionAntichain C) (z : ℕ) :
    C (leastCover C z) = C z := by
  exact (hC z (leastCover C z) (leastCover_spec C z)).symm

/-- Least-compatible enumeration identifies every language in an inclusion
antichain family, despite possible repeated indices. -/
theorem enumerationLearner_identifiesFamily_of_isInclusionAntichain
    {C : LanguageFamily} (hC : IsInclusionAntichain C) :
    IdentifiesFamily C (enumerationLearner C) := by
  intro z stream hP
  exact enumerationLearner_identifiesOnText hP
    (leastCover_language_eq_of_isInclusionAntichain hC z)

end Text
end Gold
end GenLimit
