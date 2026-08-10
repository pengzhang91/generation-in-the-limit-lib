import GenLimit.Paper00_LanguageIdentification.Informant.Model
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

/-!
# Identification by enumeration from informants

For an indexed family, the learner searches the finite index scope visible at
the current time and conjectures its least member compatible with all labels
seen so far.  Completeness of the informant eventually eliminates every
extensionally wrong candidate in any fixed finite scope.  Consequently the
learner stabilizes to the least index denoting the target.

This semantic construction is noncomputable because arbitrary
`Language = Set ℕ` membership is not equipped with a decision procedure.  It
isolates the identification argument from the later question of compiling it
to finite Boolean membership queries.
-/

namespace GenLimit
namespace Gold
namespace Informant

open Gold.Text

/-- The least family index denoting the same language as `C z`.  Repeated
names for one language are allowed. -/
noncomputable def leastEqualName (C : LanguageFamily) (z : ℕ) : ℕ := by
  classical
  exact Nat.find
    (show ∃ i, C i = C z from ⟨z, rfl⟩)

theorem leastEqualName_spec (C : LanguageFamily) (z : ℕ) :
    C (leastEqualName C z) = C z := by
  classical
  exact Nat.find_spec (show ∃ i, C i = C z from ⟨z, rfl⟩)

theorem leastEqualName_minimal
    (C : LanguageFamily) (z i : ℕ) (hi : C i = C z) :
    leastEqualName C z ≤ i := by
  classical
  exact Nat.find_min'
    (show ∃ j, C j = C z from ⟨z, rfl⟩) hi

theorem leastEqualName_le (C : LanguageFamily) (z : ℕ) :
    leastEqualName C z ≤ z := by
  exact leastEqualName_minimal C z z rfl

/-- Indices in the currently visible finite scope whose languages agree with
all observed labels. -/
noncomputable def informantCompatibleIndices
    (C : LanguageFamily) (history : List InformantDatum) : Finset ℕ := by
  classical
  exact (Finset.range history.length).filter
    (fun i => InformantCompatible history (C i))

@[simp] theorem mem_informantCompatibleIndices
    {C : LanguageFamily} {history : List InformantDatum} {i : ℕ} :
    i ∈ informantCompatibleIndices C history ↔
      i < history.length ∧ InformantCompatible history (C i) := by
  classical
  simp [informantCompatibleIndices]

/-- The least compatible family index below the history length.  `fallback`
is used only before the finite scope contains any compatible candidate. -/
noncomputable def informantEnumerationLearnerWithFallback
    (C : LanguageFamily) (fallback : ℕ) : InformantLearner ℕ := by
  classical
  intro history
  let candidates := informantCompatibleIndices C history
  exact if h : candidates.Nonempty then candidates.min' h else fallback

/-- The canonical totalized informant enumeration learner. -/
noncomputable def informantEnumerationLearner
    (C : LanguageFamily) : InformantLearner ℕ :=
  informantEnumerationLearnerWithFallback C 0

theorem informantEnumerationLearnerWithFallback_eq_min'
    {C : LanguageFamily} {fallback : ℕ}
    {history : List InformantDatum}
    (hne : (informantCompatibleIndices C history).Nonempty) :
    informantEnumerationLearnerWithFallback C fallback history =
      (informantCompatibleIndices C history).min' hne := by
  classical
  simp only [informantEnumerationLearnerWithFallback]
  rw [dif_pos hne]

theorem informantEnumerationLearnerWithFallback_mem
    {C : LanguageFamily} {fallback : ℕ}
    {history : List InformantDatum}
    (hne : (informantCompatibleIndices C history).Nonempty) :
    informantEnumerationLearnerWithFallback C fallback history ∈
      informantCompatibleIndices C history := by
  rw [informantEnumerationLearnerWithFallback_eq_min' hne]
  exact Finset.min'_mem _ _

theorem informantEnumerationLearnerWithFallback_le
    {C : LanguageFamily} {fallback : ℕ}
    {history : List InformantDatum} {i : ℕ}
    (hi : i ∈ informantCompatibleIndices C history) :
    informantEnumerationLearnerWithFallback C fallback history ≤ i := by
  have hne : (informantCompatibleIndices C history).Nonempty := ⟨i, hi⟩
  rw [informantEnumerationLearnerWithFallback_eq_min' hne]
  exact Finset.min'_le _ _ hi

/-- On every complete correct informant, bounded least-compatible
enumeration stabilizes to the least name denoting the target. -/
theorem informantEnumerationLearnerWithFallback_stabilizesTo_leastEqualName
    {C : LanguageFamily} {info : InformantStream} {z fallback : ℕ}
    (hI : IsInformantFor info (C z)) :
    StabilizesTo
      (fun t =>
        informantEnumerationLearnerWithFallback C fallback
          (textPrefix info t))
      (leastEqualName C z) := by
  classical
  let k := leastEqualName C z
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_informantCompatible_iff_eq
      hI (k + 1)
  refine ⟨max T (k + 1), ?_⟩
  intro t ht
  have hTt : T ≤ t :=
    le_trans (Nat.le_max_left T (k + 1)) ht
  have hkt : k < t :=
    lt_of_lt_of_le (Nat.lt_succ_self k)
      (le_trans (Nat.le_max_right T (k + 1)) ht)
  have hkcompat :
      InformantCompatible (textPrefix info t) (C k) := by
    apply informantCompatible_target
    simpa [k, leastEqualName_spec C z] using hI
  have hkmem :
      k ∈ informantCompatibleIndices C (textPrefix info t) := by
    rw [mem_informantCompatibleIndices]
    exact ⟨by simpa using hkt, hkcompat⟩
  have hne :
      (informantCompatibleIndices C (textPrefix info t)).Nonempty :=
    ⟨k, hkmem⟩
  let n :=
    informantEnumerationLearnerWithFallback C fallback
      (textPrefix info t)
  have hnmem :
      n ∈ informantCompatibleIndices C (textPrefix info t) := by
    exact informantEnumerationLearnerWithFallback_mem hne
  have hnk : n ≤ k := by
    exact informantEnumerationLearnerWithFallback_le hkmem
  have hncompat :
      InformantCompatible (textPrefix info t) (C n) :=
    (mem_informantCompatibleIndices.mp hnmem).2
  have hneq : C n = C z := by
    exact (hT t hTt n (Nat.lt_succ_of_le hnk)).1 hncompat
  have hkn : k ≤ n := by
    exact leastEqualName_minimal C z n hneq
  exact Nat.le_antisymm hnk hkn

theorem informantEnumerationLearner_stabilizesTo_leastEqualName
    {C : LanguageFamily} {info : InformantStream} {z : ℕ}
    (hI : IsInformantFor info (C z)) :
    StabilizesTo
      (fun t =>
        informantEnumerationLearner C (textPrefix info t))
      (leastEqualName C z) := by
  exact
    informantEnumerationLearnerWithFallback_stabilizesTo_leastEqualName
      (fallback := 0) hI

/-- The semantic enumeration learner identifies the target on every one of
its complete correct informants. -/
theorem informantEnumerationLearner_identifiesOnInformant
    {C : LanguageFamily} {info : InformantStream} {z : ℕ}
    (hI : IsInformantFor info (C z)) :
    IdentifiesOnInformant (familyNaming C)
      (informantEnumerationLearner C) info (C z) := by
  exact ⟨leastEqualName C z, leastEqualName_spec C z,
    informantEnumerationLearner_stabilizesTo_leastEqualName hI⟩

/-- Every indexed family is semantically identifiable from complete correct
informants.  Duplicate indices are resolved by convergence to the least name
of the target language. -/
theorem informantEnumerationLearner_identifiesFamily
    (C : LanguageFamily) :
    IdentifiesFamilyFromInformant C
      (informantEnumerationLearner C) := by
  intro z info hI
  exact informantEnumerationLearner_identifiesOnInformant hI

end Informant
end Gold
end GenLimit
