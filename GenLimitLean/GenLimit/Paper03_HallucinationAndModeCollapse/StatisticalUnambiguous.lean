import GenLimit.Paper03_HallucinationAndModeCollapse.UnambiguousModel
import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineReductions
import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalNecessity

/-!
# Theorem 3.6: no statistical rate for unambiguous generation

A strict closest language, if it exists, is unique up to duplicate indices.
Classical selection therefore turns any support-valued finite-sample rule
into a semantic identifier whose error is bounded by unambiguous-generation
failure. The statistical necessity theorem for arbitrary randomized kernels
then gives a fixed-distribution lower bound of one half infinitely often.

This is an alternative proof and a strengthening in the library's semantic
identifiability model. The classifier is not asserted computable; it is used
only as input to a theorem covering all semantic kernels. Thus the stronger
lemma needs neither stability nor MOP. The source-facing Theorem 3.6 retains
both hypotheses. No randomized-to-deterministic online derandomization or
uniformization of pointwise MOP is assumed, and source Lemmas 7.3--7.4 are
not duplicated. The source's error-polarity correction is explicit in
`UnambiguousModel`.
-/

namespace GenLimit.HallucinationModeCollapse

noncomputable section

open GenLimit.Generic GenLimit.DiscreteIID Filter

/-- Strict closeness identifies one extensional target, even with repeated
indices or infinite symmetric differences in the collection. -/
theorem unambiguousAt_unique {C : Generic.LanguageFamily ℕ} {S : Set ℕ} {i j : ℕ}
    (hi : UnambiguousAt C i S) (hj : UnambiguousAt C j S) : C i = C j := by
  by_contra hne
  exact lt_asymm (hi j (Ne.symm hne)) (hj i hne)

def closestLanguageIndex (C : Generic.LanguageFamily ℕ) (S : Set ℕ) : ℕ := by
  classical
  exact if h : ∃ i, UnambiguousAt C i S then Nat.find h else 0

theorem closestLanguageIndex_correct {C : Generic.LanguageFamily ℕ} {S : Set ℕ} {i : ℕ}
    (hi : UnambiguousAt C i S) : C (closestLanguageIndex C S) = C i := by
  classical
  let hex : ∃ j, UnambiguousAt C j S := ⟨i, hi⟩
  rw [closestLanguageIndex, dif_pos hex]
  exact unambiguousAt_unique (Nat.find_spec hex) hi

/-- A semantic classifier for proof use. No algorithm for deciding strict
closeness of infinite sets, or for finding a closest language, is claimed. -/
def closestSupportIdentifier (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator) :
    GenLimit.Learner ℕ ℕ := fun xs => closestLanguageIndex C (G xs).support

theorem identificationError_le_unambiguousError (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) :
    identificationError C (deterministicIdentifier (closestSupportIdentifier C G)) p i n ≤
      unambiguousError C G p i n := by
  rw [identificationError_deterministic]
  apply probability_mono
  intro xs hwrong hgood
  exact hwrong (closestLanguageIndex_correct hgood)

/-- A quantitative semantic strengthening of Theorem 3.6. It applies to every
PMF kernel and requires neither stable supports nor a computable support oracle. -/
theorem unambiguousError_frequently_ge_half (C : Generic.LanguageFamily ℕ)
    (hC : ¬IdentifiableInLimit C) (G : StatisticalGenerator) :
    ∃ i p, ValidDistribution C i p ∧
      ∃ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ unambiguousError C G p i n := by
  have hnot : ¬GenLimit.Angluin.ConditionTwo C :=
    fun h => hC ((GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo C).mpr h)
  obtain ⟨i, p, hp, hf⟩ := lemma_5_8_frequently C hnot
    (deterministicIdentifier (closestSupportIdentifier C G))
  exact ⟨i, p, hp, hf.mono (fun n hn => hn.trans (identificationError_le_unambiguousError C G p i n))⟩

theorem unambiguousError_limsup_ge_half (C : Generic.LanguageFamily ℕ)
    (hC : ¬IdentifiableInLimit C) (G : StatisticalGenerator) :
    ∃ i p, ValidDistribution C i p ∧
      (1 / 2 : ℝ) ≤ limsup (fun n => unambiguousError C G p i n) atTop := by
  obtain ⟨i, p, hp, hf⟩ := unambiguousError_frequently_ge_half C hC G
  exact ⟨i, p, hp, le_limsup_of_frequently_le hf
    (isBoundedUnder_of ⟨1, unambiguousError_le_one C G p i⟩)⟩

theorem noUnambiguousRate_of_not_identifiable (C : Generic.LanguageFamily ℕ)
    (hC : ¬IdentifiableInLimit C) (G : StatisticalGenerator) : NoUnambiguousRate C G := by
  obtain ⟨i, p, hp, hl⟩ := unambiguousError_limsup_ge_half C hC G
  exact ⟨i, p, hp, lt_of_lt_of_le (by norm_num) hl⟩

/-- Theorem 3.6 with the source's stability and pointwise decidable-MOP
hypotheses. The loss is failure of strict unambiguity, correcting the printed
success-indicator polarity. Positive limsup excludes every vanishing rate,
including distribution-dependent positive horizontal and vertical scaling. -/
theorem theorem_3_6 (C : Generic.LanguageFamily ℕ) (hC : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (_hstable : StatisticalStable G C) (_hMOP : DecidableMOP G) :
    NoUnambiguousRate C G :=
  noUnambiguousRate_of_not_identifiable C hC G

end
end GenLimit.HallucinationModeCollapse
