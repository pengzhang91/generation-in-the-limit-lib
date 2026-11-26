import GenLimit.Support.DiscreteIID
import GenLimit.Support.FiniteTellTale
import GenLimit.Core.Identification

/-! # Agnostic identification and generation

The loss definitions of Høgsgaard and Pabbaraju (arXiv:2601.23258v4)
use the ordered IID sample and its multiplicities. Identifiers return an
index into the given countable family. Probability kernels include
randomized algorithms, independently of a representation of their coins.
-/

namespace GenLimit.AgnosticLanguage
open Generic DiscreteIID
open scoped Classical
noncomputable section

abbrev Identifier (α : Type*) := GenLimit.Learner α (PMF ℕ)
abbrev StatisticalGenerator (α : Type*) := List α → PMF α

def risk (p : PMF α) (L : Generic.Language α) : ℝ := probability p Lᶜ
def optimalRisk (C : Generic.LanguageFamily α) (p : PMF α) : ℝ := ⨅ j, risk p (C j)
def Optimal (C : Generic.LanguageFamily α) (p : PMF α) (j : ℕ) : Prop := risk p (C j) = optimalRisk C p
def MinimalOptimal (C : Generic.LanguageFamily α) (p : PMF α) (j : ℕ) : Prop :=
  Optimal C p j ∧ ∀ k, Optimal C p k → ¬ C k ⊂ C j

def HasSupportedTellTale (C : Generic.LanguageFamily α) (p : PMF α) : Prop :=
  ∃ j, Optimal C p j ∧ ∃ T : Finset α, IsFiniteTellTale (Set.range C) (C j) T ∧ (T : Set α) ⊆ p.support

def deterministic (A : List α → β) (xs : List α) : PMF β := PMF.pure (A xs)

/-- Expected excess risk over the sample and the learner's randomness. -/
def idErr (C : Generic.LanguageFamily α) (A : Identifier α) (p : PMF α) (n : ℕ) : ℝ :=
  ∑' j, (((samples p n).bind A) j).toReal * (risk p (C j) - optimalRisk C p)

def idP (C : Generic.LanguageFamily α) (A : Identifier α) (p : PMF α) (n : ℕ) : ℝ :=
  probability ((samples p n).bind A) {j | ¬ MinimalOptimal C p j}

def genErr (A : StatisticalGenerator α) (p : PMF α) (n : ℕ) : ℝ :=
  probability ((samples p n).bind (fun xs => (A xs).map (Prod.mk xs)))
    {z | z.2 ∉ p.support ∨ z.2 ∈ z.1}

theorem optimalRisk_nonneg (C : Generic.LanguageFamily α) (p : PMF α) : 0 ≤ optimalRisk C p :=
  le_ciInf (fun _ ↦ probability_nonneg ..)

theorem optimalRisk_le (C : Generic.LanguageFamily α) (p : PMF α) (j : ℕ) :
    optimalRisk C p ≤ risk p (C j) :=
  ciInf_le ⟨0, fun _ ⟨_,h⟩ ↦ h ▸ probability_nonneg ..⟩ j

theorem optimal_iff (C : Generic.LanguageFamily α) (p : PMF α) (j : ℕ) :
    Optimal C p j ↔ ∀ k, risk p (C j) ≤ risk p (C k) :=
  ⟨fun h k ↦ (le_of_eq h).trans (optimalRisk_le C p k),
   fun h ↦ le_antisymm (le_ciInf h) (optimalRisk_le C p j)⟩

theorem prob_event_tsum (q : PMF β) (E : Set β) :
    probability q E = ∑' j, (q j).toReal * (if j ∈ E then (1:ℝ) else 0) := by
  classical
  unfold probability
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro j
    by_cases h : j ∈ E <;> simp [h]
  · intro j
    by_cases h : j ∈ E <;> simp [h, q.apply_ne_top]

theorem weighted_summable (q : PMF β) {v : β → ℝ} (h : ∀ j, v j ∈ Set.Icc 0 1) :
    Summable (fun j ↦ (q j).toReal * v j) :=
  (ENNReal.summable_toReal (q.tsum_coe ▸ ENNReal.one_ne_top)).of_nonneg_of_le
    (fun j ↦ mul_nonneg ENNReal.toReal_nonneg (h j).1)
    (fun j ↦ mul_le_of_le_one_right ENNReal.toReal_nonneg (h j).2)

theorem excess_unit (C : Generic.LanguageFamily α) (p : PMF α) (j : ℕ) :
    risk p (C j) - optimalRisk C p ∈ Set.Icc 0 1 :=
  ⟨sub_nonneg.mpr (optimalRisk_le ..), (sub_le_self _ (optimalRisk_nonneg ..)).trans (probability_le_one ..)⟩

theorem idErr_le_failure (C : Generic.LanguageFamily α) (A : Identifier α) (p : PMF α) (n : ℕ) :
    idErr C A p n ≤ probability ((samples p n).bind A) {j | ¬ Optimal C p j} := by
  classical
  rw [prob_event_tsum]
  apply Summable.tsum_le_tsum _ (weighted_summable _ (excess_unit C p)) (weighted_summable _ ?_)
  · intro j
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    by_cases h : Optimal C p j <;> simp only [Set.mem_setOf_eq, h, not_true_eq_false, not_false_eq_true, if_true, if_false]
    · rw [show risk p (C j) = _ from h, sub_self]
    · exact (excess_unit C p j).2
  · intro j
    split <;> norm_num

theorem probability_deterministic (q : PMF α) (A : α → β) (E : Set β) :
    probability (q.bind (fun x ↦ PMF.pure (A x))) E = probability q (A ⁻¹' E) := by
  unfold probability
  change ((q.map A).toOuterMeasure E).toReal = _
  rw [PMF.toOuterMeasure_map_apply]

theorem genErr_deterministic (A : List α → α) (p : PMF α) (n : ℕ) :
    genErr (deterministic A) p n = probability (samples p n) {xs | A xs ∉ p.support ∨ A xs ∈ xs} := by
  unfold genErr deterministic
  simp only [PMF.pure_map]
  exact probability_deterministic ..

end
end GenLimit.AgnosticLanguage
