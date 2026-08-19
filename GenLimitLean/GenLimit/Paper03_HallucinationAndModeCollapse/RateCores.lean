import GenLimit.Paper03_HallucinationAndModeCollapse.Definitions
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper01_LanguageGeneration.Semantic

/-!
# Probability-free cores of the statistical rate theorems

Theorems 3.1, 3.2, 3.6, 3.8, and 3.13 are statistical universal-rate
statements.  This file deliberately does not call them complete.  It checks
the deterministic facts on which their probability arguments rest:

* the qualitative Angluin dichotomy;
* indistinguishability of two targets on a common constant sample;
* the finite-common-intersection obstruction for fresh generation;
* the Kleinberg--Mullainathan online generation engine;
* persistence of a support property after stabilization; and
* the polarity defect in the printed unambiguous-error indicator.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic

noncomputable local instance rateCoresPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## Theorem 3.1 -/

/-- Qualitative core of Theorem 3.1: positive-data identification is
equivalent to existence of finite tell-tales.  This is semantic and does not
assert the paper's universal rate or effective-oracle statement. -/
theorem theorem_3_1_qualitative_core
    (C : Generic.LanguageFamily ℕ) :
    IdentifiableInLimit C ↔ GenLimit.Angluin.ConditionTwo C := by
  exact GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo C

/-- The deterministic ambiguity behind the exponential lower bounds in
Theorems 3.1 and 3.13: the same constant sample is valid for two distinct
targets, so one guess cannot be extensionally correct for both. -/
theorem common_constant_sample_ambiguity
    {C : Generic.LanguageFamily ℕ} {i j x n : ℕ}
    (hij : C i ≠ C j) (hxi : x ∈ C i) (hxj : x ∈ C j)
    (M : GenLimit.Angluin.SemanticIdentifier ℕ) :
    (∀ k : Fin n, (fun _ : Fin n => x) k ∈ C i) ∧
      (∀ k : Fin n, (fun _ : Fin n => x) k ∈ C j) ∧
      (C (M (GenLimit.textPrefix (fun _ : ℕ => x) n)) ≠ C i ∨
        C (M (GenLimit.textPrefix (fun _ : ℕ => x) n)) ≠ C j) := by
  refine ⟨fun _ => hxi, fun _ => hxj, ?_⟩
  by_cases hi : C (M (GenLimit.textPrefix (fun _ : ℕ => x) n)) = C i
  · exact Or.inr (fun hj => hij (hi.symm.trans hj))
  · exact Or.inl hi

/-! ## Theorem 3.2 -/

/-- Common intersection of a finite subcollection, matching Definition 18. -/
def finiteCommonIntersection (F : Finset (Set ℕ)) : Set ℕ :=
  {x | ∀ L, L ∈ F → x ∈ L}

/-- Once the finite common intersection is already in the sample, every fresh
output is rejected by at least one language in the finite subcollection.  This
is the probability-free adversarial core of the generation lower bound. -/
theorem fresh_output_rejected_by_some_language
    {F : Finset (Set ℕ)} {seen : Finset ℕ} {y : ℕ}
    (hcover : finiteCommonIntersection F ⊆ ↑seen)
    (hyfresh : y ∉ seen) :
    ∃ L, L ∈ F ∧ y ∉ L := by
  by_contra h
  push_neg at h
  have hycommon : y ∈ finiteCommonIntersection F :=
    fun L hLF => h L hLF
  exact hyfresh (hcover hycommon)

/-- The online generation engine used in the upper-bound proof of Theorem
3.2.  The statistical `e^{-n}` rate is intentionally not attached. -/
theorem theorem_3_2_online_engine
    (O : GenLimit.OracleFamily)
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : GenLimit.Presents stream (O.language z)) :
    GenLimit.KM.Semantic.GeneratesInLimit O stream z :=
  GenLimit.KM.Semantic.kleinbergMullainathan_main O hP

/-! ## Theorems 3.6 and 3.8 -/

/-- A property depending only on support persists after the support has
stabilized.  The statistical proofs of Theorems 3.6 and 3.8 additionally need
a probability argument to obtain one successful post-stability round. -/
theorem stable_support_property_persists
    {G : SupportGenerator} {stream : Stream ℕ}
    {P : Set ℕ → Prop} {T n : ℕ}
    (hstable : ∀ s t, T ≤ s → T ≤ t →
      supportAt G stream s = supportAt G stream t)
    (hn : T ≤ n) (hgood : P (supportAt G stream n)) :
    ∀ t, T ≤ t → P (supportAt G stream t) := by
  intro t ht
  rw [hstable t n ht hn]
  exact hgood

/-- Deterministic persistence component used by Theorem 3.6. -/
theorem theorem_3_6_stability_core
    {C : Generic.LanguageFamily ℕ} {G : SupportGenerator}
    {stream : Stream ℕ} {z T n : ℕ}
    (hstable : ∀ s t, T ≤ s → T ≤ t →
      supportAt G stream s = supportAt G stream t)
    (hn : T ≤ n)
    (hgood : UnambiguousAt C z (supportAt G stream n)) :
    ∀ t, T ≤ t → UnambiguousAt C z (supportAt G stream t) :=
  stable_support_property_persists hstable hn hgood

/-- Deterministic persistence component used by Theorem 3.8. -/
theorem theorem_3_8_stability_core
    {G : SupportGenerator} {stream : Stream ℕ}
    {K : Set ℕ} {T n : ℕ}
    (hstable : ∀ s t, T ≤ s → T ≤ t →
      supportAt G stream s = supportAt G stream t)
    (hn : T ≤ n)
    (hgood : ApproximateBreadthAt (supportAt G stream n) K) :
    ∀ t, T ≤ t →
      ApproximateBreadthAt (supportAt G stream t) K :=
  stable_support_property_persists
    (P := fun S => ApproximateBreadthAt S K) hstable hn hgood

/-! ## Printed-error diagnostic -/

/-- Equation (unambiguous-error) as printed: it assigns one to success. -/
noncomputable def printedUnambiguousError (good : Prop) : ℕ :=
  if good then 1 else 0

/-- The polarity used by the surrounding rate definition and later proofs. -/
noncomputable def correctedUnambiguousError (good : Prop) : ℕ :=
  if good then 0 else 1

theorem printedUnambiguousError_eq_zero_iff (good : Prop) :
    printedUnambiguousError good = 0 ↔ ¬good := by
  by_cases h : good <;> simp [printedUnambiguousError, h]

theorem correctedUnambiguousError_eq_zero_iff (good : Prop) :
    correctedUnambiguousError good = 0 ↔ good := by
  by_cases h : good <;> simp [correctedUnambiguousError, h]

end GenLimit.HallucinationModeCollapse
