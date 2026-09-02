import GenLimit.Paper17_InfiniteContamination.Definitions
import Mathlib.Tactic.FinCases

/-!
# Proper versus improper generation under one contamination

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Examples 3.3 and 3.4.

The source uses positive naturals and removes `1` or `2`.  Lean's naturals
start at zero, so the isomorphic formal example removes `0` or `1`.
-/

namespace GenLimit.InfiniteContamination

/-- The language of all naturals except `a`. -/
def coSingletonLanguage (a : ℕ) : GenLimit.Generic.Language ℕ :=
  {x | x ≠ a}

/-- The two-language collection in Examples 3.3 and 3.4. -/
def coSingletonFamily : Fin 2 → GenLimit.Generic.Language ℕ :=
  ![coSingletonLanguage 0, coSingletonLanguage 1]

/-- The complete canonical enumeration of `ℕ`. -/
def identityStream : GenLimit.Generic.Stream ℕ := fun n => n

theorem identityStream_injective :
    Function.Injective identityStream := by
  intro m n h
  exact h

theorem identityStream_noOmissions (a : ℕ) :
    NoOmissions identityStream (coSingletonLanguage a) := by
  intro x _hx
  exact ⟨x, rfl⟩

theorem identityStream_noise_set (a : ℕ) :
    {t | identityStream t ∉ coSingletonLanguage a} = {a} := by
  ext t
  simp [identityStream, coSingletonLanguage]

theorem identityStream_finiteNoise (a : ℕ) :
    FiniteNoise identityStream (coSingletonLanguage a) := by
  change {t | identityStream t ∉ coSingletonLanguage a}.Finite
  rw [identityStream_noise_set]
  exact Set.finite_singleton a

/-- Example 3.3's common input is a one-noise enumeration for either
co-singleton target. -/
theorem identityStream_finiteNoiseEnumeration (i : Fin 2) :
    FiniteNoiseEnumeration identityStream (coSingletonFamily i) := by
  fin_cases i
  · exact
      ⟨identityStream_injective,
        identityStream_noOmissions 0,
        identityStream_finiteNoise 0⟩
  · exact
      ⟨identityStream_injective,
        identityStream_noOmissions 1,
        identityStream_finiteNoise 1⟩

/-- The common stream in Example 3.4, whose range is `{2,3,...}`. -/
def tailFromTwo : GenLimit.Generic.Stream ℕ := fun n => n + 2

theorem tailFromTwo_injective :
    Function.Injective tailFromTwo := by
  intro m n h
  simp only [tailFromTwo] at h
  omega

theorem mem_range_tailFromTwo_iff {x : ℕ} :
    x ∈ Set.range tailFromTwo ↔ 2 ≤ x := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [tailFromTwo]
  · intro hx
    refine ⟨x - 2, ?_⟩
    simp only [tailFromTwo]
    omega

theorem tailFromTwo_noNoise (a : Fin 2) :
    NoNoise tailFromTwo (coSingletonLanguage a) := by
  rintro x ⟨n, rfl⟩
  simp only [tailFromTwo, coSingletonLanguage, Set.mem_setOf_eq]
  have ha : (a : ℕ) < 2 := a.isLt
  omega

theorem tailFromTwo_omission_zero :
    coSingletonLanguage 0 \ Set.range tailFromTwo = {1} := by
  ext x
  rw [Set.mem_diff, Set.mem_singleton_iff]
  simp only [coSingletonLanguage, Set.mem_setOf_eq,
    mem_range_tailFromTwo_iff]
  omega

theorem tailFromTwo_omission_one :
    coSingletonLanguage 1 \ Set.range tailFromTwo = {0} := by
  ext x
  rw [Set.mem_diff, Set.mem_singleton_iff]
  simp only [coSingletonLanguage, Set.mem_setOf_eq,
    mem_range_tailFromTwo_iff]
  omega

/-- Example 3.4's common input omits exactly one element from either
co-singleton target. -/
theorem tailFromTwo_finiteOmissionEnumeration (i : Fin 2) :
    FiniteOmissionEnumeration tailFromTwo (coSingletonFamily i) := by
  fin_cases i
  · refine ⟨tailFromTwo_injective, tailFromTwo_noNoise 0, ?_⟩
    change FiniteOmissions tailFromTwo (coSingletonLanguage 0)
    rw [FiniteOmissions, tailFromTwo_omission_zero]
    exact Set.finite_singleton 1
  · refine ⟨tailFromTwo_injective, tailFromTwo_noNoise 1, ?_⟩
    change FiniteOmissions tailFromTwo (coSingletonLanguage 1)
    rw [FiniteOmissions, tailFromTwo_omission_one]
    exact Set.finite_singleton 0

/-- No member of the two-language collection is contained in both possible
targets.  This is the semantic obstruction behind both proper-learning
separations. -/
theorem no_common_proper_hypothesis (i : Fin 2) :
    ¬(coSingletonFamily i ⊆ coSingletonFamily 0 ∧
      coSingletonFamily i ⊆ coSingletonFamily 1) := by
  fin_cases i
  · intro h
    have hbad := h.2 (show 1 ∈ coSingletonFamily 0 by
      simp [coSingletonFamily, coSingletonLanguage])
    simp [coSingletonFamily, coSingletonLanguage] at hbad
  · intro h
    have hbad := h.1 (show 0 ∈ coSingletonFamily 1 by
      simp [coSingletonFamily, coSingletonLanguage])
    simp [coSingletonFamily, coSingletonLanguage] at hbad

/-- Example 3.3: on the identical one-noise history, every proper output
fails for at least one of the two possible targets. -/
theorem example_3_3_single_noise_proper_separation
    (gen : IndexGenerator (Fin 2) ℕ) (t : ℕ) :
    ¬(IndexCorrectAt coSingletonFamily gen (coSingletonFamily 0)
        identityStream t ∧
      IndexCorrectAt coSingletonFamily gen (coSingletonFamily 1)
        identityStream t) := by
  intro h
  exact no_common_proper_hypothesis
    (indexOutput gen identityStream t) h

/-- Example 3.4: the same pointwise impossibility holds on the history with
one omission from either possible target. -/
theorem example_3_4_single_omission_proper_separation
    (gen : IndexGenerator (Fin 2) ℕ) (t : ℕ) :
    ¬(IndexCorrectAt coSingletonFamily gen (coSingletonFamily 0)
        tailFromTwo t ∧
      IndexCorrectAt coSingletonFamily gen (coSingletonFamily 1)
        tailFromTwo t) := by
  intro h
  exact no_common_proper_hypothesis
    (indexOutput gen tailFromTwo t) h

end GenLimit.InfiniteContamination
