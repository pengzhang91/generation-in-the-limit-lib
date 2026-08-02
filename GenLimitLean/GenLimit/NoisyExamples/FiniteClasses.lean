import GenLimit.NoisyExamples.NoisyClosure
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Powerset

/-!
# Raman--Raman: finite classes under bounded noise

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Corollary 3.4.

The paper gives the quantitative estimate `NC_n(H) < n |H| + d + 1`,
where `d` bounds the size of every finite intersection arising from a
subclass.  The proof below records that same counting argument: each observed
example is either in the common core of the noisy version space or is one of
at most `n` disagreements for some member of that version space.
-/

namespace GenLimit.NoisyExamples

private def classCore
    (V : Set (GenLimit.Generic.Language α)) :
    GenLimit.Generic.Language α :=
  {x | ∀ L, L ∈ V → x ∈ L}

private theorem noisyCommonCore_eq_classCore
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) (n : ℕ) :
    noisyCommonCore H S n = classCore (noisyVersionSpace H S n) :=
  rfl

/-- A finite class has a uniform bound on the cardinalities of all finite
cores of its subclasses. -/
private theorem finite_class_has_core_bound
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite) :
    ∃ B : ℕ, ∀ V : Set (GenLimit.Generic.Language α),
      V ⊆ H → (classCore V).Finite → (classCore V).ncard ≤ B := by
  classical
  have hcoresFinite : (classCore '' Set.powerset H).Finite :=
    hH.powerset.image classCore
  let cores : Finset (GenLimit.Generic.Language α) := hcoresFinite.toFinset
  let B : ℕ := cores.sup Set.ncard
  refine ⟨B, ?_⟩
  intro V hVH hcore
  have hmem : classCore V ∈ cores := by
    change classCore V ∈ hcoresFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨V, hVH, rfl⟩
  exact Finset.le_sup (f := Set.ncard) hmem

/-- The counting inequality at the heart of Corollary 3.4. -/
theorem noisy_witness_card_le_for_finite_class
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite)
    (B : ℕ)
    (hB : ∀ V : Set (GenLimit.Generic.Language α),
      V ⊆ H → (classCore V).Finite → (classCore V).ncard ≤ B)
    {S : Finset α} {n : ℕ}
    (hcore : (noisyCommonCore H S n).Finite) :
    S.card ≤ B + H.ncard * n := by
  classical
  let Vset := noisyVersionSpace H S n
  have hVfinite : Vset.Finite := by
    apply hH.subset
    intro L hL
    exact hL.1
  let V : Finset (GenLimit.Generic.Language α) := hVfinite.toFinset
  let bad : Finset α := V.biUnion (fun L ↦ negativePart S L)
  let C : Finset α := hcore.toFinset
  have hcover : S ⊆ C ∪ bad := by
    intro x hxS
    by_cases hxcore : x ∈ noisyCommonCore H S n
    · exact Finset.mem_union_left bad (by simpa [C] using hxcore)
    · apply Finset.mem_union_right C
      simp only [noisyCommonCore, Set.mem_setOf_eq, not_forall] at hxcore
      obtain ⟨L, hLVS, hxL⟩ := hxcore
      apply Finset.mem_biUnion.mpr
      refine ⟨L, ?_, ?_⟩
      · change L ∈ hVfinite.toFinset
        rw [Set.Finite.mem_toFinset]
        exact hLVS
      · simp [negativePart, hxS, hxL]
  have hbad : bad.card ≤ V.card * n := by
    apply Finset.card_biUnion_le_card_mul
    intro L hLV
    apply negativePart_card_le_of_mem_noisyVersionSpace
    change L ∈ hVfinite.toFinset at hLV
    simpa only [Set.Finite.mem_toFinset] using hLV
  have hVcard : V.card ≤ H.ncard := by
    rw [Set.ncard_eq_toFinset_card H hH]
    apply Finset.card_le_card
    intro L hLV
    rw [Set.Finite.mem_toFinset]
    change L ∈ hVfinite.toFinset at hLV
    have hLVS : L ∈ Vset := by
      simpa only [Set.Finite.mem_toFinset] using hLV
    exact hLVS.1
  have hCcard : C.card ≤ B := by
    have hcoreEq : noisyCommonCore H S n = classCore Vset :=
      noisyCommonCore_eq_classCore H S n
    have hVsub : Vset ⊆ H := by
      intro L hL
      exact hL.1
    have hbound : (classCore Vset).ncard ≤ B :=
      hB Vset hVsub (hcoreEq ▸ hcore)
    change hcore.toFinset.card ≤ B
    rw [← Set.ncard_eq_toFinset_card _ hcore]
    simpa only [hcoreEq] using hbound
  calc
    S.card ≤ (C ∪ bad).card := Finset.card_le_card hcover
    _ ≤ C.card + bad.card := Finset.card_union_le C bad
    _ ≤ B + V.card * n := Nat.add_le_add hCcard hbad
    _ ≤ B + H.ncard * n := Nat.add_le_add_left
      (Nat.mul_le_mul_right n hVcard) B

/-- Every finite class has finite noisy closure dimension at every noise
level, the combinatorial statement used in Corollary 3.4. -/
theorem finite_class_has_finite_noisyClosureDimensionAt
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite)
    (n : ℕ) : FiniteNoisyClosureDimensionAt H n := by
  classical
  obtain ⟨B, hB⟩ := finite_class_has_core_bound hH
  let D := B + H.ncard * n
  refine ⟨D, ?_⟩
  intro d hDd hwit
  obtain ⟨S, hScard, _hVS, hcore⟩ := hwit
  have hcard : S.card ≤ B + H.ncard * n :=
    noisy_witness_card_le_for_finite_class hH B hB hcore
  have hdD : d ≤ D := by
    rw [← hScard]
    exact hcard
  exact (Nat.not_le_of_gt hDd) hdD

/-- Corollary 3.4 (All Finite Classes are Uniformly Noise-dependent
Generatable). -/
theorem corollary_3_4 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hH : H.Finite) :
    UniformNoiseDependentGeneratable H := by
  apply (theorem_3_3 hUUS).mpr
  intro n
  exact finite_class_has_finite_noisyClosureDimensionAt hH n

end GenLimit.NoisyExamples
