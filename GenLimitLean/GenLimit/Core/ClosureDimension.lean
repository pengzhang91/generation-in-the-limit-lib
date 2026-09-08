import GenLimit.Core.VersionSpace
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Powerset

/-!
# Positive closure dimension

Neutral witness and dimension predicates, together with the combinatorial
facts that do not depend on a particular paper's generation theorems.
-/

namespace GenLimit.Generic

/-- A consistent finite positive sample with finite common core. -/
def IsClosureWitness (H : LanguageClass α) (S : Finset α) : Prop :=
  (versionSpace H S).Nonempty ∧ (commonCore H S).Finite

/-- Every consistent sample larger than `d` has infinite common core. -/
def ClosureDimensionAtMost (H : LanguageClass α) (d : ℕ) : Prop :=
  ∀ S : Finset α, d < S.card → (versionSpace H S).Nonempty →
    (commonCore H S).Infinite

/-- `d` is the largest finite closure-witness size, with the zero convention. -/
def HasClosureDimension (H : LanguageClass α) (d : ℕ) : Prop :=
  ClosureDimensionAtMost H d ∧
    (d = 0 ∨ ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S)

/-- The class has some finite closure dimension. -/
def HasFiniteClosureDimension (H : LanguageClass α) : Prop :=
  ∃ d : ℕ, HasClosureDimension H d

/-- Finite closure witnesses exist at arbitrarily large cardinalities. -/
def HasInfiniteClosureDimension (H : LanguageClass α) : Prop :=
  ∀ d : ℕ, ∃ S : Finset α, d ≤ S.card ∧ IsClosureWitness H S

theorem closure_witness_mono
    {H : LanguageClass α} {S T : Finset α}
    (hST : S ⊆ T) (hT : IsClosureWitness H T) :
    IsClosureWitness H S := by
  rcases hT with ⟨⟨L, hLH, hTL⟩, hcore⟩
  constructor
  · exact ⟨L, hLH, fun x hx ↦ hTL (hST hx)⟩
  · apply hcore.subset
    intro x hx K hK
    exact hx K ⟨hK.1, fun y hy ↦ hK.2 (hST hy)⟩

theorem exists_closure_witness_card_eq
    {H : LanguageClass α}
    (hC : HasInfiniteClosureDimension H) (d : ℕ) :
    ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S := by
  obtain ⟨T, hdT, hT⟩ := hC d
  obtain ⟨S, hST, hSd⟩ := Finset.exists_subset_card_eq hdT
  exact ⟨S, hSd, closure_witness_mono hST hT⟩

theorem finite_closure_dimension_iff_not_infinite
    {H : LanguageClass α} :
    HasFiniteClosureDimension H ↔ ¬ HasInfiniteClosureDimension H := by
  classical
  constructor
  · rintro ⟨d, hd⟩ hInfinite
    obtain ⟨S, hcard, hS⟩ := hInfinite (d + 1)
    have hdS : d < S.card := Nat.lt_of_succ_le hcard
    exact (hd.1 S hdS hS.1) hS.2
  · intro hNotInfinite
    unfold HasInfiniteClosureDimension at hNotInfinite
    push_neg at hNotInfinite
    let P : ℕ → Prop := fun n ↦
      ∀ S : Finset α, n ≤ S.card → ¬ IsClosureWitness H S
    have hPExists : ∃ n, P n := by
      simpa only [P] using hNotInfinite
    let m := Nat.find hPExists
    have hm : P m := Nat.find_spec hPExists
    by_cases hm0 : m = 0
    · refine ⟨0, ?_, Or.inl rfl⟩
      intro S _hcard hVS
      change ¬ (commonCore H S).Finite
      intro hfinite
      exact hm S (by simp [hm0]) ⟨hVS, hfinite⟩
    · obtain ⟨k, hmk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hNotPk : ¬ P k := by
        apply Nat.find_min hPExists
        change k < m
        rw [hmk]
        exact Nat.lt_succ_self k
      dsimp only [P] at hNotPk
      push_neg at hNotPk
      obtain ⟨S, hkS, hS⟩ := hNotPk
      have hSm : S.card < m := by
        by_contra hnot
        exact hm S (Nat.le_of_not_gt hnot) hS
      have hSk : S.card = k := by
        apply Nat.le_antisymm
        · rw [hmk] at hSm
          exact Nat.lt_succ_iff.mp hSm
        · exact hkS
      refine ⟨k, ?_, Or.inr ⟨S, hSk, hS⟩⟩
      intro T hkT hTVS
      change ¬ (commonCore H T).Finite
      intro hfinite
      apply hm T
      · rw [hmk]
        exact Nat.succ_le_iff.mpr hkT
      · exact ⟨hTVS, hfinite⟩

theorem core_diff_sample_infinite
    {H : LanguageClass α} {d : ℕ}
    (hC : ClosureDimensionAtMost H d) (S : Finset α)
    (hd : d < S.card) (hVS : (versionSpace H S).Nonempty) :
    (commonCore H S \ (↑S : Set α)).Infinite :=
  (hC S hd hVS).diff S.finite_toSet

/-- Every finite language class has finite positive closure dimension.

This is paper-independent finite-class infrastructure.  The proof takes the
maximum cardinality of the finite intersections arising from subcollections
of `H`; a larger consistent sample must therefore have infinite common core.
-/
theorem finite_language_class_has_finite_closure_dimension
    {H : LanguageClass α} (hH : H.Finite) :
    HasFiniteClosureDimension H := by
  classical
  apply finite_closure_dimension_iff_not_infinite.mpr
  intro hInfinite
  let coreOf : Set (Language α) → Language α :=
    fun V ↦ {x | ∀ L, L ∈ V → x ∈ L}
  have hcoresFinite : (coreOf '' Set.powerset H).Finite :=
    hH.powerset.image coreOf
  let cores : Finset (Language α) := hcoresFinite.toFinset
  let bound : ℕ := cores.sup Set.ncard
  obtain ⟨S, hlarge, hS⟩ := hInfinite (bound + 1)
  have hcoreMem : commonCore H S ∈ cores := by
    change commonCore H S ∈ hcoresFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨versionSpace H S, ?_, rfl⟩
    exact fun L hL ↦ hL.1
  have hcoreBound : (commonCore H S).ncard ≤ bound := by
    exact Finset.le_sup (f := Set.ncard) hcoreMem
  have hsampleCore : S.card ≤ (commonCore H S).ncard := by
    simpa using Set.ncard_le_ncard sample_subset_commonCore hS.2
  omega

end GenLimit.Generic
