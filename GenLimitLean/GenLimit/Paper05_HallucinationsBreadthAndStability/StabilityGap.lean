import GenLimit.Paper05_HallucinationsBreadthAndStability.ExactBreadth
import GenLimit.Support.EnumerationProgress

/-!
# Literal stability countertheorems

Definitions 3.1 and 8.3 require outputs to avoid the cumulative observed
sample, while Definition 3.14 requires the raw output support eventually to
be exactly constant.  On a complete presentation of an infinite language
these requirements are incompatible.

These are countertheorems to the literal conjunctions in the pinned source,
not formalizations of a repaired sample-allowing convention.
-/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Generic

/-- A raw-stable support cannot have literal exact breadth on a presentation
of an infinite target. -/
theorem stable_exactBreadth_false_on_presentation
    {G : SupportAlgorithm α} {K : Generic.Language α}
    {stream : Generic.Stream α}
    (hK : K.Infinite)
    (hP : Generic.Presents stream K)
    (hStable : ∃ T, ∀ n n', T ≤ n → T ≤ n' →
      supportAt G stream n = supportAt G stream n')
    (hExact : ∃ T, ∀ t, T ≤ t →
      ExactBreadthCorrectAt G K stream t) :
    False := by
  classical
  obtain ⟨Ts, hTs⟩ := hStable
  obtain ⟨Te, hTe⟩ := hExact
  let n := max Ts Te
  obtain ⟨x, hxK, hxNotSample⟩ :=
    hK.exists_notMem_finset (Generic.sample stream n)
  obtain ⟨Tx, hTx⟩ :=
    Generic.eventually_mem_sample_of_presents hP hxK
  let m := max n Tx
  have hTsN : Ts ≤ n := Nat.le_trans (Nat.le_max_left _ _) (le_rfl)
  have hTeN : Te ≤ n := Nat.le_trans (Nat.le_max_right _ _) (le_rfl)
  have hNm : n ≤ m := Nat.le_max_left _ _
  have hTsM : Ts ≤ m := le_trans hTsN hNm
  have hTeM : Te ≤ m := le_trans hTeN hNm
  have hxSampleM : x ∈ Generic.sample stream m :=
    hTx m (Nat.le_max_right _ _)
  have hxAtN : x ∈ supportAt G stream n := by
    rw [hTe n hTeN]
    exact ⟨hxK, hxNotSample⟩
  have hSupports : supportAt G stream n = supportAt G stream m :=
    hTs n m hTsN hTsM
  have hxAtM : x ∈ supportAt G stream m := hSupports ▸ hxAtN
  rw [hTe m hTeM] at hxAtM
  exact hxAtM.2 hxSampleM

/-- Family-level form of the literal obstruction, assuming one explicitly
presented infinite member. -/
theorem no_stable_exactBreadth_on_presented_infinite_member
    {F : Generic.LanguageFamily α} (z : ℕ)
    (stream : Generic.Stream α)
    (hP : Generic.Presents stream (F z))
    (hInfinite : (F z).Infinite) :
    ¬ ∃ G : SupportAlgorithm α,
      IsStableGenerator G F ∧ IsExactBreadthGenerator G F := by
  rintro ⟨G, hStable, hExact⟩
  exact stable_exactBreadth_false_on_presentation
    hInfinite hP (hStable z stream hP) (hExact z stream hP)

/-- For a countable universe and a family of infinite languages, the literal
stable-exact clause in Theorems 3.15 and 4.5 is impossible. -/
theorem no_stable_exactBreadth_for_infinite_family
    [Countable α] (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    ¬ ∃ G : SupportAlgorithm α,
      IsStableGenerator G F ∧ IsExactBreadthGenerator G F := by
  let stream :=
    GenLimit.Support.infiniteEnumeration (F 0) (hInfinite 0)
  have hP : Generic.Presents stream (F 0) :=
    GenLimit.Support.infiniteEnumeration_presents
      (F 0) (hInfinite 0)
  exact no_stable_exactBreadth_on_presented_infinite_member 0 stream hP
    (hInfinite 0)

/-- A raw-stable support cannot remain nonempty, valid, and disjoint from
every cumulative prefix of a complete target presentation. -/
theorem stable_infiniteCoverage_false_on_presentation
    {G : SupportAlgorithm α} {K : Generic.Language α}
    {stream : Generic.Stream α}
    (hP : Generic.Presents stream K)
    (hStable : ∃ T, ∀ n n', T ≤ n → T ≤ n' →
      supportAt G stream n = supportAt G stream n')
    (hCoverage : ∃ T, ∀ t, T ≤ t →
      InfiniteCoverageCorrectAt G K stream t) :
    False := by
  classical
  obtain ⟨Ts, hTs⟩ := hStable
  obtain ⟨Tc, hTc⟩ := hCoverage
  let n := max Ts Tc
  have hTsN : Ts ≤ n := Nat.le_max_left _ _
  have hTcN : Tc ≤ n := Nat.le_max_right _ _
  have hCoverN := hTc n hTcN
  obtain ⟨x, hxAtN⟩ := hCoverN.2.2.nonempty
  have hxK : x ∈ K := hCoverN.1 hxAtN
  obtain ⟨Tx, hTx⟩ :=
    Generic.eventually_mem_sample_of_presents hP hxK
  let m := max n Tx
  have hNm : n ≤ m := Nat.le_max_left _ _
  have hTsM : Ts ≤ m := le_trans hTsN hNm
  have hTcM : Tc ≤ m := le_trans hTcN hNm
  have hxSampleM : x ∈ Generic.sample stream m :=
    hTx m (Nat.le_max_right _ _)
  have hSupports : supportAt G stream n = supportAt G stream m :=
    hTs n m hTsN hTsM
  have hxAtM : x ∈ supportAt G stream m := hSupports ▸ hxAtN
  have hCoverM := hTc m hTcM
  exact Set.disjoint_left.mp hCoverM.2.1 hxAtM hxSampleM

/-- Family-level form of the Definition 8.3 obstruction. -/
theorem no_stable_infiniteCoverage_on_presented_member
    {F : Generic.LanguageFamily α} (z : ℕ)
    (stream : Generic.Stream α)
    (hP : Generic.Presents stream (F z)) :
    ¬ ∃ G : SupportAlgorithm α,
      IsStableGenerator G F ∧ IsInfiniteCoverageGenerator G F := by
  rintro ⟨G, hStable, hCoverage⟩
  exact stable_infiniteCoverage_false_on_presentation
    hP (hStable z stream hP) (hCoverage z stream hP)

/-- On the paper's standing assumption that every language is infinite,
literal stable infinite coverage is impossible for the entire family.
This contradicts the literal statements of Proposition 8.10 and
Corollary 8.11(2). -/
theorem no_stable_infiniteCoverage_for_infinite_family
    [Countable α] (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    ¬ ∃ G : SupportAlgorithm α,
      IsStableGenerator G F ∧ IsInfiniteCoverageGenerator G F := by
  let stream :=
    GenLimit.Support.infiniteEnumeration (F 0) (hInfinite 0)
  have hP : Generic.Presents stream (F 0) :=
    GenLimit.Support.infiniteEnumeration_presents
      (F 0) (hInfinite 0)
  exact no_stable_infiniteCoverage_on_presented_member 0 stream hP

end GenLimit.BreadthCharacterizations
