import GenLimit.Paper14_ListLanguageIdentification.Psi
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization

/-!
# Stabilization of the least eligible index

This is the finite-history convergence mechanism used in Claim 5.1 of
Charikar--Pabbaraju--Tewari.  It is stated for an arbitrary set of active
indices and arbitrary assigned finite witnesses, so it can be reused at each
recursive level of Algorithm 1.
-/

namespace GenLimit.ListIdentification

/-- At a finite sample `S`, index `i` is eligible at the current recursive
level when it is active, is consistent with the data, and its assigned
finite witness has appeared. -/
def LevelEligible
    (F : GenLimit.Generic.LanguageFamily α)
    (T : ℕ → Finset α) (I : Set ℕ)
    (S : Finset α) (i : ℕ) : Prop :=
  i ∈ I ∧
    (↑S : Set α) ⊆ F i ∧
    T i ⊆ S

/-- The least eligible index, with the paper's arbitrary default `0` when
there is no eligible index. -/
noncomputable def levelChoice
    (F : GenLimit.Generic.LanguageFamily α)
    (T : ℕ → Finset α) (I : Set ℕ)
    (S : Finset α) : ℕ := by
  classical
  exact
    if h : ∃ i, LevelEligible F T I S i then
      Nat.find h
    else
      0

theorem levelChoice_eligible
    {F : GenLimit.Generic.LanguageFamily α}
    {T : ℕ → Finset α} {I : Set ℕ} {S : Finset α}
    (h : ∃ i, LevelEligible F T I S i) :
    LevelEligible F T I S (levelChoice F T I S) := by
  classical
  rw [levelChoice, dif_pos h]
  exact Nat.find_spec h

theorem levelChoice_le_of_eligible
    {F : GenLimit.Generic.LanguageFamily α}
    {T : ℕ → Finset α} {I : Set ℕ} {S : Finset α}
    {i : ℕ} (hi : LevelEligible F T I S i) :
    levelChoice F T I S ≤ i := by
  classical
  let h : ∃ j, LevelEligible F T I S j := ⟨i, hi⟩
  rw [levelChoice, dif_pos h]
  exact Nat.find_min' h hi

/-- An index which can remain eligible forever on a presentation of `F z`.
The explicit bound `i ≤ z` makes the comparison set finite in exactly the
way used in the proof of Claim 5.1. -/
def LimitCandidate
    (F : GenLimit.Generic.LanguageFamily α)
    (T : ℕ → Finset α) (I : Set ℕ)
    (z i : ℕ) : Prop :=
  i ∈ I ∧
    i ≤ z ∧
    F z ⊆ F i ∧
    (↑(T i) : Set α) ⊆ F z

/-- The limiting least eligible index selected in Claim 5.1. -/
noncomputable def limitChoice
    (F : GenLimit.Generic.LanguageFamily α)
    (T : ℕ → Finset α) (I : Set ℕ)
    (z : ℕ) : ℕ := by
  classical
  exact
    if h : ∃ i, LimitCandidate F T I z i then
      Nat.find h
    else
      0

theorem limitChoice_spec
    {F : GenLimit.Generic.LanguageFamily α}
    {T : ℕ → Finset α} {I : Set ℕ} {z : ℕ}
    (h : ∃ i, LimitCandidate F T I z i) :
    LimitCandidate F T I z (limitChoice F T I z) := by
  classical
  rw [limitChoice, dif_pos h]
  exact Nat.find_spec h

theorem limitChoice_le_of_candidate
    {F : GenLimit.Generic.LanguageFamily α}
    {T : ℕ → Finset α} {I : Set ℕ} {z i : ℕ}
    (hi : LimitCandidate F T I z i) :
    limitChoice F T I z ≤ i := by
  classical
  let h : ∃ j, LimitCandidate F T I z j := ⟨i, hi⟩
  rw [limitChoice, dif_pos h]
  exact Nat.find_min' h hi

/-- Claim 5.1's stabilization argument.

If the target index is active and every active index's assigned witness lies
inside its own language, then the least finite-stage eligible index eventually
stabilizes.  Its stable value is the least active index at most `z` which
contains the target and whose witness lies in the target.
-/
theorem levelChoice_stabilizes
    {F : GenLimit.Generic.LanguageFamily α}
    {T : ℕ → Finset α} {I : Set ℕ} {z : ℕ}
    {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream (F z))
    (hzI : z ∈ I)
    (hT : ∀ i, i ∈ I → (↑(T i) : Set α) ⊆ F i) :
    ∃ N, ∀ t, N ≤ t →
      levelChoice F T I (GenLimit.Generic.sample stream t) =
        limitChoice F T I z := by
  classical
  have hzCandidate : LimitCandidate F T I z z := by
    exact ⟨hzI, le_rfl, Set.Subset.rfl, hT z hzI⟩
  let hex : ∃ i, LimitCandidate F T I z i := ⟨z, hzCandidate⟩
  let q : ℕ := limitChoice F T I z
  have hq : LimitCandidate F T I z q := by
    simpa [q] using limitChoice_spec hex
  have hqle : q ≤ z := hq.2.1
  obtain ⟨Nq, hTqNq⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hP (T q) hq.2.2.2
  have hpointwise :
      ∀ i, i < q → ∃ N, ∀ t, N ≤ t →
        ¬LevelEligible F T I (GenLimit.Generic.sample stream t) i := by
    intro i hi
    by_cases hiI : i ∈ I
    · by_cases hzi : F z ⊆ F i
      · have hnotTi : ¬(↑(T i) : Set α) ⊆ F z := by
          intro hTi
          have hiCandidate : LimitCandidate F T I z i := by
            exact ⟨hiI, (Nat.le_of_lt hi).trans hqle, hzi, hTi⟩
          have hqlei : q ≤ i := by
            simpa [q] using limitChoice_le_of_candidate hiCandidate
          exact (Nat.not_lt_of_ge hqlei) hi
        obtain ⟨x, hxTi, hxnotTarget⟩ := Set.not_subset.mp hnotTi
        refine ⟨0, ?_⟩
        intro t _ hEligible
        have hxSample : x ∈ GenLimit.Generic.sample stream t :=
          hEligible.2.2 hxTi
        exact hxnotTarget
          (GenLimit.Generic.mem_language_of_mem_sample_of_presents hP hxSample)
      · obtain ⟨x, hxTarget, hxnotCandidate⟩ := Set.not_subset.mp hzi
        obtain ⟨Ni, hNi⟩ :=
          GenLimit.Generic.eventually_mem_sample_of_presents hP hxTarget
        refine ⟨Ni, ?_⟩
        intro t ht hEligible
        exact hxnotCandidate (hEligible.2.1 (hNi t ht))
    · refine ⟨0, ?_⟩
      intro _ _ hEligible
      exact hiI hEligible.1
  obtain ⟨Nlower, hLower⟩ :=
    GenLimit.Angluin.eventually_all_lt hpointwise
  refine ⟨max Nq Nlower, ?_⟩
  intro t ht
  have hNqt : Nq ≤ t := (Nat.le_max_left _ _).trans ht
  have hNlowert : Nlower ≤ t := (Nat.le_max_right _ _).trans ht
  have hTqSample : T q ⊆ GenLimit.Generic.sample stream t :=
    hTqNq.trans (GenLimit.Generic.sample_mono hNqt)
  have hSampleTarget :
      (↑(GenLimit.Generic.sample stream t) : Set α) ⊆ F z := by
    intro x hx
    exact GenLimit.Generic.mem_language_of_mem_sample_of_presents hP hx
  have hqEligible :
      LevelEligible F T I (GenLimit.Generic.sample stream t) q := by
    exact ⟨hq.1, hSampleTarget.trans hq.2.2.1, hTqSample⟩
  have hexStage :
      ∃ i, LevelEligible F T I (GenLimit.Generic.sample stream t) i :=
    ⟨q, hqEligible⟩
  let j := levelChoice F T I (GenLimit.Generic.sample stream t)
  have hjEligible :
      LevelEligible F T I (GenLimit.Generic.sample stream t) j := by
    simpa [j] using levelChoice_eligible hexStage
  have hjle : j ≤ q := by
    simpa [j] using levelChoice_le_of_eligible hqEligible
  have hjnotlt : ¬j < q := by
    intro hjlt
    exact hLower t hNlowert j hjlt hjEligible
  have hjq : j = q := Nat.le_antisymm hjle (Nat.not_lt.mp hjnotlt)
  simpa [j, q] using hjq

end GenLimit.ListIdentification
