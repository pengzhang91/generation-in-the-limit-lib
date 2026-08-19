import GenLimit.Paper03_HallucinationAndModeCollapse.Definitions
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization

/-!
# Further qualitative identification results

This file isolates the probability-free cores of Propositions 3.11--3.12 in
Kalavasis--Mehrotra--Velegkas, arXiv:2411.09642v3.

For Proposition 3.11, a finite collection may contain infinite languages.
There are only finitely many proper sublanguages of a fixed target within the
collection, so choosing one target element excluded by each such sublanguage
gives a finite tell-tale.

The source obtains an exponential statistical rate for a countable collection
of finite languages.  The exact deterministic content is that each finite
target is its own finite tell-tale, so Angluin's semantic learner identifies
the collection in the limit.  The IID coverage estimate and exponential-rate
wrapper remain outside this declaration.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic

/-- Every indexed family with finite range satisfies Angluin's finite
tell-tale condition, even when its languages themselves are infinite.

For a target `C i`, choose one target point outside each proper sublanguage
which occurs in the finite range.  Any candidate below the target and
containing all chosen witnesses must therefore equal the target. -/
theorem finiteCollection_conditionTwo
    (C : Generic.LanguageFamily ℕ)
    (hRange : (Set.range C).Finite) :
    GenLimit.Angluin.ConditionTwo C := by
  classical
  intro i
  let languages : Finset (Set ℕ) := hRange.toFinset
  let properBelow : Finset (Set ℕ) :=
    languages.filter fun L => L ⊂ C i
  have hexists (L : {L : Set ℕ // L ∈ properBelow}) :
      ∃ x, x ∈ C i ∧ x ∉ L.1 := by
    have hproper : L.1 ⊂ C i :=
      (Finset.mem_filter.mp L.2).2
    have hnot : ¬C i ⊆ L.1 := by
      intro hsub
      exact hproper.ne (Set.Subset.antisymm hproper.1 hsub)
    exact Set.not_subset.mp hnot
  let witness : {L : Set ℕ // L ∈ properBelow} → ℕ :=
    fun L => Classical.choose (hexists L)
  have hwitness (L : {L : Set ℕ // L ∈ properBelow}) :
      witness L ∈ C i ∧ witness L ∉ L.1 :=
    Classical.choose_spec (hexists L)
  let T : Finset ℕ := properBelow.attach.image witness
  refine ⟨T, ?_, ?_⟩
  · intro x hx
    obtain ⟨L, _hL, rfl⟩ := Finset.mem_image.mp hx
    exact (hwitness L).1
  · intro j hTj hji
    by_contra hnot
    have hproper : C j ⊂ C i :=
      Set.ssubset_iff_subset_ne.mpr
        ⟨hji, fun heq => hnot heq.symm.subset⟩
    have hjLanguages : C j ∈ languages := by
      simp [languages, hRange.mem_toFinset]
    have hjProperBelow : C j ∈ properBelow :=
      Finset.mem_filter.mpr ⟨hjLanguages, hproper⟩
    let L : {L : Set ℕ // L ∈ properBelow} :=
      ⟨C j, hjProperBelow⟩
    have hwT : witness L ∈ T := by
      apply Finset.mem_image.mpr
      exact ⟨L, Finset.mem_attach _ _, rfl⟩
    exact (hwitness L).2 (hTj hwT)

/-- Probability-free online core of Proposition 3.11: every indexed family
with only finitely many distinct languages is semantically identifiable from
positive presentations.  Repeated indices are allowed.

The proposition's exact exponential statistical rate still requires the IID
finite-witness coverage estimate and is not asserted here. -/
theorem proposition_3_11_online_core
    (C : Generic.LanguageFamily ℕ)
    (hRange : (Set.range C).Finite) :
    IdentifiableInLimit C :=
  (GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo C).2
    (finiteCollection_conditionTwo C hRange)

/-- Every indexed family of finite languages satisfies Angluin's finite
tell-tale condition: the whole finite target is a tell-tale for itself. -/
theorem finiteLanguages_conditionTwo
    (C : Generic.LanguageFamily ℕ)
    (hfinite : ∀ i, (C i).Finite) :
    GenLimit.Angluin.ConditionTwo C := by
  intro i
  refine ⟨(hfinite i).toFinset, ?_⟩
  constructor
  · intro x hx
    simpa using hx
  · intro j hcontains _hsub x hxi
    apply hcontains
    simpa using hxi

/-- Probability-free online core of Proposition 3.12: every countable indexed
collection consisting only of finite languages is semantically identifiable
in the limit from positive presentations.

The source's exact exponential statistical rate additionally needs the IID
finite-support coverage bound and is intentionally not asserted here. -/
theorem proposition_3_12_online_core
    (C : Generic.LanguageFamily ℕ)
    (hfinite : ∀ i, (C i).Finite) :
    IdentifiableInLimit C :=
  (GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo C).2
    (finiteLanguages_conditionTwo C hfinite)

end GenLimit.HallucinationModeCollapse
