import GenLimit.Paper03_HallucinationAndModeCollapse.Definitions

/-!
# Finite tell-tale consequences

These structural lemmas are motivated by ingredients in the proofs of
Propositions 3.11--3.12 of Kalavasis--Mehrotra--Velegkas,
arXiv:2411.09642v3.  They are not wrappers for those statistical propositions:
the IID coverage estimates and exponential-rate conclusions are not
formalized.

For Proposition 3.11, a finite collection may contain infinite languages.
There are only finitely many proper sublanguages of a fixed target within the
collection, so choosing one target element excluded by each such sublanguage
gives a finite tell-tale.

For Proposition 3.12, each finite target is itself a finite tell-tale.  Both
results expose reusable relationships with Angluin's condition without
claiming the source propositions.
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

end GenLimit.HallucinationModeCollapse
