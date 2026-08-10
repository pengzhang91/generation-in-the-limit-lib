import GenLimit.Paper02_LearningTheory.PromptedNonuniform

/-!
# The infinite-prompt separation

This file formalizes Lemma 5.4 and Corollary 5.5.  The source realizes the
construction inside `ℤ` using triangular positive blocks and disjoint
prime-power tails.  We use the isomorphic tagged presentation: a finite
common block of size `n`, and two disjoint countably infinite tails for each
positive prompt `n`.  This removes irrelevant prime arithmetic while
preserving the two hypotheses and every prompted support and closure used in
the proof.
-/

namespace GenLimit.LiRamanTewari

/-- The paper uses positive natural-number prompts. -/
abbrev PositivePrompt := {n : ℕ // 0 < n}

def firstPositivePrompt : PositivePrompt := ⟨1, by omega⟩

/-- A tagged version of the paper's integer universe.  `none` marks the
finite common block; the two Boolean tags mark the disjoint infinite tails. -/
abbrev PromptSeparationUniverse :=
  PositivePrompt × Option Bool × ℕ

def promptSeparationLeft :
    MulticlassHypothesis PromptSeparationUniverse PositivePrompt :=
  fun x ↦
    match x.2.1 with
    | none =>
        if x.2.2 < x.1.1 then x.1 else firstPositivePrompt
    | some false => x.1
    | some true => firstPositivePrompt

def promptSeparationRight :
    MulticlassHypothesis PromptSeparationUniverse PositivePrompt :=
  fun x ↦
    match x.2.1 with
    | none =>
        if x.2.2 < x.1.1 then x.1 else firstPositivePrompt
    | some false => firstPositivePrompt
    | some true => x.1

def promptSeparationClass :
    MulticlassHypothesisClass PromptSeparationUniverse PositivePrompt :=
  {promptSeparationLeft, promptSeparationRight}

/-- The finite block `A_n` from Lemma 5.4. -/
noncomputable def promptBlock (p : PositivePrompt) :
    Finset PromptSeparationUniverse := by
  classical
  exact (Finset.range p.1).image (fun k ↦ (p, none, k))

theorem promptBlock_card (p : PositivePrompt) :
    (promptBlock p).card = p.1 := by
  classical
  rw [promptBlock, Finset.card_image_of_injective]
  · exact Finset.card_range p.1
  · intro a b hab
    exact congrArg (fun x : PromptSeparationUniverse ↦ x.2.2) hab

theorem promptSeparationLeft_block
    (p : PositivePrompt) {x : PromptSeparationUniverse}
    (hx : x ∈ promptBlock p) :
    promptSeparationLeft x = p := by
  classical
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hkp : k < p.1 := Finset.mem_range.mp hk
  simp [promptSeparationLeft, hkp]

theorem promptSeparationRight_block
    (p : PositivePrompt) {x : PromptSeparationUniverse}
    (hx : x ∈ promptBlock p) :
    promptSeparationRight x = p := by
  classical
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hkp : k < p.1 := Finset.mem_range.mp hk
  simp [promptSeparationRight, hkp]

theorem promptSeparationClass_finite :
    promptSeparationClass.Finite := by
  simp [promptSeparationClass]

theorem promptSeparationClass_puus :
    PUUS promptSeparationClass := by
  intro h hh p
  simp only [promptSeparationClass, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hh
  rcases hh with rfl | rfl
  · let f : ℕ → PromptSeparationUniverse :=
      fun k ↦ (p, some false, k)
    have hf : Function.Injective f := by
      intro a b hab
      exact congrArg
        (fun x : PromptSeparationUniverse ↦ x.2.2) hab
    apply (Set.infinite_range_of_injective hf).mono
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    simp [promptSupport, promptSeparationLeft, f]
  · let f : ℕ → PromptSeparationUniverse :=
      fun k ↦ (p, some true, k)
    have hf : Function.Injective f := by
      intro a b hab
      exact congrArg
        (fun x : PromptSeparationUniverse ↦ x.2.2) hab
    apply (Set.infinite_range_of_injective hf).mono
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    simp [promptSupport, promptSeparationRight, f]

private theorem prompt_left_mem_class :
    promptSeparationLeft ∈ promptSeparationClass := by
  simp [promptSeparationClass]

private theorem prompt_right_mem_class :
    promptSeparationRight ∈ promptSeparationClass := by
  simp [promptSeparationClass]

theorem promptBlock_versionSpace_nonempty (p : PositivePrompt) :
    (promptedVersionSpace promptSeparationClass (promptBlock p) p).Nonempty := by
  refine ⟨promptSeparationLeft, prompt_left_mem_class, ?_⟩
  intro x hx
  exact promptSeparationLeft_block p hx

theorem promptedCommonCore_promptBlock_subset
    (p : PositivePrompt) (hp : p ≠ firstPositivePrompt) :
    promptedCommonCore promptSeparationClass (promptBlock p) p ⊆
      (↑(promptBlock p) : Set PromptSeparationUniverse) := by
  classical
  intro x hx
  have hleft : promptSeparationLeft x = p :=
    hx promptSeparationLeft
      ⟨prompt_left_mem_class, fun z hz ↦
        promptSeparationLeft_block p hz⟩
  have hright : promptSeparationRight x = p :=
    hx promptSeparationRight
      ⟨prompt_right_mem_class, fun z hz ↦
        promptSeparationRight_block p hz⟩
  rcases x with ⟨q, mode, k⟩
  rcases mode with _ | b
  · by_cases hk : k < q.1
    · have hqp : q = p := by
        simpa [promptSeparationLeft, hk] using hleft
      subst q
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_range.mpr hk, rfl⟩
    · have hfirst : firstPositivePrompt = p := by
        simpa [promptSeparationLeft, hk] using hleft
      exact False.elim (hp hfirst.symm)
  · cases b with
    | false =>
        have hfirst : firstPositivePrompt = p := by
          simpa [promptSeparationRight] using hright
        exact False.elim (hp hfirst.symm)
    | true =>
        have hfirst : firstPositivePrompt = p := by
          simpa [promptSeparationLeft] using hleft
        exact False.elim (hp hfirst.symm)

theorem promptSeparationClass_infinite_prompted_closure_dimension :
    HasInfinitePromptedClosureDimension promptSeparationClass := by
  intro d
  let p : PositivePrompt := ⟨d + 2, by omega⟩
  have hp : p ≠ firstPositivePrompt := by
    intro h
    have := congrArg Subtype.val h
    change d + 2 = 1 at this
    omega
  refine ⟨p, promptBlock p, ?_, ?_⟩
  · rw [promptBlock_card]
    change d ≤ d + 2
    omega
  · constructor
    · exact promptBlock_versionSpace_nonempty p
    · exact (promptBlock p).finite_toSet.subset
        (promptedCommonCore_promptBlock_subset p hp)

/-- Lemma 5.4. -/
theorem exists_finite_prompt_class_not_uniformly_generatable :
    ∃ H :
        MulticlassHypothesisClass
          PromptSeparationUniverse PositivePrompt,
      H.Finite ∧ PUUS H ∧ ¬PromptedUniformlyGeneratable H := by
  refine ⟨promptSeparationClass, promptSeparationClass_finite,
    promptSeparationClass_puus, ?_⟩
  exact prompted_closure_dimension_necessity
    promptSeparationClass_puus
    promptSeparationClass_infinite_prompted_closure_dimension

theorem promptSeparationClass_not_nonuniformly_generatable :
    ¬PromptedNonuniformlyGeneratable promptSeparationClass := by
  intro hNonuniform
  obtain ⟨classes, hcover, hfinite⟩ :=
    (prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover
      promptSeparationClass_puus).mp hNonuniform
  have hleftUnion :
      promptSeparationLeft ∈ ⋃ n, classes n := by
    rw [← hcover.2]
    exact prompt_left_mem_class
  have hrightUnion :
      promptSeparationRight ∈ ⋃ n, classes n := by
    rw [← hcover.2]
    exact prompt_right_mem_class
  obtain ⟨i, hlefti⟩ := Set.mem_iUnion.mp hleftUnion
  obtain ⟨j, hrightj⟩ := Set.mem_iUnion.mp hrightUnion
  let n := max i j
  have hleftn : promptSeparationLeft ∈ classes n :=
    hcover.1 (Nat.le_max_left i j) hlefti
  have hrightn : promptSeparationRight ∈ classes n :=
    hcover.1 (Nat.le_max_right i j) hrightj
  have hclassEq : classes n = promptSeparationClass := by
    apply Set.Subset.antisymm
    · intro h hhn
      rw [hcover.2]
      exact Set.mem_iUnion.mpr ⟨n, hhn⟩
    · intro h hh
      simp only [promptSeparationClass, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · exact hleftn
      · exact hrightn
  have hfiniteClass := hfinite n
  rw [hclassEq] at hfiniteClass
  exact
    (finite_prompted_closure_dimension_iff_not_infinite.mp hfiniteClass)
      promptSeparationClass_infinite_prompted_closure_dimension

/-- Corollary 5.5. -/
theorem exists_finite_prompt_class_not_nonuniformly_generatable :
    ∃ H :
        MulticlassHypothesisClass
          PromptSeparationUniverse PositivePrompt,
      H.Finite ∧ PUUS H ∧ ¬PromptedNonuniformlyGeneratable H :=
  ⟨promptSeparationClass, promptSeparationClass_finite,
    promptSeparationClass_puus,
    promptSeparationClass_not_nonuniformly_generatable⟩

end GenLimit.LiRamanTewari
