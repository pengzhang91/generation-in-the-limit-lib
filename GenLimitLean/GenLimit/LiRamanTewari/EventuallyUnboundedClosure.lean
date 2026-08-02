import GenLimit.LiRamanTewari.NonuniformCharacterization

/-!
# Eventually Unbounded Closure

This file formalizes Definition C.1, Lemma C.1, and Theorem C.4
(`thm:altweaksuff`) in
the appendix of Li--Raman--Tewari, *Generation through the Lens of Learning
Theory*, arXiv:2410.13714v5 / COLT 2025.

The proof follows Algorithm 1 in the pinned source.  At time `t` it considers
the first `t + 1` classes, selects the largest index whose positive version
space is nonempty and whose common core is infinite, and emits a fresh member
of that core.  Once a target-containing class has acquired infinite closure,
its index is always eligible.  Monotonicity of the cover then guarantees that
the selected class also contains the target.
-/

namespace GenLimit.LiRamanTewari

/-- Definition C.1 (Eventually Unbounded Closure, EUC). -/
def EventuallyUnboundedClosure
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream L →
      ∃ t, (commonCore H (GenLimit.Generic.sample stream t)).Infinite

theorem commonCore_mono_sample
    {H : GenLimit.Generic.LanguageClass α} {S T : Finset α}
    (hST : S ⊆ T) :
    commonCore H S ⊆ commonCore H T := by
  intro x hx L hL
  apply hx L
  exact ⟨hL.1, fun y hy ↦ hL.2 (hST hy)⟩

theorem commonCore_infinite_mono_sample
    {H : GenLimit.Generic.LanguageClass α} {S T : Finset α}
    (hST : S ⊆ T) (hInfinite : (commonCore H S).Infinite) :
    (commonCore H T).Infinite :=
  hInfinite.mono (commonCore_mono_sample hST)

/-- Finite closure dimension implies EUC.  This is the implication used in
the source to compare Theorem 3.10 with the appendix conditions. -/
theorem finite_closure_dimension_implies_eventuallyUnboundedClosure
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hFinite : HasFiniteClosureDimension H) :
    EventuallyUnboundedClosure H := by
  obtain ⟨d, hd⟩ := hFinite
  intro L hLH stream hPresentation
  obtain ⟨t, ht⟩ :=
    GenLimit.Generic.exists_sample_card_eq_of_presents_infinite
      hPresentation (hUUS L hLH) (d + 1)
  refine ⟨t, hd.1 (GenLimit.Generic.sample stream t) ?_ ?_⟩
  · omega
  · exact ⟨L, hLH, sample_subset_of_streamIn
      (GenLimit.Generic.streamIn_of_presents hPresentation) t⟩

/-- On a nonempty countable example space, uniform generatability implies
EUC via Theorem 3.3. -/
theorem uniform_implies_eventuallyUnboundedClosure
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hUniform : UniformlyGeneratable H) :
    EventuallyUnboundedClosure H :=
  finite_closure_dimension_implies_eventuallyUnboundedClosure hUUS
    ((uniform_generatability_iff_finite_closure_dimension hUUS).mp hUniform)

/-! ## Lemma C.1: EUC is not necessary for non-uniform generation -/

/-- A convenient presentation-equivalent form of the source's countable
counterexample: all cofinite subsets of `α`. -/
def cofiniteLanguageClass (α : Type*) : GenLimit.Generic.LanguageClass α :=
  {L | ∃ A : Set α, A.Finite ∧ L = Set.univ \ A}

theorem cofiniteLanguageClass_countable [Countable α] :
    (cofiniteLanguageClass α).Countable := by
  have hfinite : {A : Set α | A.Finite}.Countable :=
    Set.Countable.setOf_finite
  have himage := hfinite.image (fun A : Set α ↦ Set.univ \ A)
  apply himage.mono
  rintro L ⟨A, hA, rfl⟩
  exact ⟨A, hA, rfl⟩

theorem cofiniteLanguageClass_uus [Infinite α] :
    UUS (cofiniteLanguageClass α) := by
  intro L hL
  obtain ⟨A, hA, rfl⟩ := hL
  exact Set.infinite_univ.diff hA

theorem commonCore_cofiniteLanguageClass_eq (S : Finset α) :
    commonCore (cofiniteLanguageClass α) S = (↑S : Set α) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxS
    let L : Set α := Set.univ \ {x}
    have hLClass : L ∈ cofiniteLanguageClass α :=
      ⟨{x}, Set.finite_singleton x, rfl⟩
    have hSL : (↑S : Set α) ⊆ L := by
      intro y hy
      refine ⟨Set.mem_univ y, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hyx
      apply hxS
      rw [← hyx]
      exact hy
    have hxL := hx L ⟨hLClass, hSL⟩
    exact hxL.2 (Set.mem_singleton x)
  · exact sample_subset_commonCore

theorem cofiniteLanguageClass_not_eventuallyUnboundedClosure :
    ¬EventuallyUnboundedClosure (cofiniteLanguageClass ℕ) := by
  intro hEUC
  have hUnivClass : (Set.univ : Set ℕ) ∈ cofiniteLanguageClass ℕ := by
    refine ⟨∅, Set.finite_empty, ?_⟩
    simp
  have hIdPresentation :
      GenLimit.Generic.Presents (fun n : ℕ ↦ n) (Set.univ : Set ℕ) := by
    exact Set.range_id
  obtain ⟨t, hInfinite⟩ :=
    hEUC Set.univ hUnivClass (fun n : ℕ ↦ n) hIdPresentation
  rw [commonCore_cofiniteLanguageClass_eq] at hInfinite
  exact hInfinite (GenLimit.Generic.sample (fun n : ℕ ↦ n) t).finite_toSet

/-- Lemma C.1 (`lem:stillnotnec`), including the countability property used
by the paper to invoke Corollary 3.6. -/
theorem exists_nonuniformly_generatable_not_eventuallyUnboundedClosure :
    ∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ UUS H ∧ NonuniformlyGeneratable H ∧
        ¬EventuallyUnboundedClosure H := by
  refine ⟨cofiniteLanguageClass ℕ, cofiniteLanguageClass_countable,
    cofiniteLanguageClass_uus, ?_,
    cofiniteLanguageClass_not_eventuallyUnboundedClosure⟩
  exact countable_classes_are_nonuniformly_generatable
    cofiniteLanguageClass_uus cofiniteLanguageClass_countable

private noncomputable def eucActiveIndices
    (classes : ℕ → GenLimit.Generic.LanguageClass α)
    (S : Finset α) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t + 1)).filter (fun n ↦
    (versionSpace (classes n) S).Nonempty ∧
      (commonCore (classes n) S).Infinite)

private theorem mem_eucActiveIndices_iff
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {S : Finset α} {t n : ℕ} :
    n ∈ eucActiveIndices classes S t ↔
      n ≤ t ∧ (versionSpace (classes n) S).Nonempty ∧
        (commonCore (classes n) S).Infinite := by
  classical
  simp [eucActiveIndices, Nat.lt_add_one_iff]

private noncomputable def freshFromCore
    (C : Set α) (hC : C.Infinite) (S : Finset α) : α :=
  Classical.choose (hC.diff S.finite_toSet).nonempty

private theorem freshFromCore_mem
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    freshFromCore C hC S ∈ C :=
  (Classical.choose_spec (hC.diff S.finite_toSet).nonempty).1

private theorem freshFromCore_not_mem
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    freshFromCore C hC S ∉ S :=
  (Classical.choose_spec (hC.diff S.finite_toSet).nonempty).2

/-- Algorithm 1 in the source of Theorem C.4. -/
noncomputable def eventuallyUnboundedCoverGenerator [Nonempty α]
    (classes : ℕ → GenLimit.Generic.LanguageClass α) :
    GenLimit.Generic.Generator α := by
  classical
  exact fun t xs ↦
    let S := GenLimit.Generic.sequenceSample xs
    let active := eucActiveIndices classes S t
    if h : active.Nonempty then
      let selected := active.max' h
      freshFromCore (commonCore (classes selected) S)
        ((mem_eucActiveIndices_iff.mp (active.max'_mem h)).2.2) S
    else
      Classical.choice inferInstance

private theorem eventuallyUnboundedCoverGenerator_spec [Nonempty α]
    (classes : ℕ → GenLimit.Generic.LanguageClass α)
    {t : ℕ} (xs : Fin t → α)
    (hactive : (eucActiveIndices classes
      (GenLimit.Generic.sequenceSample xs) t).Nonempty) :
    let selected := (eucActiveIndices classes
      (GenLimit.Generic.sequenceSample xs) t).max' hactive
    eventuallyUnboundedCoverGenerator classes t xs ∈
        commonCore (classes selected) (GenLimit.Generic.sequenceSample xs) ∧
      eventuallyUnboundedCoverGenerator classes t xs ∉
        GenLimit.Generic.sequenceSample xs := by
  classical
  dsimp only
  unfold eventuallyUnboundedCoverGenerator
  simp only [dif_pos hactive]
  exact ⟨freshFromCore_mem _ _ _, freshFromCore_not_mem _ _ _⟩

/-- Theorem C.4 (`thm:altweaksuff`).

The paper assumes a countable example space and UUS.  The constructive proof
only needs a nonempty example type; countability and UUS are retained as
hypotheses in the paper-facing wrapper below. -/
theorem nondecreasing_euc_cover_implies_generatable_in_limit
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hcover : IsNondecreasingCover H classes)
    (hEUC : ∀ n, EventuallyUnboundedClosure (classes n)) :
    GeneratableInLimit H := by
  classical
  let gen := eventuallyUnboundedCoverGenerator classes
  refine ⟨gen, ?_⟩
  intro L hLH stream hPresentation
  have hLUnion : L ∈ ⋃ n, classes n := by
    rwa [← hcover.2]
  obtain ⟨targetIndex, hLTarget⟩ := Set.mem_iUnion.mp hLUnion
  obtain ⟨T, hcoreT⟩ := hEUC targetIndex L hLTarget stream hPresentation
  refine ⟨max T targetIndex, ?_⟩
  intro t ht
  have hTt : T ≤ t := (Nat.le_max_left T targetIndex).trans ht
  have hIndexT : targetIndex ≤ t :=
    (Nat.le_max_right T targetIndex).trans ht
  have hsampleMono :
      GenLimit.Generic.sample stream T ⊆ GenLimit.Generic.sample stream t :=
    GenLimit.Generic.sample_mono hTt
  have htargetCoreInfinite :
      (commonCore (classes targetIndex)
        (GenLimit.Generic.sample stream t)).Infinite :=
    commonCore_infinite_mono_sample hsampleMono hcoreT
  have htargetVS :
      (versionSpace (classes targetIndex)
        (GenLimit.Generic.sample stream t)).Nonempty :=
    ⟨L, hLTarget, sample_subset_of_streamIn
      (GenLimit.Generic.streamIn_of_presents hPresentation) t⟩
  let active := eucActiveIndices classes
    (GenLimit.Generic.sample stream t) t
  have htargetActive : targetIndex ∈ active := by
    apply mem_eucActiveIndices_iff.mpr
    exact ⟨hIndexT, htargetVS, htargetCoreInfinite⟩
  have hactive : active.Nonempty := ⟨targetIndex, htargetActive⟩
  let selected := active.max' hactive
  have hselectedActive : selected ∈ active := active.max'_mem hactive
  have htargetSelected : targetIndex ≤ selected :=
    active.le_max' targetIndex htargetActive
  have hLSelected : L ∈ classes selected :=
    hcover.1 htargetSelected hLTarget
  have hspec :
      GenLimit.Generic.output gen stream t ∈
          commonCore (classes selected) (GenLimit.Generic.sample stream t) ∧
        GenLimit.Generic.output gen stream t ∉
          GenLimit.Generic.sample stream t := by
    unfold GenLimit.Generic.output gen eventuallyUnboundedCoverGenerator
    simp only [GenLimit.Generic.sequenceSample_prefix, dif_pos hactive,
      active, selected]
    exact ⟨freshFromCore_mem _ _ _, freshFromCore_not_mem _ _ _⟩
  have houtputCore :
      GenLimit.Generic.output gen stream t ∈
        commonCore (classes selected) (GenLimit.Generic.sample stream t) :=
    hspec.1
  have houtputFresh :
      GenLimit.Generic.output gen stream t ∉
        GenLimit.Generic.sample stream t :=
    hspec.2
  have hLVersion :
      L ∈ versionSpace (classes selected)
        (GenLimit.Generic.sample stream t) :=
    ⟨hLSelected, sample_subset_of_streamIn
      (GenLimit.Generic.streamIn_of_presents hPresentation) t⟩
  exact ⟨houtputCore L hLVersion, houtputFresh⟩

/-- The paper-facing form of Theorem C.4, retaining its countability and UUS
assumptions verbatim. -/
theorem theorem_C4_eventually_unbounded_closure
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H)
    (hcover : ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
      IsNondecreasingCover H classes ∧
        ∀ n, EventuallyUnboundedClosure (classes n)) :
    GeneratableInLimit H := by
  rcases hcover with ⟨classes, hclasses, hEUC⟩
  exact nondecreasing_euc_cover_implies_generatable_in_limit hclasses hEUC

end GenLimit.LiRamanTewari
