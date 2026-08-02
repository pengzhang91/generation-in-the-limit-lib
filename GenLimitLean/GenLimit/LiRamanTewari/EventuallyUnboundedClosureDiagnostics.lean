import GenLimit.LiRamanTewari.EventuallyUnboundedClosure

/-!
# Diagnostics for Appendix C.2

The proof of Theorem C.2 in arXiv:2410.13714v5 claims that Definition C.1 is
equivalent to a property of every arbitrary stream.  This file gives a
kernel-checked counterexample to that equivalence.  It also formalizes the
valid closure generator for a class satisfying Definition C.1 itself.
-/

namespace GenLimit.LiRamanTewari

/-- The stronger stream property used (but not assumed) in the printed proof
of Theorem C.2. -/
def StreamwiseEventuallyUnboundedClosure
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ stream : GenLimit.Generic.Stream α,
    ∃ t,
      ¬(versionSpace H (GenLimit.Generic.sample stream t)).Nonempty ∨
        (commonCore H (GenLimit.Generic.sample stream t)).Infinite

private noncomputable def diagnosticFreshFromCore
    (C : Set α) (hC : C.Infinite) (S : Finset α) : α :=
  Classical.choose (hC.diff S.finite_toSet).nonempty

private theorem diagnosticFreshFromCore_mem
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    diagnosticFreshFromCore C hC S ∈ C :=
  (Classical.choose_spec (hC.diff S.finite_toSet).nonempty).1

private theorem diagnosticFreshFromCore_not_mem
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    diagnosticFreshFromCore C hC S ∉ S :=
  (Classical.choose_spec (hC.diff S.finite_toSet).nonempty).2

private noncomputable def eucClosureGenerator [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α) :
    GenLimit.Generic.Generator α := by
  classical
  exact fun _ xs ↦
    let S := GenLimit.Generic.sequenceSample xs
    if hVS : (versionSpace H S).Nonempty then
      if hInf : (commonCore H S).Infinite then
        diagnosticFreshFromCore (commonCore H S) hInf S
      else Classical.choice inferInstance
    else Classical.choice inferInstance

/-- The valid assertion immediately following Definition C.1: EUC for the
whole class is sufficient for generation in the limit. -/
theorem eventuallyUnboundedClosure_implies_generatable_in_limit
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hEUC : EventuallyUnboundedClosure H) :
    GeneratableInLimit H := by
  classical
  let gen := eucClosureGenerator H
  refine ⟨gen, ?_⟩
  intro L hLH stream hPresentation
  obtain ⟨T, hcoreT⟩ := hEUC L hLH stream hPresentation
  refine ⟨T, ?_⟩
  intro t hTt
  have hsampleMono :
      GenLimit.Generic.sample stream T ⊆
        GenLimit.Generic.sample stream t :=
    GenLimit.Generic.sample_mono hTt
  have hcore :
      (commonCore H (GenLimit.Generic.sample stream t)).Infinite :=
    commonCore_infinite_mono_sample hsampleMono hcoreT
  have hVS :
      (versionSpace H (GenLimit.Generic.sample stream t)).Nonempty :=
    ⟨L, hLH, sample_subset_of_streamIn
      (GenLimit.Generic.streamIn_of_presents hPresentation) t⟩
  have hchosen :
      GenLimit.Generic.output gen stream t ∈
          commonCore H (GenLimit.Generic.sample stream t) ∧
        GenLimit.Generic.output gen stream t ∉
          GenLimit.Generic.sample stream t := by
    unfold GenLimit.Generic.output gen eucClosureGenerator
    simp only [GenLimit.Generic.sequenceSample_prefix, dif_pos hVS,
      dif_pos hcore]
    exact ⟨diagnosticFreshFromCore_mem _ _ _,
      diagnosticFreshFromCore_not_mem _ _ _⟩
  exact ⟨hchosen.1 L ⟨hLH, sample_subset_of_streamIn
    (GenLimit.Generic.streamIn_of_presents hPresentation) t⟩,
    hchosen.2⟩

/-- Spine points are on the left; the tail point `(n,k)` is on the right. -/
abbrev SpineTailUniverse := ℕ ⊕ (ℕ × ℕ)

/-- `L_n = {a_i : i < n} ∪ T_n`. -/
def spineTailLanguage (n : ℕ) : GenLimit.Generic.Language SpineTailUniverse :=
  {x | match x with
    | Sum.inl i => i < n
    | Sum.inr p => p.1 = n}

def spineTailClass : GenLimit.Generic.LanguageClass SpineTailUniverse :=
  Set.range spineTailLanguage

theorem spineTailLanguage_infinite (n : ℕ) :
    (spineTailLanguage n).Infinite := by
  let f : ℕ → SpineTailUniverse := fun k ↦ Sum.inr (n, k)
  have hf : Function.Injective f := by
    intro a b hab
    exact congrArg (fun x : SpineTailUniverse ↦
      match x with
      | Sum.inl _ => 0
      | Sum.inr p => p.2) hab
  apply (Set.infinite_range_of_injective hf).mono
  rintro x ⟨k, rfl⟩
  simp [spineTailLanguage, f]

theorem spineTailClass_uus : UUS spineTailClass := by
  rintro L ⟨n, rfl⟩
  exact spineTailLanguage_infinite n

private theorem tail_mem_language_iff {n m k : ℕ} :
    (Sum.inr (n, k) : SpineTailUniverse) ∈ spineTailLanguage m ↔
      n = m := by
  rfl

private theorem spine_mem_language_iff {i n : ℕ} :
    (Sum.inl i : SpineTailUniverse) ∈ spineTailLanguage n ↔
      i < n := by
  rfl

theorem spineTailClass_eventuallyUnboundedClosure :
    EventuallyUnboundedClosure spineTailClass := by
  intro L hL stream hPresentation
  obtain ⟨n, rfl⟩ := hL
  have htail :
      (Sum.inr (n, 0) : SpineTailUniverse) ∈
        spineTailLanguage n := by
    rfl
  rw [← hPresentation] at htail
  obtain ⟨k, hk⟩ := htail
  let t := k + 1
  have htailSample :
      (Sum.inr (n, 0) : SpineTailUniverse) ∈
        GenLimit.Generic.sample stream t := by
    apply GenLimit.Generic.mem_sample_iff.mpr
    exact ⟨k, Nat.lt_succ_self k, hk⟩
  have hversionSingleton :
      ∀ K, K ∈ versionSpace spineTailClass
          (GenLimit.Generic.sample stream t) →
        K = spineTailLanguage n := by
    intro K hK
    obtain ⟨m, rfl⟩ := hK.1
    have hm := hK.2 htailSample
    rw [tail_mem_language_iff] at hm
    subst m
    rfl
  have hsubset :
      spineTailLanguage n ⊆
        commonCore spineTailClass
          (GenLimit.Generic.sample stream t) := by
    intro x hx K hK
    rw [hversionSingleton K hK]
    exact hx
  exact ⟨t, (spineTailLanguage_infinite n).mono hsubset⟩

/-- The arbitrary spine stream from the counterexample. -/
def spineStream : GenLimit.Generic.Stream SpineTailUniverse :=
  fun n ↦ Sum.inl n

private theorem spine_sample_subset_language (t n : ℕ) (htn : t ≤ n) :
    (↑(GenLimit.Generic.sample spineStream t) : Set SpineTailUniverse) ⊆
      spineTailLanguage n := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := GenLimit.Generic.mem_sample_iff.mp hx
  rw [← hix]
  exact hi.trans_le htn

theorem spine_versionSpace_nonempty (t : ℕ) :
    (versionSpace spineTailClass
      (GenLimit.Generic.sample spineStream t)).Nonempty :=
  ⟨spineTailLanguage t, ⟨t, rfl⟩,
    spine_sample_subset_language t t le_rfl⟩

theorem spine_commonCore_subset_sample (t : ℕ) :
    commonCore spineTailClass
        (GenLimit.Generic.sample spineStream t) ⊆
      (↑(GenLimit.Generic.sample spineStream t) : Set SpineTailUniverse) := by
  classical
  intro x hx
  rcases x with i | p
  · have hi :
        (Sum.inl i : SpineTailUniverse) ∈ spineTailLanguage t :=
      hx (spineTailLanguage t)
        ⟨⟨t, rfl⟩, spine_sample_subset_language t t le_rfl⟩
    apply GenLimit.Generic.mem_sample_iff.mpr
    exact ⟨i, hi, rfl⟩
  · let m := max t (p.1 + 1)
    have htm : t ≤ m := Nat.le_max_left _ _
    have hpnm : p.1 ≠ m := by
      intro h
      have hle : p.1 + 1 ≤ p.1 :=
        (Nat.le_max_right t (p.1 + 1)).trans_eq h.symm
      omega
    have hp :
        (Sum.inr p : SpineTailUniverse) ∈ spineTailLanguage m :=
      hx (spineTailLanguage m)
        ⟨⟨m, rfl⟩, spine_sample_subset_language t m htm⟩
    exact False.elim (hpnm hp)

theorem spine_commonCore_finite (t : ℕ) :
    (commonCore spineTailClass
      (GenLimit.Generic.sample spineStream t)).Finite :=
  (GenLimit.Generic.sample spineStream t).finite_toSet.subset
    (spine_commonCore_subset_sample t)

theorem spineTailClass_not_streamwise_euc :
    ¬StreamwiseEventuallyUnboundedClosure spineTailClass := by
  intro hStreamwise
  obtain ⟨t, hbottom | hInfinite⟩ := hStreamwise spineStream
  · exact hbottom (spine_versionSpace_nonempty t)
  · exact hInfinite (spine_commonCore_finite t)

/-- Concrete failure of the equivalence asserted in the prose before C.2:
Definition C.1 holds, but the arbitrary-stream property does not. -/
theorem eventuallyUnboundedClosure_not_equivalent_to_streamwise :
    EventuallyUnboundedClosure spineTailClass ∧
      ¬StreamwiseEventuallyUnboundedClosure spineTailClass :=
  ⟨spineTailClass_eventuallyUnboundedClosure,
    spineTailClass_not_streamwise_euc⟩

/-- A logically explicit diagnostic: the universal equivalence printed
before Theorem C.2 is false. -/
theorem printed_EUC_equivalence_is_false :
    ¬(∀ (H : GenLimit.Generic.LanguageClass SpineTailUniverse),
      EventuallyUnboundedClosure H ↔
        StreamwiseEventuallyUnboundedClosure H) := by
  intro h
  exact spineTailClass_not_streamwise_euc
    ((h spineTailClass).mp spineTailClass_eventuallyUnboundedClosure)

end GenLimit.LiRamanTewari
