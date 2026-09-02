import GenLimit.Paper17_InfiniteContamination.VanishingNoise

/-!
# Constant-noise generation: necessity

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, necessity direction of Theorem 5.4.

This is the paper's full finite-common-core obstruction.  In particular, the
proof uses the literal element-generator rule that every late output avoids
both the input sample and **all previous generator outputs**.  Merely proving
membership in the common core would not suffice: the freshness rule is what
forces infinitely many distinct elements in that core.

The source states its condition as an alternative: for every finite
subcollection and common stream, either one language's noise rate exceeds
`c` infinitely often or the common intersection is infinite.  The definition
below uses the logically equivalent implication form on streams that satisfy
the paper's `c`-noise and arbitrary-omission enumeration predicate for every
member of the finite subcollection.
-/

namespace GenLimit.InfiniteContamination

/-! ## A finite family shares one eventual threshold -/

theorem eventually_correct_on_finite_family
    (gen : GenLimit.Generic.Generator α)
    (stream : GenLimit.Generic.Stream α)
    (S : Finset (GenLimit.Generic.Language α))
    (hgen :
      ∀ L, L ∈ S → GeneratesElementInLimitOn gen L stream) :
    ∃ T, ∀ L, L ∈ S → ∀ t, T ≤ t →
      FreshElementCorrectAt gen L stream t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert L S hLS ih =>
      obtain ⟨TL, hTL⟩ := hgen L (Finset.mem_insert_self L S)
      obtain ⟨TS, hTS⟩ := ih (by
        intro K hKS
        exact hgen K (Finset.mem_insert_of_mem hKS))
      refine ⟨max TL TS, ?_⟩
      intro K hK t ht
      rcases Finset.mem_insert.mp hK with rfl | hKS
      · exact hTL t ((Nat.le_max_left _ _).trans ht)
      · exact hTS K hKS t ((Nat.le_max_right _ _).trans ht)

/-! ## Fresh simultaneous generation forces an infinite common core -/

/-- The semantic heart of the necessity proof: if one run eventually
generates correctly and freshly for every member of a nonempty finite
family, then that family's common intersection is infinite. -/
theorem simultaneous_fresh_generation_infinite_core
    (gen : GenLimit.Generic.Generator α)
    (stream : GenLimit.Generic.Stream α)
    (S : Finset (GenLimit.Generic.Language α))
    (hS : S.Nonempty)
    (hgen :
      ∀ L, L ∈ S → GeneratesElementInLimitOn gen L stream) :
    (finiteCommonCore S).Infinite := by
  classical
  obtain ⟨T, hT⟩ :=
    eventually_correct_on_finite_family gen stream S hgen
  obtain ⟨L₀, hL₀S⟩ := hS
  let tailOutput : ℕ → α :=
    fun n => GenLimit.Generic.output gen stream (T + n)
  have htailMem : Set.range tailOutput ⊆ finiteCommonCore S := by
    rintro x ⟨n, rfl⟩
    intro L hLS
    exact (hT L hLS (T + n) (Nat.le_add_right T n)).1
  have htailInjective : Function.Injective tailOutput := by
    intro m n hmn
    by_contra hne
    rcases lt_or_gt_of_ne hne with hmnlt | hmnlt
    · have hfresh :=
        (hT L₀ hL₀S (T + n) (Nat.le_add_right T n)).2.2
      apply hfresh
      apply mem_generatedBefore_iff.mpr
      refine ⟨T + m, by omega, ?_⟩
      exact hmn
    · have hfresh :=
        (hT L₀ hL₀S (T + m) (Nat.le_add_right T m)).2.2
      apply hfresh
      apply mem_generatedBefore_iff.mpr
      refine ⟨T + n, by omega, ?_⟩
      exact hmn.symm
  exact (Set.infinite_range_of_injective htailInjective).mono htailMem

/-- Contrapositive form, useful for recording source-side obstructions. -/
theorem finite_core_precludes_simultaneous_fresh_generation
    (gen : GenLimit.Generic.Generator α)
    (stream : GenLimit.Generic.Stream α)
    (S : Finset (GenLimit.Generic.Language α))
    (hS : S.Nonempty)
    (hcore : (finiteCommonCore S).Finite) :
    ¬(∀ L, L ∈ S → GeneratesElementInLimitOn gen L stream) := by
  intro hgen
  exact simultaneous_fresh_generation_infinite_core
    gen stream S hS hgen hcore

/-! ## Theorem 5.4 -/

/-- A fixed generator succeeds on the paper's constant-noise,
arbitrary-omission adversaries. -/
def GeneratesUnderConstantNoise
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) (c : ℝ) : Prop :=
  ∀ L, L ∈ C → ∀ stream,
    ConstantNoiseArbitraryOmissionEnumeration stream L c →
      GeneratesElementInLimitOn gen L stream

/-- The `c`-constant-noise generation property in Theorem 5.4, in
implication form. -/
def ConstantNoiseGenerationProperty
    (C : GenLimit.Generic.LanguageClass α) (c : ℝ) : Prop :=
  ∀ S : Finset (GenLimit.Generic.Language α),
    S.Nonempty → (↑S : Set (GenLimit.Generic.Language α)) ⊆ C →
      ∀ stream,
        (∀ L, L ∈ S →
          ConstantNoiseArbitraryOmissionEnumeration stream L c) →
        (finiteCommonCore S).Infinite

/-- Necessity in Theorem 5.4.  The proof is fully semantic and includes the
paper's actual freshness requirement. -/
theorem theorem_5_4_necessity
    {gen : GenLimit.Generic.Generator α}
    {C : GenLimit.Generic.LanguageClass α} {c : ℝ}
    (hgen : GeneratesUnderConstantNoise gen C c) :
    ConstantNoiseGenerationProperty C c := by
  intro S hS hSC stream hstream
  apply simultaneous_fresh_generation_infinite_core gen stream S hS
  intro L hLS
  exact hgen L (hSC hLS) stream (hstream L hLS)

end GenLimit.InfiniteContamination
