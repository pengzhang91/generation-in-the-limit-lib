import GenLimit.Paper28_ContrastiveGeneration.UnorderedStrategies
import GenLimit.Paper28_ContrastiveGeneration.CleanHierarchy
import GenLimit.Paper28_ContrastiveGeneration.InfiniteDefect
import GenLimit.Paper28_ContrastiveGeneration.IdentifierCharacterization
import GenLimit.Paper28_ContrastiveGeneration.GenerationCores
import GenLimit.Paper28_ContrastiveGeneration.ClosureDimension
import GenLimit.Paper28_ContrastiveGeneration.NonuniformClosure
import GenLimit.Paper28_ContrastiveGeneration.Hierarchy
import GenLimit.Paper28_ContrastiveGeneration.DisjointHierarchy
import GenLimit.Paper28_ContrastiveGeneration.CorruptedPresentations
import GenLimit.Paper28_ContrastiveGeneration.AbsenceCount
import GenLimit.Paper28_ContrastiveGeneration.CorruptedIncomparability
import GenLimit.Paper28_ContrastiveGeneration.DefectInfimum

/-!
# Paper 28: main-results overview

This is the public results facade for Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*. Each result gives
its statement and refers to the proof in the corresponding P28 module.

The named regimes of Theorem 4.3, the strict diamond of Theorem 5.13 and
the general finite-corruption implication are exposed below.
-/

namespace GenLimit.ContrastiveGeneration.Results

/-- Section 1.1, result (4), for every finite corruption budget. -/
theorem infinite_defect_identification (F : Generic.LanguageFamily α)
    (gap : ∀ i j, F i ≠ F j → defectNumber (F i) (F j) = ⊤) :
    FinitelyCorruptionContrastivelyIdentifiable F :=
  finiteCorruption_of_infinite_defects F gap

/-- Proposition 4.2 characterizes non-eliminability by coverage of the target. -/
theorem proposition_4_2 {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) (henum : h ⊆ Set.range enumeration) :
    NotEliminableFrom g h ↔ h ⊆ commonVertices h g :=
  GenLimit.ContrastiveGeneration.proposition_4_2 x₀ hx₀ enumeration henum

/-- Theorem 4.3. The four-region test characterizes common-vertex coverage for any
two supports. On a countable space, the three regimes N1, N2 and N3 characterize
non-eliminability when the supports are distinct, `h` is nonempty and `g` is proper. -/
theorem theorem_4_3 (h g : Set α) :
    (h ⊆ commonVertices h g ↔
      ((bothPositive h g).Nonempty → (bothNegative h g).Nonempty) ∧
      ((hOnly h g).Nonempty → (gOnly h g).Nonempty)) ∧
    (∀ [Countable α], h.Nonempty → gᶜ.Nonempty → h ≠ g →
      (NotEliminableFrom g h ↔ h ⊂ g ∨
        (Incomparable h g ∧ Disjoint h g) ∨
        (Incomparable h g ∧ (h ∩ g).Nonempty ∧ h ∪ g ≠ Set.univ))) :=
  ⟨GenLimit.ContrastiveGeneration.theorem_4_3 h g, fun [_] => noneliminability_regimes⟩

/-- Theorem 4.7 characterizes contrastive identification by text identification
and overlap of incomparable pairs. -/
theorem theorem_4_7 [Nonempty α] [Countable α] [Infinite α]
    (F : Generic.LanguageFamily α) (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧ IncomparablePairsOverlap (Set.range F) :=
  GenLimit.ContrastiveGeneration.theorem_4_7 F hproper

/-- Theorem 5.4. Uniform contrastive generation is possible exactly when the contrastive
closure dimension is finite. At exact dimension `d`, the least positive threshold is
`d + 1` distinct unordered edges. -/
theorem theorem_5_4 [Nonempty α] (𝓗 : Set (Set α)) :
    (UniformlyContrastivelyGeneratable 𝓗 ↔ FiniteContrastiveClosureDimension 𝓗) ∧
      ∀ d : ℕ, ContrastiveClosureDimensionEquals 𝓗 d →
        IsLeastPositiveUniformThreshold 𝓗 (d + 1) :=
  ⟨GenLimit.ContrastiveGeneration.theorem_5_4 𝓗,
    fun _ hdim => GenLimit.ContrastiveGeneration.theorem_5_4_sharp_sample_complexity hdim⟩

/-- Theorem 5.5 characterizes nonuniform generation by an increasing cover
of classes of finite contrastive closure dimension. -/
theorem theorem_5_5 [Nonempty α] (𝓗 : Set (Set α)) :
    NonuniformlyContrastivelyGeneratable 𝓗 ↔
      ∃ classes : ℕ → Set (Set α),
        Generic.IsNondecreasingCover 𝓗 classes ∧
        ∀ n, FiniteContrastiveClosureDimension (classes n) :=
  GenLimit.ContrastiveGeneration.theorem_5_5 𝓗

/-- Proposition 5.8 gives generation from infinite safe cores. -/
theorem proposition_5_8 [Nonempty α] (𝓗 : Set (Set α)) (hsafe : InfiniteSafeCores 𝓗) :
    ContrastivelyGeneratable 𝓗 :=
  GenLimit.ContrastiveGeneration.proposition_5_8 𝓗 hsafe

/-- Proposition 5.11 gives generation from an eventual core. -/
theorem proposition_5_11 (𝓗 : Set (Set α)) (core : ℕ → α) (hcore : IsEventualCore 𝓗 core) :
    ContrastivelyGeneratable 𝓗 :=
  GenLimit.ContrastiveGeneration.proposition_5_11 𝓗 core hcore

/-- Proposition 5.12 rules out generation when a finite subfamily with finite
intersection admits a shared presentation. -/
theorem proposition_5_12 {𝓗 : Set (Set α)} {family : Finset (Set α)}
    {core : Finset α} {stream : ℕ → Edge α}
    (hfamilyNonempty : family.Nonempty) (hfamilyClass : ∀ h, h ∈ family → h ∈ 𝓗)
    (hshared : IsSharedPresentation stream family)
    (hcore : IsFiniteFamilyIntersection family core) :
    ¬ContrastivelyGeneratable 𝓗 :=
  GenLimit.ContrastiveGeneration.proposition_5_12 hfamilyNonempty hfamilyClass hshared hcore

/-- Theorem 5.13. On countable classes of infinite proper supports, the punctured and
disjoint families witness the four strict inclusions below. -/
theorem theorem_5_13 :
    let CI := cleanFamilies ContrastivelyIdentifiable
    let TI := cleanFamilies TextIdentifiable
    let CG := cleanFamilies (fun F => ContrastivelyGeneratable (Set.range F))
    let TG := cleanFamilies (fun F => Generic.GeneratableInLimit (Set.range F))
    CI ⊂ CG ∧ CG ⊂ TG ∧ CI ⊂ TI ∧ TI ⊂ TG :=
  clean_strict_diamond

/-- Theorem 5.14. The punctured family witnesses contrastive generation without text
identification, and the disjoint family witnesses text identification without contrastive
generation. -/
theorem theorem_5_14 :
    let CG := cleanFamilies (fun F => ContrastivelyGeneratable (Set.range F))
    let TI := cleanFamilies TextIdentifiable
    ¬ (CG ⊆ TI) ∧ ¬ (TI ⊆ CG) :=
  clean_generation_text_identification_incomparable

/-- Proposition 6.3. The defect number equals the infimum of wrong-cut violations
over clean presentations. Zero defect characterizes non-eliminability. -/
theorem proposition_6_3 [Countable α] {h g : Set α}
    (hne : h ≠ g) (hh : ProperNontrivialSupport h) (hg : ProperNontrivialSupport g) :
    forcedWrongCutViolationInfimum h g = defectNumber h g ∧
      (NotEliminableFrom g h ↔ defectNumber h g = 0) :=
  ⟨proposition_6_3_defect_eq_forced_wrong_cut_infimum hne hh hg,
    proposition_6_3_notEliminable_iff_defectNumber_zero hne hh hg⟩

/-- Theorem 6.5 rules out text identification of the co-singleton family with one corruption. -/
theorem theorem_6_5 : ¬KTextIdentifiable 1 coSingletonFamily :=
  GenLimit.ContrastiveGeneration.theorem_6_5

/-- Theorem 6.6 gives one contrastive identifier for the co-singleton family
that works for every finite corruption budget. -/
theorem theorem_6_6 : FinitelyCorruptionContrastivelyIdentifiable coSingletonFamily :=
  GenLimit.ContrastiveGeneration.theorem_6_6

/-- Theorem 6.8 separates corrupted text and contrastive identification in both directions. -/
theorem theorem_6_8 (k : ℕ) (hk : 1 ≤ k) :
    (KContrastivelyIdentifiable k coSingletonFamily ∧ ¬KTextIdentifiable k coSingletonFamily) ∧
    (KTextIdentifiable k (robustBlockFamily k) ∧
      ¬KContrastivelyIdentifiable k (robustBlockFamily k)) :=
  GenLimit.ContrastiveGeneration.theorem_6_8 k hk

end GenLimit.ContrastiveGeneration.Results
