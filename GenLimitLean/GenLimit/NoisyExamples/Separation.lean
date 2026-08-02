import GenLimit.Core.ClosureDimension
import GenLimit.NoisyExamples.NoisyClosure
import Mathlib.Data.Set.Countable

/-!
# Raman--Raman: separation from noiseless uniform generation

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Lemma 3.5.

The printed lemma begins with an arbitrary countable example space and then
constructs a particular countably infinite space from primes and negative
prime powers.  The assertion is false on a finite example space under UUS.
We therefore state the existential separation on the concrete countably
infinite tagged space below.  `primePoint p` represents the paper's prime
`p`, while `powerPoint p n` represents `-p^n`; using tags avoids importing
irrelevant arithmetic facts about unique prime-power representations.
-/

namespace GenLimit.NoisyExamples

/-- The concrete countably infinite universe used for Lemma 3.5. -/
abbrev SeparationPoint := ℕ × Option ℕ

/-- The point representing the paper's `p`-th prime. -/
def primePoint (p : ℕ) : SeparationPoint := (p, none)

/-- The point representing the paper's negative prime power `-p^n`. -/
def powerPoint (p n : ℕ) : SeparationPoint := (p, some n)

/-- The hypothesis indexed by `p`: it omits `primePoint p` and the entire
row of `powerPoint p n`, and contains every point with a different index. -/
def separationLanguage (p : ℕ) :
    GenLimit.Generic.Language SeparationPoint :=
  {x | x.1 ≠ p}

/-- The countable class in the proof of Lemma 3.5. -/
def separationClass :
    GenLimit.Generic.LanguageClass SeparationPoint :=
  Set.range separationLanguage

theorem separationClass_countable : separationClass.Countable := by
  exact Set.countable_range separationLanguage

theorem separationLanguage_infinite (p : ℕ) :
    (separationLanguage p).Infinite := by
  let row : ℕ → SeparationPoint := fun n ↦ powerPoint (p + 1) n
  have hrow : (Set.range row).Infinite := by
    apply Set.infinite_range_of_injective
    intro m n hmn
    have hsnd := congrArg Prod.snd hmn
    simpa [row, powerPoint] using hsnd
  apply hrow.mono
  rintro _ ⟨n, rfl⟩
  simp [row, powerPoint, separationLanguage]

theorem separationClass_uus :
    GenLimit.Generic.UUS separationClass := by
  rintro L ⟨p, rfl⟩
  exact separationLanguage_infinite p

/-- Every nonempty positive sample has infinite ordinary common core. -/
theorem separation_commonCore_infinite
    (S : Finset SeparationPoint) (hS : S.Nonempty) :
    (GenLimit.Generic.commonCore separationClass S).Infinite := by
  classical
  obtain ⟨x, hxS⟩ := hS
  let row : ℕ → SeparationPoint := fun n ↦ powerPoint x.1 n
  have hrow : (Set.range row).Infinite := by
    apply Set.infinite_range_of_injective
    intro m n hmn
    have hsnd := congrArg Prod.snd hmn
    simpa [row, powerPoint] using hsnd
  apply hrow.mono
  rintro _ ⟨n, rfl⟩
  intro L hLVS
  obtain ⟨p, rfl⟩ := hLVS.1
  have hxPositive : x ∈ separationLanguage p := hLVS.2 hxS
  exact hxPositive

/-- The class has ordinary Closure dimension zero, the first half of
Lemma 3.5. -/
theorem separation_hasClosureDimension_zero :
    GenLimit.Generic.HasClosureDimension separationClass 0 := by
  constructor
  · intro S hcard _hVS
    apply separation_commonCore_infinite S
    exact Finset.card_pos.mp hcard
  · exact Or.inl rfl

/-- The first `d` prime tags, used as the noisy-closure witness. -/
noncomputable def separationPrimeSample (d : ℕ) :
    Finset SeparationPoint :=
  GenLimit.Generic.sequenceSample
    (fun i : Fin d ↦ primePoint i)

theorem separationPrimeSample_card (d : ℕ) :
    (separationPrimeSample d).card = d := by
  apply sequenceSample_card_of_injective
  intro i j hij
  apply Fin.ext
  exact congrArg Prod.fst hij

private theorem separationPrimeSample_negativePart_card_le_one
    (d p : ℕ) :
    (negativePart (separationPrimeSample d)
      (separationLanguage p)).card ≤ 1 := by
  classical
  have hsub :
      negativePart (separationPrimeSample d) (separationLanguage p) ⊆
        {primePoint p} := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨i, hix⟩ :=
      GenLimit.Generic.mem_sequenceSample_iff.mp hx'.1
    have hlabel : x.1 = p := by
      simpa [separationLanguage] using hx'.2
    have hip : (i : ℕ) = p := by
      rw [← hlabel, ← hix]
      rfl
    subst p
    rw [← hix]
    simp [primePoint]
  exact (Finset.card_le_card hsub).trans (by simp)

/-- Every member of the separating class belongs to the one-noisy version
space of the prime sample. -/
theorem separationLanguage_mem_oneNoisyVersionSpace
    (d p : ℕ) :
    separationLanguage p ∈
      noisyVersionSpace separationClass (separationPrimeSample d) 1 := by
  classical
  constructor
  · exact ⟨p, rfl⟩
  · have hsplit :
        (positivePart (separationPrimeSample d) (separationLanguage p)).card +
            (negativePart
              (separationPrimeSample d) (separationLanguage p)).card =
          (separationPrimeSample d).card := by
      simpa [positivePart, negativePart] using
        (separationPrimeSample d).filter_card_add_filter_neg_card_eq_card
          (fun x ↦ x ∈ separationLanguage p)
    have hbad :=
      separationPrimeSample_negativePart_card_le_one d p
    omega

/-- The one-noisy version space at the prime sample is the whole class. -/
theorem separation_oneNoisyVersionSpace_eq (d : ℕ) :
    noisyVersionSpace separationClass (separationPrimeSample d) 1 =
      separationClass := by
  ext L
  constructor
  · exact fun hL ↦ hL.1
  · rintro ⟨p, rfl⟩
    exact separationLanguage_mem_oneNoisyVersionSpace d p

/-- The common core of that one-noisy version space is empty. -/
theorem separation_oneNoisyCommonCore_eq_empty (d : ℕ) :
    noisyCommonCore separationClass (separationPrimeSample d) 1 = ∅ := by
  ext x
  constructor
  · intro hx
    have hmem :=
      hx (separationLanguage x.1)
        (separationLanguage_mem_oneNoisyVersionSpace d x.1)
    exact False.elim (hmem rfl)
  · simp

/-- At noise level one there is a noisy-closure witness of every exact
finite cardinality.  This is the paper's assertion `NC₁(H) = ∞`. -/
theorem separation_oneNoisyWitness_every_card (d : ℕ) :
    NoisyClosureWitnessAt separationClass 1 d := by
  refine ⟨separationPrimeSample d, separationPrimeSample_card d, ?_, ?_⟩
  · exact ⟨separationLanguage 0,
      separationLanguage_mem_oneNoisyVersionSpace d 0⟩
  · rw [separation_oneNoisyCommonCore_eq_empty]
    exact Set.finite_empty

/-- Exact proposition-level encoding of `NC_n(H) = ∞`: witnesses occur at
every finite cardinality. -/
def InfiniteNoisyClosureDimensionAt
    (H : GenLimit.Generic.LanguageClass α) (n : ℕ) : Prop :=
  ∀ d : ℕ, NoisyClosureWitnessAt H n d

/-- The named class has all four properties required by Lemma 3.5. -/
theorem separationClass_properties :
    separationClass.Countable ∧
      GenLimit.Generic.UUS separationClass ∧
      GenLimit.Generic.HasClosureDimension separationClass 0 ∧
      InfiniteNoisyClosureDimensionAt separationClass 1 := by
  exact ⟨separationClass_countable, separationClass_uus,
    separation_hasClosureDimension_zero,
    separation_oneNoisyWitness_every_card⟩

/-- Lemma 3.5, corrected to the concrete countably infinite universe used by
its proof.  There exists a countable UUS class with ordinary Closure
dimension zero and infinite one-noisy Closure dimension. -/
theorem lemma_3_5 :
    ∃ H : GenLimit.Generic.LanguageClass SeparationPoint,
      H.Countable ∧
      GenLimit.Generic.UUS H ∧
      GenLimit.Generic.HasClosureDimension H 0 ∧
      InfiniteNoisyClosureDimensionAt H 1 :=
  ⟨separationClass, separationClass_properties⟩

/-- In particular, the class is not uniformly noise-dependent generatable,
making the separation in Lemma 3.5 explicit at the generation level. -/
theorem separation_not_uniform_noiseDependent :
    ¬UniformNoiseDependentGeneratable separationClass := by
  intro hgen
  have hfinite :=
    uniform_noiseDependent_implies_finite_noisyClosureDimensions
      separationClass_uus hgen 1
  obtain ⟨D, hD⟩ := hfinite
  exact hD (D + 1) (Nat.lt_succ_self D)
    (separation_oneNoisyWitness_every_card (D + 1))

end GenLimit.NoisyExamples
