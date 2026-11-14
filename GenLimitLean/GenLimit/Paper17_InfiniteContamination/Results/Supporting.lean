import GenLimit.Paper17_InfiniteContamination.AlgorithmFour
import GenLimit.Paper17_InfiniteContamination.AlgorithmFive
import GenLimit.Paper17_InfiniteContamination.AlgorithmSixSeven
import GenLimit.Paper17_InfiniteContamination.AlgorithmEight
import GenLimit.Paper17_InfiniteContamination.AlgorithmNine
import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationNecessity
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper17_InfiniteContamination.FiniteExpansionTransfer
import GenLimit.Paper17_InfiniteContamination.ProperSeparations
import GenLimit.Paper17_InfiniteContamination.SetDensityObstruction


/-!
# Paper 17: supporting results

The set-to-element conversion, its error-allowance corollary, and the
bounded-displacement lemmas support the main theorems in `Results.Overview`.
Their existing names and statements are preserved here.
-/

namespace GenLimit.InfiniteContamination.Results

open Filter
open GenLimit.Generic
open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback

/-- Theorem 6.15: Algorithm 8 converts an eventually `ρ`-dense set
generator into a fresh element generator of lower density at least `ρ / 2`.
The ambient-order compatibility implicit in the paper is explicit here. -/
theorem theorem_6_15
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (target : ℕ) (stream : Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i))
    (hdensity : ∃ N, ∀ t, N ≤ t →
      ρ ≤ (orders target).lowerDensity (setOutput setGen stream t)) :
    GeneratesElementInLimitOn
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ)
        (family target) stream ∧
      ρ / 2 ≤ elementBasedLowerDensity
        (algorithmEightGenerator
          setGen hinfinite selection orders ρ)
        (orders target) stream :=
  GenLimit.InfiniteContamination.theorem_6_15_algorithmEight
    setGen hinfinite family selection orders ρ hρ hinvariant
    hcarrier horder target stream hselected hdensity

/-- Corollary 6.16: every positive error allowance gives an element
generator with lower density at least `(ρ - ε) / 2`. -/
theorem corollary_6_16
    (setGen : SetGenerator ℕ)
    (hinfinite : IsInfiniteSetGenerator setGen)
    (family : ℕ → Set ℕ)
    (selection : ∀ t, (Fin t → ℕ) → Finset ℕ)
    (orders : ℕ → OrderedLanguage)
    (ρ ε : ℝ) (hε : 0 < ε)
    (hinvariant : SetCoreSelectionInvariant setGen family selection)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (horder : ∀ i, InheritsAmbientOrder (orders i))
    (target : ℕ) (stream : Stream ℕ)
    (hselected : ∃ N, ∀ t, N ≤ t →
      target ∈ selection t (fun i => stream i))
    (hsetDensity : ρ ≤
      setBasedLowerDensity setGen (orders target) stream) :
    ∃ gen : Generator ℕ,
      GeneratesElementInLimitOn gen (family target) stream ∧
        (ρ - ε) / 2 ≤
          elementBasedLowerDensity gen (orders target) stream :=
  GenLimit.InfiniteContamination.corollary_6_16
    setGen hinfinite family selection orders ρ ε hε hinvariant
    hcarrier horder target stream hselected hsetDensity

/-- Proposition 7.4: a bounded-displacement guarantee is preserved when the
measured language is replaced by a subset in the same ambient ordering. -/
theorem proposition_7_4
    (K : OrderedLanguage)
    (stream : Stream ℕ)
    {L L' : Set ℕ} {M : ℝ}
    (hsub : L' ⊆ L)
    (hbounded : BoundedDisplacement K stream L M) :
    BoundedDisplacement K stream L' M :=
  GenLimit.InfiniteContamination.proposition_7_4_boundedDisplacement_subset
    K stream hsub hbounded

/-- Lemma 7.5: bounded displacement transfers empirical lower and upper
density to canonical ordered density. -/
theorem lemma_7_5
    (K : OrderedLanguage)
    (stream : Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (M : ℝ) (hM : 0 < M)
    (hbounded : BoundedDisplacement K stream K.carrier M) :
    ((1 / M) *
        liminf (empiricalTargetRatio stream L) atTop ≤
      K.lowerDensity L) ∧
    ((1 / M) *
        limsup (empiricalTargetRatio stream L) atTop ≤
      K.upperDensity L) :=
  GenLimit.InfiniteContamination.lemma_7_5_change_of_density
    K stream L hLK M hM hbounded

end GenLimit.InfiniteContamination.Results
