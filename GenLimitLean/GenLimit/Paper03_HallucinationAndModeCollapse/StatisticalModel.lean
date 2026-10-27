import GenLimit.Core.Identification
import GenLimit.Core.Basic
import GenLimit.Core.GenericGeneration
import GenLimit.Support.DiscreteIID

/-!
# Discrete statistical identification

Source: Definitions 1 and 13--14 of arXiv:2411.09642v3. Samples are ordered
IID lists on the natural-number encoding of the countable domain. A valid
distribution has support exactly equal to its target. Loss compares languages,
not their possibly nonunique indices. Randomized learners are arbitrary PMF
kernels; deterministic learners embed by `PMF.pure`.

`ExponentialIdentifies` fixes the learner before quantifying over target
distributions. Its positive constants may depend on the distribution. The
semantic interfaces do not themselves certify computability. `UniversalRates`
adds admissible rate exponents and the full mathematical dichotomy;
`OracleIdentification` certifies the positive branch's oracle procedure.
-/

namespace GenLimit.HallucinationModeCollapse

noncomputable section

open GenLimit.Generic GenLimit.DiscreteIID

/-- Full support, rather than merely having no mass outside the target. -/
def ValidDistribution (C : Generic.LanguageFamily ℕ) (i : ℕ) (p : PMF ℕ) : Prop :=
  p.support = C i

/-- A semantic randomized identification algorithm on finite ordered samples. -/
abbrev StatisticalIdentifier := List ℕ → PMF ℕ

/-- Deterministic identification as a special case of a randomized kernel. -/
def deterministicIdentifier (A : GenLimit.Learner ℕ ℕ) : StatisticalIdentifier :=
  fun xs => PMF.pure (A xs)

/-- Probability of returning an index for the wrong language. -/
def identificationError (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier)
    (p : PMF ℕ) (i n : ℕ) : ℝ :=
  probability ((samples p n).bind A) {j | C j ≠ C i}

/-- One learner works for every valid distribution, with distribution-dependent
positive exponential constants. This states the upper-rate direction. -/
def ExponentialIdentifies (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier) : Prop :=
  ∀ i p, ValidDistribution C i p →
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
      ∀ n : ℕ, identificationError C A p i n ≤ D * Real.exp (-c * n)

/-- The source's nontriviality assumption: two distinct languages share a point. -/
def NontrivialCollection (C : Generic.LanguageFamily ℕ) : Prop :=
  ∃ i j x, C i ≠ C j ∧ x ∈ C i ∧ x ∈ C j

/-- A target-dependent finite witness and cutoff force correctness on every
target-contained sample, independently of its order and repetitions. -/
def FiniteWitnessIdentifies (C : Generic.LanguageFamily ℕ) (A : GenLimit.Learner ℕ ℕ) : Prop :=
  ∀ i, ∃ T : Finset ℕ, (∀ x ∈ T, x ∈ C i) ∧ ∃ N : ℕ,
    ∀ xs : List ℕ, N ≤ xs.length → (∀ x ∈ xs, x ∈ C i) →
      (∀ x ∈ T, x ∈ xs) → C (A xs) = C i

theorem identificationError_deterministic (C : Generic.LanguageFamily ℕ)
    (A : GenLimit.Learner ℕ ℕ) (p : PMF ℕ) (i n : ℕ) :
    identificationError C (deterministicIdentifier A) p i n =
      probability (samples p n) {xs | C (A xs) ≠ C i} := by
  unfold identificationError deterministicIdentifier probability
  change (((samples p n).map A).toOuterMeasure {j | C j ≠ C i}).toReal = _
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem identificationError_le_one (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier)
    (p : PMF ℕ) (i n : ℕ) : identificationError C A p i n ≤ 1 :=
  probability_le_one _ _

/-- Under the same sample law, errors for two distinct target languages
cannot both have probability less than one half. -/
theorem identificationError_add_ge_one (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier)
    (p : PMF ℕ) (i j n : ℕ) (hij : C i ≠ C j) :
    1 ≤ identificationError C A p i n + identificationError C A p j n := by
  have heq : {k | C k ≠ C i} ∪ {k | C k ≠ C j} = Set.univ := by
    ext k
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_contra! h
    exact hij (h.1.symm.trans h.2)
  have h := probability_union_le ((samples p n).bind A) {k | C k ≠ C i} {k | C k ≠ C j}
  rw [heq] at h
  have hu : probability ((samples p n).bind A) Set.univ = 1 := by
    exact probability_univ _
  rwa [hu] at h

end
end GenLimit.HallucinationModeCollapse
