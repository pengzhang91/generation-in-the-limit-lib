import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalModel

/-!
# Statistical fresh generation

Source: equation (5), Theorem 3.2, and Definition 18 of arXiv:2411.09642v3.
The output must belong to the target and be absent from the entire ordered
training sample. Randomized generators are PMF kernels, as for identification.
Generation nontriviality uses a finite subfamily with a nonempty finite
intersection; it is different from identification nontriviality.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID

abbrev StatisticalGenerator := List ℕ → PMF ℕ

/-- Expected error for one generated output, extending equation (5) of the
paper to randomized generators. We average over both the training sample and
the output drawn from `G xs`. The joint law retains the sample because
freshness depends on it.

For a fixed sample `xs`, let `q(xs)` be the probability that an output drawn
from `G xs` lies outside `C i` or occurs in `xs`. This definition is `E[q(xs)]`.
In contrast, equation (1) measures the probability over training samples that
the output support contains any such bad output. On this countable domain,
that is `Pr[q(xs) > 0]`. Since `0 ≤ q(xs) ≤ 1`, we have
`E[q(xs)] ≤ Pr[q(xs) > 0]`, possibly strictly for randomized generators.

For deterministic generators, `q(xs)` is either zero or one, so these two
errors coincide; `generationError_deterministic` gives the corresponding
sample-event formula. Thus a lower bound for this error also bounds the
equation (1) error from below, while an upper bound transfers by equality
for deterministic generators. -/
noncomputable def generationError (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : ℝ :=
  probability ((samples p n).bind fun xs => (G xs).map (fun y => (xs, y)))
    {z | z.2 ∉ C i ∨ z.2 ∈ z.1}

def ExponentialGenerates (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator) : Prop :=
  ∀ i p, ValidDistribution C i p →
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
      ∀ n : ℕ, generationError C G p i n ≤ D * Real.exp (-c * n)

def FiniteWitnessGenerates (C : Generic.LanguageFamily ℕ) (G : GenLimit.Learner ℕ ℕ) : Prop :=
  ∀ i, ∃ T : Finset ℕ, (∀ x ∈ T, x ∈ C i) ∧ ∃ N : ℕ,
    ∀ xs : List ℕ, N ≤ xs.length → (∀ x ∈ xs, x ∈ C i) →
      (∀ x ∈ T, x ∈ xs) → G xs ∈ C i ∧ G xs ∉ xs

/-- An indexed form of Definition 18, allowing repeated language indices. -/
def GenerationNontrivial (C : Generic.LanguageFamily ℕ) : Prop :=
  ∃ I : Finset ℕ, I.Nonempty ∧
    (∃ x, ∀ i ∈ I, x ∈ C i) ∧ {x | ∀ i ∈ I, x ∈ C i}.Finite

theorem generationError_deterministic (C : Generic.LanguageFamily ℕ)
    (G : GenLimit.Learner ℕ ℕ) (p : PMF ℕ) (i n : ℕ) :
    generationError C (deterministicIdentifier G) p i n =
      probability (samples p n) {xs | G xs ∉ C i ∨ G xs ∈ xs} := by
  unfold generationError deterministicIdentifier probability
  simp only [PMF.pure_map]
  change (((samples p n).map (fun xs => (xs, G xs))).toOuterMeasure _).toReal = _
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem generationError_le_one (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : generationError C G p i n ≤ 1 :=
  probability_le_one _ _

/-- A single sample contributes its mass times its conditional failure rate. -/
theorem generationError_ge_atom (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) (xs : List ℕ) :
    (samples p n xs).toReal * probability (G xs) {y | y ∉ C i ∨ y ∈ xs} ≤
      generationError C G p i n := by
  have h := probability_bind_ge (samples p n)
    (fun xs => (G xs).map (fun y => (xs, y))) {z | z.2 ∉ C i ∨ z.2 ∈ z.1} xs
  simpa only [probability, PMF.toOuterMeasure_map_apply] using h

end GenLimit.HallucinationModeCollapse
