import GenLimit.Core.GenericGeneration

/-!
# Prompted generation: paper-facing definitions

This file formalizes Assumption 5.1 and Definitions 5.1--5.4 in
Li--Raman--Tewari, *Generation through the Lens of Learning Theory*,
arXiv:2410.13714v5 / COLT 2025.

The paper's round `s` is one-based: the generator observes the current triple
`(x_s, h(x_s), y_s)` and then produces its output.  Lean represents this by a
history of length `s`; `PromptedCorrectAt` is vacuous at the artificial
zero-length round and uses the last prompt at every positive round.
-/

namespace GenLimit.LiRamanTewari

/-- A multiclass hypothesis and a class of multiclass hypotheses. -/
abbrev MulticlassHypothesis (α ι : Type*) := α → ι

abbrev MulticlassHypothesisClass (α ι : Type*) :=
  Set (MulticlassHypothesis α ι)

/-- The paper's `y`-support `supp(h,y)`. -/
def promptSupport (h : MulticlassHypothesis α ι) (y : ι) : Set α :=
  {x | h x = y}

/-- Assumption 5.1, Prompted Uniformly Unbounded Support (PUUS). -/
def PUUS (H : MulticlassHypothesisClass α ι) : Prop :=
  ∀ h, h ∈ H → ∀ y, (promptSupport h y).Infinite

/-- A revealed prompted example consists, in this order, of an example, its
true multiclass label, and the current prompt. -/
abbrev PromptedObservation (α ι : Type*) := α × ι × ι

/-- Definition 5.1.  The source has `h(x₁)` in its displayed second tuple;
the game description and every subsequent formula use the intended true
label `h(x₂)`, which is represented by the middle coordinate here. -/
abbrev PromptedGenerator (α ι : Type*) :=
  ∀ t : ℕ, (Fin t → PromptedObservation α ι) → α

/-- The exact history revealed to a prompted generator after `t` rounds. -/
def promptedHistory
    (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι)
    (t : ℕ) : Fin t → PromptedObservation α ι :=
  fun i ↦ (xs i, h (xs i), ys i)

/-- Distinct examples among the first `t` observations whose true label is
the fixed prompt `y`; this is
`{x₁,...,x_t} ∩ supp(h,y)` from Definitions 5.2--5.3. -/
noncomputable def promptedSample
    (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (y : ι) (t : ℕ) : Finset α := by
  classical
  exact (GenLimit.Generic.sample xs t).filter (fun x ↦ h x = y)

theorem mem_promptedSample_iff
    {h : MulticlassHypothesis α ι}
    {xs : GenLimit.Generic.Stream α} {y : ι} {t : ℕ} {x : α} :
    x ∈ promptedSample h xs y t ↔
      x ∈ GenLimit.Generic.sample xs t ∧ h x = y := by
  classical
  simp [promptedSample]

theorem promptedSample_mono
    {h : MulticlassHypothesis α ι}
    {xs : GenLimit.Generic.Stream α} {y : ι} {s t : ℕ}
    (hst : s ≤ t) :
    promptedSample h xs y s ⊆ promptedSample h xs y t := by
  classical
  intro x hx
  rw [mem_promptedSample_iff] at hx ⊢
  exact ⟨GenLimit.Generic.sample_mono hst hx.1, hx.2⟩

/-- Correctness at the paper's one-based round `s`.  The artificial Lean
round `s = 0` is vacuous.  At a positive round the generator has seen exactly
the first `s` triples and must answer the prompt in the last triple. -/
def PromptedCorrectAt
    (gen : PromptedGenerator α ι) (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι)
    (s : ℕ) : Prop :=
  ∀ _hs : 0 < s,
    gen s (promptedHistory h xs ys s) ∈
      promptSupport h (ys (s - 1)) \
        (↑(GenLimit.Generic.sample xs s) : Set α)

/-- A fixed threshold `d` witnesses Definition 5.2 for `gen` and `H`.

The threshold prefix and every later output retain the paper's quantifier
order.  In particular, the prompt `yStar` is universally quantified after
the two streams, and correctness is required only on later rounds whose
current prompt equals `yStar`. -/
def IsPromptedUniformGeneratorAt
    (gen : PromptedGenerator α ι)
    (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop :=
  ∀ h, h ∈ H →
    ∀ xs : GenLimit.Generic.Stream α,
    ∀ ys : GenLimit.Generic.Stream ι,
    ∀ yStar : ι,
    ∀ t, (promptedSample h xs yStar t).card = d →
      ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar →
        PromptedCorrectAt gen h xs ys s

/-- Definition 5.2, Prompted Uniform Generatability. -/
def PromptedUniformlyGeneratable
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∃ gen : PromptedGenerator α ι, ∃ d : ℕ,
    IsPromptedUniformGeneratorAt gen H d

/-- A prompted non-uniform generator.  As in Definition 5.3, the threshold
may depend on `h`, but not on either stream or on the prompt. -/
def IsPromptedNonuniformGenerator
    (gen : PromptedGenerator α ι)
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∀ h, h ∈ H → ∃ d : ℕ,
    ∀ xs : GenLimit.Generic.Stream α,
    ∀ ys : GenLimit.Generic.Stream ι,
    ∀ yStar : ι,
    ∀ t, (promptedSample h xs yStar t).card = d →
      ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar →
        PromptedCorrectAt gen h xs ys s

/-- Definition 5.3, Prompted Non-uniform Generatability. -/
def PromptedNonuniformlyGeneratable
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∃ gen : PromptedGenerator α ι, IsPromptedNonuniformGenerator gen H

/-- Definition 5.4's premise: the example stream contains the entire
`y`-support.  The paper allows additional examples in the stream. -/
def PromptSupportPresented
    (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (y : ι) : Prop :=
  promptSupport h y ⊆ Set.range xs

/-- A prompted generator witnesses Definition 5.4. -/
def IsPromptedLimitGenerator
    (gen : PromptedGenerator α ι)
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∀ h, h ∈ H →
    ∀ xs : GenLimit.Generic.Stream α,
    ∀ ys : GenLimit.Generic.Stream ι,
    ∀ yStar : ι,
    PromptSupportPresented h xs yStar →
      ∃ t, ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar →
        PromptedCorrectAt gen h xs ys s

/-- Definition 5.4, Prompted Generatability in the Limit. -/
def PromptedGeneratableInLimit
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∃ gen : PromptedGenerator α ι, IsPromptedLimitGenerator gen H

/-- The prompted version space `H(S,y)`. -/
def promptedVersionSpace
    (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) :
    Set (MulticlassHypothesis α ι) :=
  {h | h ∈ H ∧ ∀ x ∈ S, h x = y}

/-- The common `y`-support of the prompted version space. -/
def promptedCommonCore
    (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Set α :=
  {x | ∀ h, h ∈ promptedVersionSpace H S y → h x = y}

/-- The prompted closure, with `none` representing the paper's `⊥`. -/
noncomputable def promptedClosure
    (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) :
    Option (Set α) := by
  classical
  exact if (promptedVersionSpace H S y).Nonempty
    then some (promptedCommonCore H S y)
    else none

theorem mem_promptedVersionSpace_iff
    {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι}
    {h : MulticlassHypothesis α ι} :
    h ∈ promptedVersionSpace H S y ↔
      h ∈ H ∧ ∀ x ∈ S, h x = y :=
  Iff.rfl

theorem promptedClosure_eq_none_iff
    {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι} :
    promptedClosure H S y = none ↔
      ¬(promptedVersionSpace H S y).Nonempty := by
  classical
  simp [promptedClosure]

theorem promptedClosure_eq_some_iff
    {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι} {C : Set α} :
    promptedClosure H S y = some C ↔
      (promptedVersionSpace H S y).Nonempty ∧
        C = promptedCommonCore H S y := by
  classical
  constructor
  · intro hcl
    by_cases hVS : (promptedVersionSpace H S y).Nonempty
    · refine ⟨hVS, ?_⟩
      have : promptedCommonCore H S y = C := by
        simpa [promptedClosure, hVS] using hcl
      exact this.symm
    · simp [promptedClosure, hVS] at hcl
  · rintro ⟨hVS, rfl⟩
    simp [promptedClosure, hVS]

theorem promptedSample_subset_commonCore
    {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι} :
    (↑S : Set α) ⊆ promptedCommonCore H S y := by
  intro x hx h hh
  exact hh.2 x hx

theorem promptedCommonCore_subset_support
    {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι}
    {h : MulticlassHypothesis α ι}
    (hh : h ∈ promptedVersionSpace H S y) :
    promptedCommonCore H S y ⊆ promptSupport h y := by
  intro x hx
  exact hx h hh

end GenLimit.LiRamanTewari
