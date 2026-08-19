import GenLimit.Paper12_NoiseLossAndFeedback.WithoutSamples

/-!
# Noise, Loss, and Feedback: infinite omissions

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Definitions 4.8--4.10 and
Theorems 4.11--4.12.

At paper time `t`, the generator has seen `x₀,...,xₜ`.  Consequently
`outputAt` evaluates the generic prefix generator at length `t+1`.

The printed proofs of Theorems 4.11--4.12 say that every finite prefix of an
infinite-omission enumeration can be extended to a valid full enumeration.
The construction below supplies that proof obligation explicitly: retain the
ordered injective prefix, then enumerate the infinite target complement
without repetition.
-/

namespace GenLimit.NoiseLossFeedback

/-- The paper's standard repetition-free enumeration. -/
abbrev ExactEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  GenLimit.Support.InjectivePresentation stream L

/-- Definition 4.8: an injective infinite sequence contained in the target.
Its range can be any infinite subset of the target. -/
def InfiniteOmissionEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  Function.Injective stream ∧ GenLimit.Generic.StreamIn stream L

/-- Definitions 2.2 and 2.4 in the paper's repetition-free convention:
uniform generation by a fixed generator. -/
def IsUniformGenerator
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ T : ℕ, ∀ L, L ∈ C → ∀ stream,
    ExactEnumeration stream L →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Non-uniform generation by a fixed generator; the threshold may depend on
the target but not on its enumeration. -/
def IsNonuniformGenerator
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∃ T : ℕ, ∀ stream,
    ExactEnumeration stream L →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Definition 4.9 at a fixed generator. -/
def IsUniformInfiniteOmissionGenerator
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ T : ℕ, ∀ L, L ∈ C → ∀ stream,
    InfiniteOmissionEnumeration stream L →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Definition 4.10 at a fixed generator. -/
def IsNonuniformInfiniteOmissionGenerator
    (gen : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∃ T : ℕ, ∀ stream,
    InfiniteOmissionEnumeration stream L →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Every finite prefix of an infinite-omission enumeration extends to a
repetition-free exact enumeration, without changing that ordered prefix. -/
theorem exactEnumeration_extending_prefix
    [Countable α]
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hL : L.Infinite)
    (hstream : InfiniteOmissionEnumeration stream L)
    (n : ℕ) :
    ∃ full : GenLimit.Generic.Stream α,
      ExactEnumeration full L ∧
      (∀ k : Fin n, full k = stream k) := by
  let xs : Fin n → α := fun k => stream k
  have hxs : Function.Injective xs := by
    intro i j hij
    exact Fin.ext (hstream.1 hij)
  have hxsL : ∀ i, xs i ∈ L := by
    intro i
    exact hstream.2 ⟨i, rfl⟩
  let hrest :
      (L \ (GenLimit.Generic.sequenceSample xs : Set α)).Infinite :=
    hL.diff (GenLimit.Generic.sequenceSample xs).finite_toSet
  let full := prefixThenTarget xs L hrest
  refine ⟨full, ?_, ?_⟩
  · exact
      ⟨prefixThenTarget_injective hxs L hrest,
        prefixThenTarget_range L hxsL hrest⟩
  · intro k
    exact prefixThenTarget_prefix xs L hrest k

/-- The semantic core of the printed argument: correctness on every exact
enumeration at one fixed time transfers to any infinite-omission
enumeration at that same time. -/
theorem correctAt_of_exactEnumerations
    [Countable α]
    {gen : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (hL : L.Infinite)
    (hstream : InfiniteOmissionEnumeration stream L)
    (hcorrect :
      ∀ full : GenLimit.Generic.Stream α,
        ExactEnumeration full L →
        CorrectAt gen L full t) :
    CorrectAt gen L stream t := by
  obtain ⟨full, hfull, hprefix⟩ :=
    exactEnumeration_extending_prefix hL hstream (t + 1)
  have hpref :
      (fun k : Fin (t + 1) => full k) =
        fun k : Fin (t + 1) => stream k := by
    funext k
    exact hprefix k
  have hout :
      outputAt gen full t = outputAt gen stream t := by
    unfold outputAt GenLimit.Generic.output
    rw [hpref]
  have hsample :
      observedThrough full t = observedThrough stream t := by
    unfold observedThrough
    rw [← GenLimit.Generic.sequenceSample_prefix full (t + 1),
      ← GenLimit.Generic.sequenceSample_prefix stream (t + 1),
      hpref]
  have h := hcorrect full hfull
  simpa [CorrectAt, hout, hsample] using h

/-- Theorem 4.11: the very same uniformly successful generator tolerates
arbitrary infinite omissions. -/
theorem theorem_4_11
    [Countable α]
    {gen : GenLimit.Generic.Generator α}
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : ∀ L, L ∈ C → L.Infinite)
    (hgen : IsUniformGenerator gen C) :
    IsUniformInfiniteOmissionGenerator gen C := by
  obtain ⟨T, hT⟩ := hgen
  refine ⟨T, ?_⟩
  intro L hLC stream hstream t ht
  apply correctAt_of_exactEnumerations (hInfinite L hLC) hstream
  intro full hfull
  exact hT L hLC full hfull t ht

/-- Theorem 4.12: the same preservation result with a target-dependent
threshold. -/
theorem theorem_4_12
    [Countable α]
    {gen : GenLimit.Generic.Generator α}
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : ∀ L, L ∈ C → L.Infinite)
    (hgen : IsNonuniformGenerator gen C) :
    IsNonuniformInfiniteOmissionGenerator gen C := by
  intro L hLC
  obtain ⟨T, hT⟩ := hgen L hLC
  refine ⟨T, ?_⟩
  intro stream hstream t ht
  apply correctAt_of_exactEnumerations (hInfinite L hLC) hstream
  intro full hfull
  exact hT full hfull t ht

end GenLimit.NoiseLossFeedback
