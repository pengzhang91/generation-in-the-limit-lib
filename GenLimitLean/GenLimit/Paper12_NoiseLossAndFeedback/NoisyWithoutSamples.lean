import GenLimit.Paper12_NoiseLossAndFeedback.WithoutSamples

/-!
# Noise, Loss, and Feedback: finite noise versus no samples

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Definitions 2.8--2.11,
Algorithms 1--2, and Theorems 4.4--4.5.

`NoisyEnumeration` is the paper's repetition-free stream whose range contains
the target and has only finitely many values outside it.  The generator
success notions below retain the paper's time convention: at paper time `t`
the examples `x₀,...,xₜ` have already been observed.

The reverse reduction in the source probes a noisy generator on the finite
prefix `0,...,t`.  Such a prefix is not itself a noisy enumeration of an
arbitrary target.  The ordered-prefix continuation lemma below supplies the
missing semantic step: append an injective enumeration of the as-yet unseen
part of the infinite target.  The final equivalences are stated over `ℕ`,
exactly the universe chosen without loss of generality in the paper.  No
computability, probability, or running-time claim is made.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## Paper-facing finite-noise definitions -/

/-- Definition 2.8: an injective stream that covers the target and has only
finitely many extraneous values. -/
abbrev NoisyEnumeration
    (stream : Stream α) (L : GenLimit.Generic.Language α) : Prop :=
  GenLimit.Generic.InjectiveValueContaminatedPresentation stream L

/-- Definition 2.9 at a fixed generator. -/
def IsUniformNoisyGenerator
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∃ T : ℕ, ∀ L, L ∈ C → ∀ stream,
    NoisyEnumeration stream L →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Uniform noisy generatability. -/
def UniformlyNoisilyGeneratable
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsUniformNoisyGenerator gen C

/-- Definition 2.10 at a fixed generator.  The threshold depends on the
target, but not on its noisy enumeration. -/
def IsNonuniformNoisyGenerator
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∃ T : ℕ, ∀ stream,
    NoisyEnumeration stream L →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Non-uniform noisy generatability. -/
def NonuniformlyNoisilyGeneratable
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsNonuniformNoisyGenerator gen C

/-- Definition 2.11 at a fixed generator.  The stabilization threshold may
depend on both the target and the particular noisy enumeration. -/
def IsNoisyLimitGenerator
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∀ stream,
    NoisyEnumeration stream L →
      ∃ T : ℕ, ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Noisy generation in the limit from Definition 2.11. -/
def NoisilyGeneratableInLimit
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsNoisyLimitGenerator gen C

/-! ## Algorithm 1: skip already observed outputs -/

theorem exists_fresh_tail_offset
    (gen : WithoutSamplesGenerator α) (lower : ℕ) (S : Finset α) :
    ∃ k : ℕ, gen.output (lower + k) ∉ S := by
  by_contra h
  push_neg at h
  have hsubset : outputTail gen lower ⊆ (S : Set α) := by
    rintro x ⟨k, rfl⟩
    exact h k
  exact
    (outputTail_infinite gen lower)
      (S.finite_toSet.subset hsubset)

/-- The first offset in the no-sample output tail that avoids `S`. -/
noncomputable def firstFreshTailOffset
    (gen : WithoutSamplesGenerator α) (lower : ℕ) (S : Finset α) : ℕ :=
  by
    classical
    exact Nat.find (exists_fresh_tail_offset gen lower S)

theorem firstFreshTailOffset_spec
    (gen : WithoutSamplesGenerator α) (lower : ℕ) (S : Finset α) :
    gen.output (lower + firstFreshTailOffset gen lower S) ∉ S :=
  by
    classical
    exact Nat.find_spec (exists_fresh_tail_offset gen lower S)

/-- Algorithm 1: at a prefix of length `n`, scan the no-sample output tail
starting at `n` and return its first value absent from the observed sample. -/
noncomputable def noisyGeneratorFromWithoutSamples
    (gen : WithoutSamplesGenerator α) : Generator α :=
  fun n xs =>
    gen.output
      (n + firstFreshTailOffset gen n (sequenceSample xs))

theorem uniformly_withoutSamples_to_noisy
    {gen : WithoutSamplesGenerator α} {C : LanguageClass α}
    (hgen : UniformlyGeneratesWithoutSamples gen C) :
    IsUniformNoisyGenerator
      (noisyGeneratorFromWithoutSamples gen) C := by
  obtain ⟨T, hT⟩ := hgen
  refine ⟨T, ?_⟩
  intro L hLC stream _hstream t ht
  let S := sequenceSample (fun k : Fin (t + 1) => stream k)
  let k := firstFreshTailOffset gen (t + 1) S
  have hindex : T ≤ (t + 1) + k := by
    omega
  constructor
  · exact hT L hLC ((t + 1) + k) hindex
  · have hfresh :
        gen.output ((t + 1) + k) ∉ S :=
      firstFreshTailOffset_spec gen (t + 1) S
    have hsample :
        S = observedThrough stream t := by
      exact sequenceSample_prefix stream (t + 1)
    simpa [noisyGeneratorFromWithoutSamples, outputAt,
      GenLimit.Generic.output, k, S, hsample] using hfresh

theorem nonuniformly_withoutSamples_to_noisy
    {gen : WithoutSamplesGenerator α} {C : LanguageClass α}
    (hgen : GeneratesInLimitWithoutSamples gen C) :
    IsNonuniformNoisyGenerator
      (noisyGeneratorFromWithoutSamples gen) C := by
  intro L hLC
  obtain ⟨T, hT⟩ := hgen L hLC
  refine ⟨T, ?_⟩
  intro stream _hstream t ht
  let S := sequenceSample (fun k : Fin (t + 1) => stream k)
  let k := firstFreshTailOffset gen (t + 1) S
  have hindex : T ≤ (t + 1) + k := by
    omega
  constructor
  · exact hT ((t + 1) + k) hindex
  · have hfresh :
        gen.output ((t + 1) + k) ∉ S :=
      firstFreshTailOffset_spec gen (t + 1) S
    have hsample :
        S = observedThrough stream t := by
      exact sequenceSample_prefix stream (t + 1)
    simpa [noisyGeneratorFromWithoutSamples, outputAt,
      GenLimit.Generic.output, k, S, hsample] using hfresh

theorem uniformly_withoutSamples_implies_noisilyGeneratable
    {C : LanguageClass α}
    (h : UniformlyGeneratableWithoutSamples C) :
    UniformlyNoisilyGeneratable C := by
  obtain ⟨gen, hgen⟩ := h
  exact
    ⟨noisyGeneratorFromWithoutSamples gen,
      uniformly_withoutSamples_to_noisy hgen⟩

theorem inLimit_withoutSamples_implies_nonuniformlyNoisy
    {C : LanguageClass α}
    (h : GeneratableInLimitWithoutSamples C) :
    NonuniformlyNoisilyGeneratable C := by
  obtain ⟨gen, hgen⟩ := h
  exact
    ⟨noisyGeneratorFromWithoutSamples gen,
      nonuniformly_withoutSamples_to_noisy hgen⟩

/-! ## Completing the finite probe prefix -/

/-- Every ordered injective finite prefix extends to a noisy enumeration of
an infinite target.  The range is the union of the prefix values and the
target, so all extraneous values lie in the finite prefix.

This is the semantic continuation obligation implicit in the proofs of
Theorems 4.4--4.5. -/
theorem noisyEnumeration_extending_ordered_prefix
    [Countable α]
    {n : ℕ} {xs : Fin n → α}
    (hxs : Function.Injective xs)
    {L : GenLimit.Generic.Language α} (hL : L.Infinite) :
    ∃ full : Stream α,
      NoisyEnumeration full L ∧
      (∀ k : Fin n, full k = xs k) := by
  classical
  let hrest :
      (L \ (sequenceSample xs : Set α)).Infinite :=
    hL.diff (sequenceSample xs).finite_toSet
  let full := prefixThenTarget xs L hrest
  have hrange :
      Set.range full = (sequenceSample xs : Set α) ∪ L :=
    range_prefixThenTarget_eq_prefix_union
      xs L hrest
  refine ⟨full, ?_, ?_⟩
  · refine
      ⟨prefixThenTarget_injective hxs L hrest, ?_, ?_⟩
    · rw [hrange]
      exact Set.subset_union_right
    · rw [hrange]
      apply (sequenceSample xs).finite_toSet.subset
      rintro x ⟨hx, hxnotL⟩
      exact hx.resolve_right hxnotL
  · intro k
    exact prefixThenTarget_prefix xs L hrest k

/-- Correctness on every noisy enumeration at one fixed time transfers to an
arbitrary injective probe stream at that time. -/
theorem correctAt_of_all_noisyEnumerations
    [Countable α]
    {gen : Generator α} {L : GenLimit.Generic.Language α}
    {stream : Stream α} (hstream : Function.Injective stream)
    {t : ℕ} (hL : L.Infinite)
    (hcorrect :
      ∀ full : Stream α,
        NoisyEnumeration full L →
        CorrectAt gen L full t) :
    CorrectAt gen L stream t := by
  let xs : Fin (t + 1) → α := fun k => stream k
  have hxs : Function.Injective xs := by
    intro i j hij
    exact Fin.ext (hstream hij)
  obtain ⟨full, hfull, hprefix⟩ :=
    noisyEnumeration_extending_ordered_prefix hxs hL
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
    rw [← sequenceSample_prefix full (t + 1),
      ← sequenceSample_prefix stream (t + 1), hpref]
  have h := hcorrect full hfull
  simpa [CorrectAt, hout, hsample] using h

/-! ## Algorithm 2: probe on `0,...,t` and extract fresh records -/

/-- The identity probe stream used after identifying the universe with
`ℕ`, as in the source proof. -/
def identityProbe : Stream ℕ := fun n => n

theorem identityProbe_injective :
    Function.Injective identityProbe :=
  fun _ _ h => h

theorem observedThrough_identityProbe (t : ℕ) :
    observedThrough identityProbe t = Finset.range (t + 1) := by
  classical
  ext x
  simp [observedThrough, identityProbe, GenLimit.Generic.mem_sample_iff]

/-- The raw output obtained by probing `gen` on `0,...,t`. -/
def probeOutput (gen : Generator ℕ) (t : ℕ) : ℕ :=
  outputAt gen identityProbe t

theorem correctAt_identityProbe_of_all_noisy
    {gen : Generator ℕ} {L : GenLimit.Generic.Language ℕ} {t : ℕ}
    (hL : L.Infinite)
    (hcorrect :
      ∀ full : Stream ℕ,
        NoisyEnumeration full L →
        CorrectAt gen L full t) :
    CorrectAt gen L identityProbe t :=
  correctAt_of_all_noisyEnumerations
    identityProbe_injective hL hcorrect

theorem probeOutput_above_time
    {gen : Generator ℕ} {L : GenLimit.Generic.Language ℕ} {t : ℕ}
    (hcorrect : CorrectAt gen L identityProbe t) :
    t < probeOutput gen t := by
  have hnot :
      probeOutput gen t ∉ Finset.range (t + 1) := by
    rw [← observedThrough_identityProbe t]
    exact hcorrect.2
  have hge : t + 1 ≤ probeOutput gen t := by
    simpa using hnot
  omega

/-- Probe times used to make the raw outputs globally injective.  The next
time is later than both the preceding time and preceding output. -/
def recordTime (z : ℕ → ℕ) (T : ℕ) : ℕ → ℕ
  | 0 => T
  | n + 1 =>
      max (recordTime z T n + 1) (z (recordTime z T n) + 1)

theorem start_add_le_recordTime
    (z : ℕ → ℕ) (T n : ℕ) :
    T + n ≤ recordTime z T n := by
  induction n with
  | zero =>
      simp [recordTime]
  | succ n ih =>
      rw [recordTime]
      have hmax :
          recordTime z T n + 1 ≤
            max (recordTime z T n + 1)
              (z (recordTime z T n) + 1) :=
        Nat.le_max_left _ _
      omega

theorem previous_output_lt_next_recordTime
    (z : ℕ → ℕ) (T n : ℕ) :
    z (recordTime z T n) < recordTime z T (n + 1) := by
  rw [recordTime]
  exact Nat.lt_of_succ_le (Nat.le_max_right _ _)

theorem recordOutput_strictMono
    {z : ℕ → ℕ} {T : ℕ}
    (hdiag : ∀ t, T ≤ t → t < z t) :
    StrictMono (fun n => z (recordTime z T n)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hfirst :
      z (recordTime z T n) < recordTime z T (n + 1) :=
    previous_output_lt_next_recordTime z T n
  have hstart : T ≤ recordTime z T (n + 1) := by
    have h := start_add_le_recordTime z T (n + 1)
    omega
  exact hfirst.trans (hdiag _ hstart)

/-- A repetition-free subsequence of the raw probe outputs. -/
def recordSubsequence
    (z : ℕ → ℕ) (T : ℕ)
    (hdiag : ∀ t, T ≤ t → t < z t) :
    WithoutSamplesGenerator ℕ where
  output n := z (recordTime z T n)
  injective' := (recordOutput_strictMono hdiag).injective

theorem recordSubsequence_eventually_mem
    {z : ℕ → ℕ} {T : ℕ}
    (hdiag : ∀ t, T ≤ t → t < z t)
    {L : GenLimit.Generic.Language ℕ} {TL : ℕ}
    (hmem : ∀ t, TL ≤ t → z t ∈ L) :
    ∀ n, TL ≤ n →
      (recordSubsequence z T hdiag).output n ∈ L := by
  intro n hn
  apply hmem
  have h := start_add_le_recordTime z T n
  omega

/-- A canonical no-sample generator used when the language class is empty. -/
def identityWithoutSamplesGenerator :
    WithoutSamplesGenerator ℕ where
  output n := n
  injective' := fun _ _ h => h

theorem uniformly_noisy_implies_withoutSamples
    {C : LanguageClass ℕ}
    (hInfinite : GenLimit.Generic.UUS C)
    (h : UniformlyNoisilyGeneratable C) :
    UniformlyGeneratableWithoutSamples C := by
  obtain ⟨gen, T, hT⟩ := h
  by_cases hC : C.Nonempty
  · obtain ⟨L₀, hL₀C⟩ := hC
    have hcorrect :
        ∀ L, L ∈ C → ∀ t, T ≤ t →
          CorrectAt gen L identityProbe t := by
      intro L hLC t ht
      apply correctAt_identityProbe_of_all_noisy
        (hInfinite L hLC)
      intro full hfull
      exact hT L hLC full hfull t ht
    have hdiag :
        ∀ t, T ≤ t → t < probeOutput gen t := by
      intro t ht
      exact probeOutput_above_time
        (hcorrect L₀ hL₀C t ht)
    let out :=
      recordSubsequence (probeOutput gen) T hdiag
    refine ⟨out, T, ?_⟩
    intro L hLC n hn
    apply
      recordSubsequence_eventually_mem hdiag
        (L := L)
        (fun t ht => (hcorrect L hLC t ht).1)
        n hn
  · refine ⟨identityWithoutSamplesGenerator, 0, ?_⟩
    intro L hLC
    exact (hC ⟨L, hLC⟩).elim

theorem nonuniformly_noisy_implies_inLimit_withoutSamples
    {C : LanguageClass ℕ}
    (hInfinite : GenLimit.Generic.UUS C)
    (h : NonuniformlyNoisilyGeneratable C) :
    GeneratableInLimitWithoutSamples C := by
  obtain ⟨gen, hgen⟩ := h
  by_cases hC : C.Nonempty
  · obtain ⟨L₀, hL₀C⟩ := hC
    obtain ⟨T₀, hT₀⟩ := hgen L₀ hL₀C
    have hcorrect₀ :
        ∀ t, T₀ ≤ t → CorrectAt gen L₀ identityProbe t := by
      intro t ht
      apply correctAt_identityProbe_of_all_noisy
        (hInfinite L₀ hL₀C)
      intro full hfull
      exact hT₀ full hfull t ht
    have hdiag :
        ∀ t, T₀ ≤ t → t < probeOutput gen t := by
      intro t ht
      exact probeOutput_above_time (hcorrect₀ t ht)
    let out :=
      recordSubsequence (probeOutput gen) T₀ hdiag
    refine ⟨out, ?_⟩
    intro L hLC
    obtain ⟨TL, hTL⟩ := hgen L hLC
    refine ⟨TL, ?_⟩
    intro n hn
    have htime :
        TL ≤ recordTime (probeOutput gen) T₀ n := by
      have hrecord :=
        start_add_le_recordTime (probeOutput gen) T₀ n
      omega
    have hcorrect :
        CorrectAt gen L identityProbe
          (recordTime (probeOutput gen) T₀ n) := by
      apply correctAt_identityProbe_of_all_noisy
        (hInfinite L hLC)
      intro full hfull
      exact hTL full hfull _ htime
    exact hcorrect.1
  · refine ⟨identityWithoutSamplesGenerator, ?_⟩
    intro L hLC
    exact (hC ⟨L, hLC⟩).elim

/-! ## Theorems 4.4--4.5 -/

/-- Theorem 4.4: uniform noisy generation is equivalent to uniform
generation without samples. -/
theorem theorem_4_4
    (C : LanguageClass ℕ)
    (hInfinite : GenLimit.Generic.UUS C) :
    UniformlyNoisilyGeneratable C ↔
      UniformlyGeneratableWithoutSamples C :=
  ⟨uniformly_noisy_implies_withoutSamples hInfinite,
    uniformly_withoutSamples_implies_noisilyGeneratable⟩

/-- Theorem 4.5: non-uniform noisy generation is equivalent to generation
in the limit without samples. -/
theorem theorem_4_5
    (C : LanguageClass ℕ)
    (hInfinite : GenLimit.Generic.UUS C) :
    NonuniformlyNoisilyGeneratable C ↔
      GeneratableInLimitWithoutSamples C :=
  ⟨nonuniformly_noisy_implies_inLimit_withoutSamples hInfinite,
    inLimit_withoutSamples_implies_nonuniformlyNoisy⟩

end GenLimit.NoiseLossFeedback
