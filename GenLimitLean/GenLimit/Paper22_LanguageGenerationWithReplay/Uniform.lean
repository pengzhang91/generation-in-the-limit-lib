import GenLimit.Paper02_LearningTheory.Definitions

/-!
# Uniform generation with adversarial replay

Source: Giorgio Racca, Michal Valko, and Amartya Sanyal,
*Language Generation with Replay: A Learning-Theoretic View of Model
Collapse*, arXiv:2603.11784v2, Definitions 3.1--3.2 and Theorem 4.1.

The paper numbers examples from one.  Here a generator output at positive
time `t` is computed from the first `t` examples.  An output made at time
`t` may therefore first be replayed as the example with zero-based index
`t`.

The theorem below is the literal black-box burn-in reduction from Algorithm
1.  The threshold is assumed positive, as required by the algorithm's
instruction to repeat the first example before the threshold is reached.
-/

namespace GenLimit
namespace Replay

open GenLimit.Generic

/-- Definition 3.1 with zero-based example indices.  At index `n`, the
adversary may supply a target example or an output produced after one of the
first `k ≤ n` nonempty histories. -/
def IsReplaySequence
    (gen : Generic.Generator α) (L : Generic.Language α)
    (stream : Generic.Stream α) : Prop :=
  ∀ n, stream n ∈ L ∨
    ∃ k, 0 < k ∧ k ≤ n ∧ Generic.output gen stream k = stream n

/-- Definition 3.2 at a fixed positive distinct-sample threshold. -/
def IsUniformReplayGeneratorAt
    (gen : Generic.Generator α) (H : Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ L, L ∈ H → ∀ stream : Generic.Stream α,
    IsReplaySequence gen L stream →
      ∀ t, 0 < t → (Generic.sample stream t).card = d →
        ∀ s, t ≤ s → Generic.CorrectAt gen L stream s

def UniformlyGeneratableWithReplay (H : Generic.LanguageClass α) : Prop :=
  ∃ gen : Generic.Generator α, ∃ d : ℕ,
    0 < d ∧ IsUniformReplayGeneratorAt gen H d

/-- Keep a finite prefix of `stream` and fill the rest with `a`. -/
def prefixExtension
    (stream : Generic.Stream α) (n : ℕ) (a : α) :
    Generic.Stream α :=
  fun k => if k < n then stream k else a

theorem prefixExtension_eq
    (stream : Generic.Stream α) (n : ℕ) (a : α) {k : ℕ}
    (hk : k < n) :
    prefixExtension stream n a k = stream k := by
  simp [prefixExtension, hk]

theorem prefixExtension_streamIn
    {stream : Generic.Stream α} {L : Generic.Language α}
    {n : ℕ} {a : α}
    (ha : a ∈ L) (hprefix : ∀ k, k < n → stream k ∈ L) :
    Generic.StreamIn (prefixExtension stream n a) L := by
  rintro x ⟨k, rfl⟩
  by_cases hk : k < n
  · simpa [prefixExtension, hk] using hprefix k hk
  · simpa [prefixExtension, hk] using ha

theorem sample_prefixExtension
    (stream : Generic.Stream α) (n : ℕ) (a : α) {t : ℕ}
    (ht : t ≤ n) :
    Generic.sample (prefixExtension stream n a) t =
      Generic.sample stream t := by
  classical
  ext x
  simp only [Generic.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, hvalue⟩
    refine ⟨k, hk, ?_⟩
    simpa [prefixExtension, lt_of_lt_of_le hk ht] using hvalue
  · rintro ⟨k, hk, hvalue⟩
    refine ⟨k, hk, ?_⟩
    simpa [prefixExtension, lt_of_lt_of_le hk ht] using hvalue

theorem output_prefixExtension
    (gen : Generic.Generator α) (stream : Generic.Stream α)
    (n : ℕ) (a : α) :
    Generic.output gen (prefixExtension stream n a) n =
      Generic.output gen stream n := by
  apply congrArg (gen n)
  funext i
  exact prefixExtension_eq stream n a i.isLt

/-- Algorithm 1.  Before seeing `d` distinct examples, repeat the first
example.  Once at least `d` have appeared, copy the original generator.  The
empty-history branch is operationally unreachable in the replay game. -/
noncomputable def burnInGenerator
    (gen : Generic.Generator α) (d : ℕ) [Inhabited α] :
    Generic.Generator α :=
  fun t xs =>
    if ht : t = 0 then default
    else if d ≤ (Generic.sequenceSample xs).card then gen t xs
    else xs ⟨0, Nat.pos_of_ne_zero ht⟩

theorem output_burnInGenerator_of_threshold
    (gen : Generic.Generator α) (d : ℕ) [Inhabited α]
    (stream : Generic.Stream α) {t : ℕ}
    (ht : 0 < t) (hd : d ≤ (Generic.sample stream t).card) :
    Generic.output (burnInGenerator gen d) stream t =
      Generic.output gen stream t := by
  have ht0 : t ≠ 0 := Nat.ne_of_gt ht
  simp [Generic.output, burnInGenerator, ht0,
    Generic.sequenceSample_prefix, hd]

theorem output_burnInGenerator_below_threshold
    (gen : Generic.Generator α) (d : ℕ) [Inhabited α]
    (stream : Generic.Stream α) {t : ℕ}
    (ht : 0 < t) (hd : ¬d ≤ (Generic.sample stream t).card) :
    Generic.output (burnInGenerator gen d) stream t = stream 0 := by
  have ht0 : t ≠ 0 := Nat.ne_of_gt ht
  simp [Generic.output, burnInGenerator, ht0,
    Generic.sequenceSample_prefix, hd]

/-- The black-box correctness lemma used inside the replay induction.  A
positive prefix whose entries are target-valid can be completed by repeating
its first element, allowing the ordinary uniform guarantee to be applied
without assuming that the future replay stream is already valid. -/
theorem ordinary_output_valid_on_valid_prefix
    [Inhabited α]
    {gen : Generic.Generator α} {H : Generic.LanguageClass α} {d : ℕ}
    (hgen : IsUniformGeneratorAt gen H d)
    {L : Generic.Language α} (hLH : L ∈ H)
    {stream : Generic.Stream α} {threshold current : ℕ}
    (hthreshold : threshold ≤ current)
    (hcurrent : 0 < current)
    (hvalid : ∀ k, k < current → stream k ∈ L)
    (hcard : (Generic.sample stream threshold).card = d) :
    Generic.output gen stream current ∈ L := by
  have hzero : stream 0 ∈ L :=
    hvalid 0 hcurrent
  let extended := prefixExtension stream current (stream 0)
  have hextended : Generic.StreamIn extended L := by
    exact prefixExtension_streamIn hzero hvalid
  have hsample :
      Generic.sample extended threshold =
        Generic.sample stream threshold := by
    exact sample_prefixExtension stream current (stream 0) hthreshold
  have hcorrect :=
    hgen L hLH extended hextended threshold
      (by simpa [hsample] using hcard) current hthreshold
  have hout :
      Generic.output gen extended current =
        Generic.output gen stream current :=
    output_prefixExtension gen stream current (stream 0)
  have hvalidOutput := hcorrect.1
  rw [hout] at hvalidOutput
  exact hvalidOutput

/-- A replay stream for the burn-in conversion is in fact target-valid once
it reaches the ordinary generator's threshold.  This is the induction at
the heart of Theorem 4.1. -/
theorem replayStream_streamIn_of_reaches_threshold
    [Inhabited α]
    {gen : Generic.Generator α} {H : Generic.LanguageClass α} {d : ℕ}
    (hgen : IsUniformGeneratorAt gen H d)
    {L : Generic.Language α} (hLH : L ∈ H)
    {stream : Generic.Stream α}
    (hreplay : IsReplaySequence (burnInGenerator gen d) L stream)
    {t : ℕ} (_ht : 0 < t)
    (hcard : (Generic.sample stream t).card = d) :
    Generic.StreamIn stream L := by
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases hreplay n with hnL | ⟨k, hkpos, hkn, hkout⟩
      · exact hnL
      · rw [← hkout]
        have hprefix : ∀ j, j < k → stream j ∈ L := by
          intro j hj
          exact ih j (lt_of_lt_of_le hj hkn)
        by_cases hkt : k < t
        · have hcard_le :
              (Generic.sample stream k).card ≤ d := by
            rw [← hcard]
            exact Finset.card_le_card
              (Generic.sample_mono (Nat.le_of_lt hkt))
          by_cases hthreshold : d ≤ (Generic.sample stream k).card
          · have hcardk : (Generic.sample stream k).card = d :=
              Nat.le_antisymm hcard_le hthreshold
            rw [output_burnInGenerator_of_threshold
              gen d stream hkpos hthreshold]
            exact ordinary_output_valid_on_valid_prefix
              hgen hLH (le_refl k) hkpos hprefix hcardk
          · rw [output_burnInGenerator_below_threshold
              gen d stream hkpos hthreshold]
            exact ih 0 (lt_of_lt_of_le hkpos hkn)
        · have htk : t ≤ k := Nat.le_of_not_gt hkt
          have hthreshold : d ≤ (Generic.sample stream k).card := by
            rw [← hcard]
            exact Finset.card_le_card (Generic.sample_mono htk)
          rw [output_burnInGenerator_of_threshold
            gen d stream hkpos hthreshold]
          exact ordinary_output_valid_on_valid_prefix
            hgen hLH htk hkpos hprefix hcard

/-- The nontrivial direction of Theorem 4.1: Algorithm 1 preserves the exact
uniform sample threshold under arbitrary replay. -/
theorem uniform_to_uniformWithReplay
    [Inhabited α]
    {gen : Generic.Generator α} {H : Generic.LanguageClass α} {d : ℕ}
    (_hd : 0 < d)
    (hgen : IsUniformGeneratorAt gen H d) :
    IsUniformReplayGeneratorAt (burnInGenerator gen d) H d := by
  intro L hLH stream hreplay t ht hcard s hts
  have hstreamIn : Generic.StreamIn stream L :=
    replayStream_streamIn_of_reaches_threshold
      hgen hLH hreplay ht hcard
  have hds : d ≤ (Generic.sample stream s).card := by
    rw [← hcard]
    exact Finset.card_le_card (Generic.sample_mono hts)
  rw [Generic.CorrectAt,
    output_burnInGenerator_of_threshold gen d stream
      (lt_of_lt_of_le ht hts) hds]
  exact hgen L hLH stream hstreamIn t hcard s hts

/-- The easy direction of Theorem 4.1: an ordinary positive stream is a
replay stream that never uses the replay alternative. -/
theorem uniformWithReplay_to_uniform
    {gen : Generic.Generator α} {H : Generic.LanguageClass α} {d : ℕ}
    (hd : 0 < d)
    (hgen : IsUniformReplayGeneratorAt gen H d) :
    IsUniformGeneratorAt gen H d := by
  intro L hLH stream hstream t hcard s hts
  have ht : 0 < t := by
    have hdle : d ≤ t := by
      rw [← hcard]
      exact Generic.sample_card_le stream t
    exact lt_of_lt_of_le hd hdle
  apply hgen L hLH stream
  · intro n
    exact Or.inl (hstream ⟨n, rfl⟩)
  · exact ht
  · exact hcard
  · exact hts

/-- Theorem 4.1 at a fixed positive threshold, including equality of the
threshold before and after the conversion. -/
theorem theorem_4_1
    [Inhabited α]
    (H : Generic.LanguageClass α) (d : ℕ) (hd : 0 < d) :
    (∃ gen : Generic.Generator α, IsUniformGeneratorAt gen H d) ↔
      ∃ gen : Generic.Generator α,
        IsUniformReplayGeneratorAt gen H d := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact ⟨burnInGenerator gen d, uniform_to_uniformWithReplay hd hgen⟩
  · rintro ⟨gen, hgen⟩
    exact ⟨gen, uniformWithReplay_to_uniform hd hgen⟩

end Replay
end GenLimit
