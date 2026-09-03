import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackEquivalence

/-!
# A sequence-sensitive gap in Appendix Lemma A.8

The proof of P27 Theorem 3.9 claims that an arbitrary successful
sequence-sensitive element generator, after harmless freshening, becomes
self-locking along every fixed presentation.  The construction below shows
that this does not follow from the stated hypotheses.

On a singleton class the generator is wrong only on a prefix belonging to a
pairwise prefix-incomparable family of finite histories.  It therefore makes
at most one error on every presentation and is fresh on every history.
Nevertheless, every prefix of one fixed presentation has a one-element
target continuation leading to an error.  Thus no prefix of that presentation
has the self-locking property asserted by Lemma A.8.

This refutes the proof step, not the headline equivalence itself.  A separate
normal-form theorem or a different element-to-set construction would still
be needed to prove the unrestricted Theorem 3.9.
-/

namespace GenLimit.FeedbackQueries
namespace NoFeedbackLockingGap

open GenLimit.Generic
open GenLimit.Angluin

/-- A countably infinite universe with a distinguished infinite left side. -/
abbrev GapUniverse := ℕ ⊕ ℕ

/-- The sole target language in the counterexample. -/
def target : Generic.Language GapUniverse :=
  Set.range Sum.inl

theorem target_infinite : target.Infinite := by
  exact Set.infinite_range_of_injective Sum.inl_injective

/-- The fixed exact presentation used to refute self-locking. -/
def basePresentation : Generic.Stream GapUniverse :=
  fun n => Sum.inl n

theorem basePresentation_presents :
    Generic.Presents basePresentation target :=
  rfl

/-- The exceptional history after the first `n` canonical target elements:
append the later target point `n + 1` instead of the next canonical point
`n`. -/
def spikeHistory (n : ℕ) : List GapUniverse :=
  List.ofFn (fun i : Fin n => Sum.inl i.val) ++ [Sum.inl (n + 1)]

@[simp] theorem spikeHistory_length (n : ℕ) :
    (spikeHistory n).length = n + 1 := by
  simp [spikeHistory]

/-- A finite tuple is exceptional exactly when its list form is one of the
spike histories. -/
def IsSpike {t : ℕ} (samples : Fin t → GapUniverse) : Prop :=
  ∃ n, List.ofFn samples = spikeHistory n

/-- Distinct spike histories are prefix-incomparable. -/
theorem not_spikeHistory_prefix_of_lt
    {n m : ℕ} (hnm : n < m) :
    ¬ spikeHistory n <+: spikeHistory m := by
  intro hprefix
  have hget :=
    (List.prefix_iff_getElem.mp hprefix).2 n (by simp)
  simp [spikeHistory, hnm] at hget

/-- If two prefixes of one stream are spikes, their times coincide. -/
theorem spike_time_unique
    (stream : Generic.Stream GapUniverse)
    {s t : ℕ}
    (hs : IsSpike (fun i : Fin s => stream i))
    (ht : IsSpike (fun i : Fin t => stream i)) :
    s = t := by
  by_contra hne
  rcases hs with ⟨n, hn⟩
  rcases ht with ⟨m, hm⟩
  have hsn : s = n + 1 := by
    have hlen := congrArg List.length hn
    simpa using hlen
  have htm : t = m + 1 := by
    have hlen := congrArg List.length hm
    simpa using hlen
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hprefix := GenLimit.textPrefix_prefix stream (Nat.le_of_lt hst)
    rw [GenLimit.textPrefix_eq_ofFn stream s,
      GenLimit.textPrefix_eq_ofFn stream t, hn, hm] at hprefix
    exact not_spikeHistory_prefix_of_lt (by omega) hprefix
  · have hprefix := GenLimit.textPrefix_prefix stream (Nat.le_of_lt hts)
    rw [GenLimit.textPrefix_eq_ofFn stream t,
      GenLimit.textPrefix_eq_ofFn stream s, hm, hn] at hprefix
    exact not_spikeHistory_prefix_of_lt (by omega) hprefix

/-- The counterexample generator: emit one fixed invalid right-side point on
a spike history, and otherwise choose a fresh target point. -/
noncomputable def generator : Generator GapUniverse := by
  classical
  exact fun _ samples =>
    if IsSpike samples then Sum.inr 0
    else GenLimit.Support.freshFromInfinite
      target target_infinite (sequenceSample samples)

private theorem right_zero_not_mem_spikeHistory (n : ℕ) :
    Sum.inr 0 ∉ spikeHistory n := by
  simp [spikeHistory]

theorem generator_everywhereFresh : EverywhereFresh generator := by
  classical
  intro t samples
  by_cases hspike : IsSpike samples
  · simp only [generator, hspike, if_true]
    intro hmem
    obtain ⟨i, hi⟩ := mem_sequenceSample_iff.mp hmem
    obtain ⟨n, hn⟩ := hspike
    have hlist : Sum.inr 0 ∈ List.ofFn samples :=
      List.mem_ofFn.mpr ⟨i, hi⟩
    rw [hn] at hlist
    exact right_zero_not_mem_spikeHistory n hlist
  · simp only [generator, hspike, if_false]
    exact GenLimit.Support.freshFromInfinite_not_mem
      target target_infinite (sequenceSample samples)

theorem generator_correct_of_not_spike
    (stream : Generic.Stream GapUniverse) (t : ℕ)
    (hspike : ¬IsSpike (fun i : Fin t => stream i)) :
    Generic.CorrectAt generator target stream t := by
  constructor
  · change generator t (fun i => stream i) ∈ target
    simp only [generator, hspike, if_false]
    exact GenLimit.Support.freshFromInfinite_mem
      target target_infinite (sequenceSample fun i : Fin t => stream i)
  · change generator t (fun i => stream i) ∉ Generic.sample stream t
    rw [← sequenceSample_prefix]
    exact generator_everywhereFresh t (fun i => stream i)

/-- The generator makes at most one error on every stream, so it generates
the singleton target class in the ordinary element-based KM model. -/
theorem generator_isLimitGenerator :
    IsLimitGenerator generator ({target} : Generic.LanguageClass GapUniverse) := by
  intro L hL stream _hpresents
  have htarget : L = target := by simpa using hL
  subst L
  by_cases hexists : ∃ t, IsSpike (fun i : Fin t => stream i)
  · obtain ⟨t₀, ht₀⟩ := hexists
    refine ⟨t₀ + 1, ?_⟩
    intro t ht
    apply generator_correct_of_not_spike
    intro htSpike
    have heq := spike_time_unique stream ht₀ htSpike
    omega
  · push_neg at hexists
    exact ⟨0, fun t _ => generator_correct_of_not_spike stream t (hexists t)⟩

theorem base_prefix_append_eq_spikeHistory (n : ℕ) :
    GenLimit.textPrefix basePresentation n ++ [Sum.inl (n + 1)] =
      spikeHistory n := by
  rw [GenLimit.textPrefix_eq_ofFn]
  rfl

/-- Every prefix of the fixed presentation has a target continuation ending
at a spike, so no prefix self-locks. -/
theorem base_prefix_not_selfLocking (n : ℕ) :
    ¬IsSelfLockingHistory generator target
      (GenLimit.textPrefix basePresentation n) := by
  intro hlock
  let tail : List GapUniverse := [Sum.inl (n + 1)]
  have htail : ListWithin tail target := by
    intro x hx
    simp only [tail, List.mem_singleton] at hx
    subst x
    exact ⟨n + 1, rfl⟩
  have hcorrect := hlock.2 tail htail
  have hspike :
      IsSpike
        (GenLimit.textPrefix basePresentation n ++ tail).get := by
    refine ⟨n, ?_⟩
    rw [List.ofFn_get]
    exact base_prefix_append_eq_spikeHistory n
  have hbad :
      noFeedbackOutputOnList generator
        (GenLimit.textPrefix basePresentation n ++ tail) = Sum.inr 0 := by
    simp [noFeedbackOutputOnList, generator, hspike]
  have hmem := hcorrect.1
  rw [hbad] at hmem
  simp [target] at hmem

/-- Kernel-checked refutation of the unrestricted Appendix Lemma A.8
inference: this fresh successful generator has a presentation with no
self-locking prefix. -/
theorem appendix_A_8_not_derivable :
    IsLimitGenerator generator
        ({target} : Generic.LanguageClass GapUniverse) ∧
      EverywhereFresh generator ∧
      Generic.Presents basePresentation target ∧
      ¬∃ n, IsSelfLockingHistory generator target
        (GenLimit.textPrefix basePresentation n) := by
  refine ⟨generator_isLimitGenerator, generator_everywhereFresh,
    basePresentation_presents, ?_⟩
  push_neg
  exact base_prefix_not_selfLocking

end NoFeedbackLockingGap
end GenLimit.FeedbackQueries
