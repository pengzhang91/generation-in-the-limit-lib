import GenLimit.Paper06_NoisyExamples.NonuniformDefinitions
import GenLimit.Core.ClassGeneration
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Set.Countable

/-!
# #06 Noisy Examples: robustifying a non-uniform noiseless generator

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Algorithm 1 and Theorem 3.9.

The source algorithm discards an initial portion of each history until the
remaining suffix contains roughly half of all distinct observations.  It then
repeatedly invokes the noiseless generator on that suffix, appending each
generated point, until one of the generated points is absent from the full
observed history.  The development first proves this candidate argument for
the rounding-stable condition `totalDistinct ≤ 2 * suffixDistinct`.  It then
implements the paper's literal rule, exact suffix cardinality
`⌊totalDistinct / 2⌋`; the declaration `theorem_3_9` uses that literal
Algorithm 1.
-/

namespace GenLimit.NoisyExamples

/-- Once a noiseless non-uniform generator is past its target-specific
threshold, it is correct on every finite positive history, not merely on
histories presented as part of a preselected stream. -/
theorem nonuniform_generator_correct_on_finite_history
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (history : List α)
    (hhistory : (↑history.toFinset : Set α) ⊆ L)
    (hcard : d ≤ history.toFinset.card) :
    Q history.length history.get ∈ L \ (history.toFinset : Set α) := by
  classical
  obtain ⟨fallback, hfallback⟩ := hLInfinite.nonempty
  let stream := GenLimit.Generic.historyThenFallback history fallback
  have hstream : GenLimit.Generic.StreamIn stream L := by
    rintro x ⟨n, rfl⟩
    by_cases hn : n < history.length
    · apply hhistory
      change stream n ∈ history.toFinset
      rw [List.mem_toFinset, List.mem_iff_get]
      exact ⟨⟨n, hn⟩,
        by simp [stream, GenLimit.Generic.historyThenFallback, hn]⟩
    · simpa [stream, GenLimit.Generic.historyThenFallback, hn] using hfallback
  have hfull : GenLimit.Generic.sample stream history.length =
      history.toFinset :=
    GenLimit.Generic.sample_historyThenFallback_length history fallback
  have hdatEnd : d ≤ (GenLimit.Generic.sample stream history.length).card := by
    rw [hfull]
    exact hcard
  obtain ⟨r, hrEnd, hr⟩ :=
    GenLimit.Generic.exists_sample_card_eq_of_le hdatEnd
  have hcorrect := hd stream hstream r hr history.length hrEnd
  have houtput : GenLimit.Generic.output Q stream history.length =
      Q history.length history.get := by
    unfold GenLimit.Generic.output
    apply congrArg (Q history.length)
    funext i
    simp [stream, GenLimit.Generic.historyThenFallback, i.isLt]
  change GenLimit.Generic.output Q stream history.length ∈ L ∧
    GenLimit.Generic.output Q stream history.length ∉
      GenLimit.Generic.sample stream history.length at hcorrect
  rw [houtput, hfull] at hcorrect
  exact hcorrect

/-- Starting from `base`, append `j` successive outputs of `Q`, each computed
on the entire list accumulated so far. -/
noncomputable def iteratedGeneratorHistory
    (Q : GenLimit.Generic.Generator α) (base : List α) : ℕ → List α
  | 0 => base
  | j + 1 =>
      let previous := iteratedGeneratorHistory Q base j
      previous ++ [Q previous.length previous.get]

theorem iteratedGeneratorHistory_zero
    (Q : GenLimit.Generic.Generator α) (base : List α) :
    iteratedGeneratorHistory Q base 0 = base := rfl

theorem iteratedGeneratorHistory_succ
    (Q : GenLimit.Generic.Generator α) (base : List α) (j : ℕ) :
    iteratedGeneratorHistory Q base (j + 1) =
      let previous := iteratedGeneratorHistory Q base j
      previous ++ [Q previous.length previous.get] := rfl

theorem iteratedGeneratorHistory_length
    (Q : GenLimit.Generic.Generator α) (base : List α) (j : ℕ) :
    (iteratedGeneratorHistory Q base j).length = base.length + j := by
  induction j with
  | zero => simp [iteratedGeneratorHistory]
  | succ j ih => simp [iteratedGeneratorHistory, ih, Nat.add_assoc]

/-- Iteration preserves positivity and appends exactly one new distinct point
at each step once the base history is past the noiseless threshold. -/
theorem iteratedGeneratorHistory_properties
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (base : List α) (hbase : (↑base.toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤ base.toFinset.card) :
    ∀ j : ℕ,
      (↑(iteratedGeneratorHistory Q base j).toFinset : Set α) ⊆ L ∧
      base.toFinset ⊆ (iteratedGeneratorHistory Q base j).toFinset ∧
      (iteratedGeneratorHistory Q base j).toFinset.card =
        base.toFinset.card + j := by
  classical
  intro j
  induction j with
  | zero =>
      exact ⟨by simpa [iteratedGeneratorHistory] using hbase,
        by simp [iteratedGeneratorHistory], by simp [iteratedGeneratorHistory]⟩
  | succ j ih =>
      let previous := iteratedGeneratorHistory Q base j
      let z := Q previous.length previous.get
      have hpreviousCard : d ≤ previous.toFinset.card := by
        exact hbaseCard.trans (Finset.card_le_card ih.2.1)
      have hz := nonuniform_generator_correct_on_finite_history
        hLInfinite hd previous ih.1 hpreviousCard
      have hstep : iteratedGeneratorHistory Q base (j + 1) =
          previous ++ [z] := by rfl
      constructor
      · intro x hx
        change x ∈ (iteratedGeneratorHistory Q base (j + 1)).toFinset at hx
        rw [List.mem_toFinset] at hx
        simp only [hstep, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · apply ih.1
          change x ∈ (iteratedGeneratorHistory Q base j).toFinset
          rw [List.mem_toFinset]
          exact hx
        · exact hz.1
      constructor
      · intro x hx
        rw [hstep, List.toFinset_append]
        exact Finset.mem_union_left _ (ih.2.1 hx)
      · have hfinsetStep :
            (iteratedGeneratorHistory Q base (j + 1)).toFinset =
              insert z previous.toFinset := by
          ext x
          simp [hstep]
        rw [hfinsetStep, Finset.card_insert_of_notMem hz.2, ih.2.2]
        omega

/-! ## Balanced suffixes -/

noncomputable def balancedSuffixIndices [DecidableEq α]
    {t : ℕ} (history : Fin t → α) : Finset ℕ :=
  (Finset.range (t + 1)).filter fun r ↦
    (List.ofFn history).toFinset.card ≤
      2 * ((List.ofFn history).drop r).toFinset.card

theorem mem_balancedSuffixIndices_iff [DecidableEq α]
    {t : ℕ} {history : Fin t → α} {r : ℕ} :
    r ∈ balancedSuffixIndices history ↔
      r ≤ t ∧ (List.ofFn history).toFinset.card ≤
        2 * ((List.ofFn history).drop r).toFinset.card := by
  simp [balancedSuffixIndices, Nat.lt_succ_iff]

theorem balancedSuffixIndices_nonempty [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    (balancedSuffixIndices history).Nonempty := by
  refine ⟨0, ?_⟩
  apply mem_balancedSuffixIndices_iff.mpr
  simp only [Nat.zero_le, List.drop_zero, true_and]
  omega

/-- The latest suffix retaining at least half of the distinct observations. -/
noncomputable def balancedSuffixStart [DecidableEq α]
    {t : ℕ} (history : Fin t → α) : ℕ :=
  (balancedSuffixIndices history).max'
    (balancedSuffixIndices_nonempty history)

theorem balancedSuffixStart_mem [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    balancedSuffixStart history ∈ balancedSuffixIndices history :=
  Finset.max'_mem _ _

theorem balancedSuffixStart_le_length [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    balancedSuffixStart history ≤ t :=
  (mem_balancedSuffixIndices_iff.mp (balancedSuffixStart_mem history)).1

theorem balancedSuffixStart_balance [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    (List.ofFn history).toFinset.card ≤
      2 * ((List.ofFn history).drop
        (balancedSuffixStart history)).toFinset.card :=
  (mem_balancedSuffixIndices_iff.mp (balancedSuffixStart_mem history)).2

theorem le_balancedSuffixStart [DecidableEq α]
    {t : ℕ} {history : Fin t → α} {r : ℕ}
    (hr : r ∈ balancedSuffixIndices history) :
    r ≤ balancedSuffixStart history :=
  Finset.le_max' _ _ hr

private theorem history_toFinset_eq_take_union_drop [DecidableEq α]
    (history : List α) (r : ℕ) :
    history.toFinset = (history.take r).toFinset ∪ (history.drop r).toFinset := by
  rw [← List.toFinset_append, List.take_append_drop]

theorem history_card_le_start_add_suffix [DecidableEq α]
    (history : List α) (r : ℕ) :
    history.toFinset.card ≤ r + (history.drop r).toFinset.card := by
  calc
    history.toFinset.card =
        ((history.take r).toFinset ∪ (history.drop r).toFinset).card := by
      rw [history_toFinset_eq_take_union_drop]
    _ ≤ (history.take r).toFinset.card + (history.drop r).toFinset.card :=
      Finset.card_union_le _ _
    _ ≤ (history.take r).length + (history.drop r).toFinset.card :=
      Nat.add_le_add_right (List.toFinset_card_le _) _
    _ ≤ r + (history.drop r).toFinset.card := by
      exact Nat.add_le_add_right (List.length_take_le r history) _

/-- If the total history has at least twice as many distinct observations as
an index `r`, then the latest balanced suffix begins no earlier than `r`. -/
theorem start_le_balancedSuffixStart_of_large [DecidableEq α]
    {t : ℕ} {history : Fin t → α} {r : ℕ}
    (hlarge : 2 * r ≤ (List.ofFn history).toFinset.card) :
    r ≤ balancedSuffixStart history := by
  have hrt : r ≤ t := by
    have hcardLength : (List.ofFn history).toFinset.card ≤ t := by
      simpa using List.toFinset_card_le (List.ofFn history)
    omega
  have hbound := history_card_le_start_add_suffix (List.ofFn history) r
  have hsuffix : r ≤ ((List.ofFn history).drop r).toFinset.card := by
    omega
  apply le_balancedSuffixStart
  apply mem_balancedSuffixIndices_iff.mpr
  constructor
  · exact hrt
  · omega

/-! ### The paper's exact floor-based suffix

The preceding `balancedSuffixStart` is a rounding-stable variant convenient
for the first implementation.  Algorithm 1 literally asks for a suffix with
exactly `⌊d_t/2⌋` distinct observations.  The declarations below implement
that exact choice. -/

private theorem exists_drop_toFinset_card_eq [DecidableEq α]
    (history : List α) {k : ℕ} (hk : k ≤ history.toFinset.card) :
    ∃ r ≤ history.length, (history.drop r).toFinset.card = k := by
  induction history with
  | nil =>
      have hk0 : k = 0 := by simpa using hk
      exact ⟨0, by simp, by simp [hk0]⟩
  | cons x xs ih =>
      by_cases hfull : k = (x :: xs).toFinset.card
      · exact ⟨0, by simp, by simp [hfull]⟩
      · have hklt : k < (x :: xs).toFinset.card :=
          lt_of_le_of_ne hk hfull
        have hstep :
            (x :: xs).toFinset.card ≤ xs.toFinset.card + 1 := by
          rw [List.toFinset_cons]
          exact Finset.card_insert_le _ _
        have hkxs : k ≤ xs.toFinset.card := by omega
        obtain ⟨r, hr, hcard⟩ := ih hkxs
        exact ⟨r + 1, by simp; omega, by simpa using hcard⟩

noncomputable def paperBalancedSuffixIndices [DecidableEq α]
    {t : ℕ} (history : Fin t → α) : Finset ℕ :=
  (Finset.range (t + 1)).filter fun r ↦
    ((List.ofFn history).drop r).toFinset.card =
      (List.ofFn history).toFinset.card / 2

theorem mem_paperBalancedSuffixIndices_iff [DecidableEq α]
    {t : ℕ} {history : Fin t → α} {r : ℕ} :
    r ∈ paperBalancedSuffixIndices history ↔
      r ≤ t ∧
      ((List.ofFn history).drop r).toFinset.card =
        (List.ofFn history).toFinset.card / 2 := by
  simp [paperBalancedSuffixIndices, Nat.lt_succ_iff]

theorem paperBalancedSuffixIndices_nonempty [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    (paperBalancedSuffixIndices history).Nonempty := by
  obtain ⟨r, hr, hcard⟩ :=
    exists_drop_toFinset_card_eq (List.ofFn history)
      (Nat.div_le_self _ 2)
  exact ⟨r, mem_paperBalancedSuffixIndices_iff.mpr
    ⟨by simpa using hr, hcard⟩⟩

/-- The literal zero-based form of Algorithm 1's `r_t`: this is the latest
number of observations to discard while leaving exactly
`⌊d_t/2⌋` distinct observations.  The paper's one-based index is one more
than this value. -/
noncomputable def paperBalancedSuffixStart [DecidableEq α]
    {t : ℕ} (history : Fin t → α) : ℕ :=
  (paperBalancedSuffixIndices history).max'
    (paperBalancedSuffixIndices_nonempty history)

theorem paperBalancedSuffixStart_mem [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    paperBalancedSuffixStart history ∈
      paperBalancedSuffixIndices history :=
  Finset.max'_mem _ _

theorem paperBalancedSuffixStart_le_length [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    paperBalancedSuffixStart history ≤ t :=
  (mem_paperBalancedSuffixIndices_iff.mp
    (paperBalancedSuffixStart_mem history)).1

theorem paperBalancedSuffixStart_card [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    ((List.ofFn history).drop
      (paperBalancedSuffixStart history)).toFinset.card =
        (List.ofFn history).toFinset.card / 2 :=
  (mem_paperBalancedSuffixIndices_iff.mp
    (paperBalancedSuffixStart_mem history)).2

theorem le_paperBalancedSuffixStart [DecidableEq α]
    {t : ℕ} {history : Fin t → α} {r : ℕ}
    (hr : r ∈ paperBalancedSuffixIndices history) :
    r ≤ paperBalancedSuffixStart history :=
  Finset.le_max' _ _ hr

/-- Once the total number of distinct observations is at least `2r`, the
latest exact-floor suffix begins no earlier than `r`. -/
theorem start_le_paperBalancedSuffixStart_of_large [DecidableEq α]
    {t : ℕ} {history : Fin t → α} {r : ℕ}
    (hlarge : 2 * r ≤ (List.ofFn history).toFinset.card) :
    r ≤ paperBalancedSuffixStart history := by
  let full := List.ofFn history
  let k := full.toFinset.card / 2
  have hlarge' : 2 * r ≤ full.toFinset.card := by
    simpa [full] using hlarge
  have hrt : r ≤ full.length := by
    have hcardLength : full.toFinset.card ≤ full.length :=
      List.toFinset_card_le full
    omega
  have hbound := history_card_le_start_add_suffix full r
  have hksuffix : k ≤ (full.drop r).toFinset.card := by
    dsimp [k]
    omega
  obtain ⟨q, hq, hqcard⟩ :=
    exists_drop_toFinset_card_eq (full.drop r) hksuffix
  have hrq : r + q ≤ t := by
    have hdropLength : (full.drop r).length = full.length - r :=
      List.length_drop
    have hfullLength : full.length = t := by simp [full]
    rw [hdropLength, hfullLength] at hq
    omega
  apply (Nat.le_add_right r q).trans
  apply le_paperBalancedSuffixStart (r := r + q)
  apply mem_paperBalancedSuffixIndices_iff.mpr
  refine ⟨hrq, ?_⟩
  simpa [full, k, List.drop_drop, Nat.add_comm] using hqcard

/-- A finite noise set has a time after which every observation is positive. -/
noncomputable def finiteNoiseCutoff
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hnoise : HasFiniteNoise stream L) : ℕ :=
  hnoise.toFinset.sup id + 1

theorem mem_target_after_finiteNoiseCutoff
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hnoise : HasFiniteNoise stream L) {t : ℕ}
    (ht : finiteNoiseCutoff hnoise ≤ t) :
    stream t ∈ L := by
  classical
  by_contra htL
  have htF : t ∈ hnoise.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact htL
  have htSup : t ≤ hnoise.toFinset.sup id :=
    Finset.le_sup (f := id) htF
  unfold finiteNoiseCutoff at ht
  omega

theorem balanced_suffix_positive_after_cutoff [DecidableEq α]
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hnoise : HasFiniteNoise stream L) {t r : ℕ}
    (hr : finiteNoiseCutoff hnoise ≤ r) :
    (↑((List.ofFn (fun i : Fin t ↦ stream i)).drop r).toFinset : Set α)
      ⊆ L := by
  intro x hx
  change x ∈ ((List.ofFn (fun i : Fin t ↦ stream i)).drop r).toFinset at hx
  rw [List.mem_toFinset, List.mem_drop_iff_getElem] at hx
  obtain ⟨j, hj, hjx⟩ := hx
  have hvalue :
      (List.ofFn (fun i : Fin t ↦ stream i))[r + j] = stream (r + j) := by
    simp
  rw [hvalue] at hjx
  rw [← hjx]
  apply mem_target_after_finiteNoiseCutoff hnoise
  omega

/-! ## Candidate selection and the robustified generator -/

noncomputable def generatedCandidateSet [DecidableEq α]
    (Q : GenLimit.Generic.Generator α) (base : List α) (count : ℕ) :
    Finset α :=
  (iteratedGeneratorHistory Q base count).toFinset \ base.toFinset

theorem generatedCandidateSet_card
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (base : List α) (hbase : (↑base.toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤ base.toFinset.card) (count : ℕ) :
    (generatedCandidateSet Q base count).card = count := by
  have hprops := iteratedGeneratorHistory_properties
    hLInfinite hd base hbase hbaseCard count
  unfold generatedCandidateSet
  rw [Finset.card_sdiff_of_subset hprops.2.1, hprops.2.2]
  omega

theorem generatedCandidateSet_positive
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (base : List α) (hbase : (↑base.toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤ base.toFinset.card) (count : ℕ) :
    (↑(generatedCandidateSet Q base count) : Set α) ⊆ L := by
  intro x hx
  exact (iteratedGeneratorHistory_properties
    hLInfinite hd base hbase hbaseCard count).1
      (Finset.mem_sdiff.mp hx).1

theorem generatedCandidateSet_disjoint_base [DecidableEq α]
    (Q : GenLimit.Generic.Generator α) (base : List α) (count : ℕ) :
    Disjoint (generatedCandidateSet Q base count) base.toFinset := by
  exact Finset.disjoint_left.mpr fun _ hx ↦ (Finset.mem_sdiff.mp hx).2

/-- With `r+1` fresh generated candidates and only `r` earlier history
positions before the suffix, at least one candidate is absent from the full
history. -/
theorem generatedCandidate_not_in_history
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (history : List α) (r : ℕ)
    (hbase : (↑(history.drop r).toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤ (history.drop r).toFinset.card) :
    (generatedCandidateSet Q (history.drop r) (r + 1) \
      history.toFinset).Nonempty := by
  classical
  let candidates := generatedCandidateSet Q (history.drop r) (r + 1)
  by_contra hempty
  have hsubsetCurrent : candidates ⊆ history.toFinset := by
    intro x hx
    by_contra hxCurrent
    have : x ∈ candidates \ history.toFinset :=
      Finset.mem_sdiff.mpr ⟨hx, hxCurrent⟩
    exact hempty ⟨x, this⟩
  have hsubsetPrefix : candidates ⊆ (history.take r).toFinset := by
    intro x hx
    have hxCurrent := hsubsetCurrent hx
    rw [history_toFinset_eq_take_union_drop] at hxCurrent
    rcases Finset.mem_union.mp hxCurrent with hxPrefix | hxBase
    · exact hxPrefix
    · exact False.elim ((Finset.mem_sdiff.mp hx).2 hxBase)
  have hcandidateCard : candidates.card = r + 1 :=
    generatedCandidateSet_card hLInfinite hd (history.drop r)
      hbase hbaseCard (r + 1)
  have hprefixCard : (history.take r).toFinset.card ≤ r :=
    (List.toFinset_card_le _).trans (List.length_take_le r history)
  have := Finset.card_le_card hsubsetPrefix
  omega

/-- Algorithm 1, represented as a total generator. -/
noncomputable def robustifiedNoiselessGenerator
    [DecidableEq α] [Nonempty α]
    (Q : GenLimit.Generic.Generator α) : GenLimit.Generic.Generator α :=
  fun _ history ↦
    let observed := (List.ofFn history).toFinset
    let r := balancedSuffixStart history
    let base := (List.ofFn history).drop r
    let candidates := generatedCandidateSet Q base (r + 1) \ observed
    if h : candidates.Nonempty then Classical.choose h
    else Classical.choice inferInstance

theorem robustifiedNoiselessGenerator_correct
    [DecidableEq α] [Nonempty α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d t : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ q, (GenLimit.Generic.sample stream q).card = d →
        ∀ s, q ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (history : Fin t → α)
    (hbase :
      (↑((List.ofFn history).drop (balancedSuffixStart history)).toFinset :
        Set α) ⊆ L)
    (hbaseCard : d ≤
      ((List.ofFn history).drop (balancedSuffixStart history)).toFinset.card) :
    robustifiedNoiselessGenerator Q t history ∈ L \
      ((List.ofFn history).toFinset : Set α) := by
  classical
  let r := balancedSuffixStart history
  let base := (List.ofFn history).drop r
  let candidates := generatedCandidateSet Q base (r + 1) \
    (List.ofFn history).toFinset
  have hCandidates : candidates.Nonempty := by
    exact generatedCandidate_not_in_history hLInfinite hd
      (List.ofFn history) r hbase hbaseCard
  have hout : robustifiedNoiselessGenerator Q t history =
      Classical.choose hCandidates := by
    simp only [robustifiedNoiselessGenerator, r, base, candidates,
      dif_pos hCandidates]
  have hchosen := Classical.choose_spec hCandidates
  rw [hout]
  constructor
  · apply generatedCandidateSet_positive hLInfinite hd base hbase hbaseCard
    exact (Finset.mem_sdiff.mp hchosen).1
  · exact (Finset.mem_sdiff.mp hchosen).2

/-- Algorithm 1 with the paper's literal floor-based suffix rule. -/
noncomputable def paperRobustifiedNoiselessGenerator
    [DecidableEq α] [Nonempty α]
    (Q : GenLimit.Generic.Generator α) : GenLimit.Generic.Generator α :=
  fun _ history ↦
    let observed := (List.ofFn history).toFinset
    let r := paperBalancedSuffixStart history
    let base := (List.ofFn history).drop r
    let candidates := generatedCandidateSet Q base (r + 1) \ observed
    if h : candidates.Nonempty then Classical.choose h
    else Classical.choice inferInstance

theorem paperRobustifiedNoiselessGenerator_correct
    [DecidableEq α] [Nonempty α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d t : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ q, (GenLimit.Generic.sample stream q).card = d →
        ∀ s, q ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (history : Fin t → α)
    (hbase :
      (↑((List.ofFn history).drop
        (paperBalancedSuffixStart history)).toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤
      ((List.ofFn history).drop
        (paperBalancedSuffixStart history)).toFinset.card) :
    paperRobustifiedNoiselessGenerator Q t history ∈ L \
      ((List.ofFn history).toFinset : Set α) := by
  classical
  let r := paperBalancedSuffixStart history
  let base := (List.ofFn history).drop r
  let candidates := generatedCandidateSet Q base (r + 1) \
    (List.ofFn history).toFinset
  have hCandidates : candidates.Nonempty := by
    exact generatedCandidate_not_in_history hLInfinite hd
      (List.ofFn history) r hbase hbaseCard
  have hout : paperRobustifiedNoiselessGenerator Q t history =
      Classical.choose hCandidates := by
    simp only [paperRobustifiedNoiselessGenerator, r, base, candidates,
      dif_pos hCandidates]
  have hchosen := Classical.choose_spec hCandidates
  rw [hout]
  constructor
  · apply generatedCandidateSet_positive hLInfinite hd base hbase hbaseCard
    exact (Finset.mem_sdiff.mp hchosen).1
  · exact (Finset.mem_sdiff.mp hchosen).2

/-! ## Eventual correctness on every noisy presentation -/

/-- Along a noisy presentation, the balanced suffix eventually starts after
the last noisy occurrence and contains at least any prescribed finite number
of distinct positive examples.  This is the global convergence assertion
used (but not isolated) in the proof of Theorem 3.9. -/
theorem eventually_balanced_suffix_positive_and_large
    [DecidableEq α]
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hLInfinite : L.Infinite)
    (hP : NoisyPresentation stream L)
    (d : ℕ) :
    ∃ T : ℕ, ∀ s, T ≤ s →
      let history : Fin s → α := fun i ↦ stream i
      (↑((List.ofFn history).drop
          (balancedSuffixStart history)).toFinset : Set α) ⊆ L ∧
      d ≤ ((List.ofFn history).drop
          (balancedSuffixStart history)).toFinset.card := by
  classical
  let cutoff := finiteNoiseCutoff hP.2
  let targetCard := 2 * max cutoff d
  obtain ⟨T, hTcard⟩ := exists_sample_card_eq_of_range_infinite
    (noisyPresentation_range_infinite hLInfinite hP) targetCard
  refine ⟨T, ?_⟩
  intro s hTs
  let history : Fin s → α := fun i ↦ stream i
  have hhistorySample :
      (List.ofFn history).toFinset =
        GenLimit.Generic.sample stream s := by
    ext x
    simp only [List.mem_toFinset, List.mem_ofFn,
      GenLimit.Generic.mem_sample_iff, history]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, i.isLt, hi⟩
    · rintro ⟨i, hi, hix⟩
      exact ⟨⟨i, hi⟩, hix⟩
  have hsampleMono :
      GenLimit.Generic.sample stream T ⊆
        GenLimit.Generic.sample stream s :=
    GenLimit.Generic.sample_mono hTs
  have htotalLower :
      targetCard ≤ (List.ofFn history).toFinset.card := by
    have hcardMono :
        (GenLimit.Generic.sample stream T).card ≤
          (GenLimit.Generic.sample stream s).card :=
      Finset.card_le_card hsampleMono
    rw [hTcard] at hcardMono
    rwa [hhistorySample]
  have hcutoffLarge :
      2 * cutoff ≤ (List.ofFn history).toFinset.card := by
    have : cutoff ≤ max cutoff d := Nat.le_max_left _ _
    omega
  have hstart :
      cutoff ≤ balancedSuffixStart history :=
    start_le_balancedSuffixStart_of_large hcutoffLarge
  have hpositive :
      (↑((List.ofFn history).drop
          (balancedSuffixStart history)).toFinset : Set α) ⊆ L := by
    exact balanced_suffix_positive_after_cutoff hP.2 hstart
  have hbalance := balancedSuffixStart_balance history
  have hdLarge :
      2 * d ≤ (List.ofFn history).toFinset.card := by
    have : d ≤ max cutoff d := Nat.le_max_right _ _
    omega
  have hbaseCard :
      d ≤ ((List.ofFn history).drop
          (balancedSuffixStart history)).toFinset.card := by
    omega
  exact ⟨hpositive, hbaseCard⟩

/-- Eventual global invariant for Algorithm 1's literal floor-based suffix. -/
theorem eventually_paperBalanced_suffix_positive_and_large
    [DecidableEq α]
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hLInfinite : L.Infinite)
    (hP : NoisyPresentation stream L)
    (d : ℕ) :
    ∃ T : ℕ, ∀ s, T ≤ s →
      let history : Fin s → α := fun i ↦ stream i
      (↑((List.ofFn history).drop
          (paperBalancedSuffixStart history)).toFinset : Set α) ⊆ L ∧
      d ≤ ((List.ofFn history).drop
          (paperBalancedSuffixStart history)).toFinset.card := by
  classical
  let cutoff := finiteNoiseCutoff hP.2
  let targetCard := 2 * max cutoff d
  obtain ⟨T, hTcard⟩ := exists_sample_card_eq_of_range_infinite
    (noisyPresentation_range_infinite hLInfinite hP) targetCard
  refine ⟨T, ?_⟩
  intro s hTs
  let history : Fin s → α := fun i ↦ stream i
  have hhistorySample :
      (List.ofFn history).toFinset =
        GenLimit.Generic.sample stream s := by
    ext x
    simp only [List.mem_toFinset, List.mem_ofFn,
      GenLimit.Generic.mem_sample_iff, history]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, i.isLt, hi⟩
    · rintro ⟨i, hi, hix⟩
      exact ⟨⟨i, hi⟩, hix⟩
  have hsampleMono :
      GenLimit.Generic.sample stream T ⊆
        GenLimit.Generic.sample stream s :=
    GenLimit.Generic.sample_mono hTs
  have htotalLower :
      targetCard ≤ (List.ofFn history).toFinset.card := by
    have hcardMono :
        (GenLimit.Generic.sample stream T).card ≤
          (GenLimit.Generic.sample stream s).card :=
      Finset.card_le_card hsampleMono
    rw [hTcard] at hcardMono
    rwa [hhistorySample]
  have hcutoffLarge :
      2 * cutoff ≤ (List.ofFn history).toFinset.card := by
    have : cutoff ≤ max cutoff d := Nat.le_max_left _ _
    omega
  have hstart :
      cutoff ≤ paperBalancedSuffixStart history :=
    start_le_paperBalancedSuffixStart_of_large hcutoffLarge
  have hpositive :
      (↑((List.ofFn history).drop
          (paperBalancedSuffixStart history)).toFinset : Set α) ⊆ L := by
    exact balanced_suffix_positive_after_cutoff hP.2 hstart
  have hcard := paperBalancedSuffixStart_card history
  have hdLarge :
      2 * d ≤ (List.ofFn history).toFinset.card := by
    have : d ≤ max cutoff d := Nat.le_max_right _ _
    omega
  have hbaseCard :
      d ≤ ((List.ofFn history).drop
          (paperBalancedSuffixStart history)).toFinset.card := by
    rw [hcard]
    omega
  exact ⟨hpositive, hbaseCard⟩

/-- Theorem 3.9 (Non-uniform Generatability implies Noisy Generatability in
the Limit).

The formal proof supplies the monotonicity step omitted by the prose:
after one prefix has at least `2 * max cutoff d` distinct observations, every
later prefix does too.  Consequently its latest balanced suffix starts after
the finite-noise cutoff and contains at least the target-specific noiseless
threshold. -/
theorem theorem_3_9 [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hNonuniform : GenLimit.Generic.NonuniformlyGeneratable H) :
    NoisilyGeneratableInLimit H := by
  classical
  obtain ⟨Q, hQ⟩ := hNonuniform
  letI : Nonempty α := ⟨Q 0 Fin.elim0⟩
  refine ⟨paperRobustifiedNoiselessGenerator Q, ?_⟩
  intro L hLH stream hP
  obtain ⟨d, hd⟩ := hQ L hLH
  obtain ⟨T, hT⟩ :=
    eventually_paperBalanced_suffix_positive_and_large
      (hUUS L hLH) hP d
  refine ⟨T, ?_⟩
  intro s hTs
  have hgood := hT s hTs
  have hcorrect := paperRobustifiedNoiselessGenerator_correct
    (hUUS L hLH) hd (fun i : Fin s ↦ stream i) hgood.1 hgood.2
  have hhistorySample :
      (List.ofFn (fun i : Fin s ↦ stream i)).toFinset =
        GenLimit.Generic.sample stream s := by
    ext x
    simp only [List.mem_toFinset, List.mem_ofFn,
      GenLimit.Generic.mem_sample_iff]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, i.isLt, hi⟩
    · rintro ⟨i, hi, hix⟩
      exact ⟨⟨i, hi⟩, hix⟩
  change
    GenLimit.Generic.output (paperRobustifiedNoiselessGenerator Q) stream s ∈ L ∧
      GenLimit.Generic.output (paperRobustifiedNoiselessGenerator Q) stream s ∉
        GenLimit.Generic.sample stream s
  simpa only [GenLimit.Generic.output, hhistorySample] using hcorrect

end GenLimit.NoisyExamples
