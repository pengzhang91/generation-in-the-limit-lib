import GenLimit.Paper18_SafeLanguageGeneration.Padding
import GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions
import GenLimit.Support.FiniteCandidateRace
import GenLimit.Support.LeastCandidate
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Nat.Pairing

/-!
# Safe generation to identification: a prefix-compatible run

This file formalizes the infinite-run issue in Algorithm 1 and Theorem 5.1
of Anastasopoulos--Ateniese--Kornaropoulos,
*Safe Language Generation in the Limit*, arXiv:2601.08648v2.

The printed pseudocode rebuilds a finite labeled set at every outer time and
"feeds" it to the safe generator.  The limit guarantee of a safe generator,
however, applies only along prefixes of one fixed infinite labeled
enumeration.  Here every candidate language is instead assigned one fixed
run.  At outer time `t`, the reduction replays exactly the first `2t`
occurrences of that run.  The theorem `candidateHistory_eq_run_prefix`
kernel-checks the needed prefix compatibility.
-/

namespace GenLimit.SafeGeneration

open GenLimit.Generic

/-! ## Verticalizing a presentation online -/

/-- Diagonal verticalization of a stream.  The pairing schedule ensures that
the `n`th padded occurrence reads only an input position at most `n`. -/
def verticalizedStream
    (stream : Stream α) : Stream (α × ℕ) :=
  fun n => (stream n.unpair.1, n.unpair.2 + 1)

theorem verticalizedStream_presents
    {stream : Stream α} {L : Generic.Language α}
    (hP : Generic.Presents stream L) :
    Generic.Presents (verticalizedStream stream) (verticalPad L) := by
  apply Set.Subset.antisymm
  · rintro p ⟨n, rfl⟩
    refine ⟨?_, Nat.zero_lt_succ _⟩
    rw [← hP]
    exact ⟨n.unpair.1, rfl⟩
  · rintro ⟨x, level⟩ ⟨hxL, hlevel⟩
    rw [← hP] at hxL
    obtain ⟨k, rfl⟩ := hxL
    obtain ⟨r, rfl⟩ : ∃ r, level = r + 1 :=
      ⟨level - 1, (Nat.sub_add_cancel hlevel).symm⟩
    refine ⟨Nat.pair k r, ?_⟩
    simp [verticalizedStream]

/-- The `n`th verticalized occurrence only inspects an original-stream
position no later than `n`. -/
theorem verticalizedStream_source_le (n : ℕ) :
    n.unpair.1 ≤ n :=
  Nat.unpair_left_le n

/-! ## Merging the fixed positive and harmful presentations -/

/-- Alternate between a target-padding presentation (even positions) and a
harmful-padding presentation (odd positions). -/
def taggedInterleave
    (positive negative : Stream α) : Stream (Tagged α) :=
  fun n =>
    if n % 2 = 0 then (positive (n / 2), true)
    else (negative (n / 2), false)

theorem taggedRange_taggedInterleave_true
    (positive negative : Stream α) :
    taggedRange (taggedInterleave positive negative) true =
      Set.range positive := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, hn⟩
    by_cases heven : n % 2 = 0
    · rw [taggedInterleave, if_pos heven] at hn
      exact ⟨n / 2, congrArg Prod.fst hn⟩
    · rw [taggedInterleave, if_neg heven] at hn
      have : false = true := congrArg Prod.snd hn
      simp at this
  · rintro x ⟨n, rfl⟩
    refine ⟨2 * n, ?_⟩
    simp [taggedInterleave]

theorem taggedRange_taggedInterleave_false
    (positive negative : Stream α) :
    taggedRange (taggedInterleave positive negative) false =
      Set.range negative := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, hn⟩
    by_cases heven : n % 2 = 0
    · rw [taggedInterleave, if_pos heven] at hn
      have : true = false := congrArg Prod.snd hn
      simp at this
    · rw [taggedInterleave, if_neg heven] at hn
      exact ⟨n / 2, congrArg Prod.fst hn⟩
  · rintro x ⟨n, rfl⟩
    refine ⟨2 * n + 1, ?_⟩
    change
      (if (2 * n + 1) % 2 = 0 then
          (positive ((2 * n + 1) / 2), true)
        else (negative ((2 * n + 1) / 2), false)) =
        (negative n, false)
    rw [if_neg (by omega)]
    have hdiv : (2 * n + 1) / 2 = n := by omega
    rw [hdiv]

theorem taggedInterleave_labeledPresents
    {positive negative : Stream α}
    {K H : Generic.Language α}
    (hK : Generic.Presents positive K)
    (hH : Generic.Presents negative H) :
    LabeledPresents (taggedInterleave positive negative) K H := by
  constructor
  · rw [taggedRange_taggedInterleave_true, hK]
  · rw [taggedRange_taggedInterleave_false, hH]

/-- The fixed infinite labeled run used for candidate `L_i`: the supplied
positive stream presents its vertical padding, while the harmful half is
derived online from the observed target stream. -/
def candidateRun
    (positivePad : Stream (α × ℕ))
    (targetStream : Stream α) :
    Stream (Tagged (α × ℕ)) :=
  taggedInterleave positivePad (verticalizedStream targetStream)

theorem candidateRun_labeledPresents
    {positivePad : Stream (α × ℕ)}
    {targetStream : Stream α}
    {candidate target : Generic.Language α}
    (hCandidate :
      Generic.Presents positivePad (verticalPad candidate))
    (hTarget : Generic.Presents targetStream target) :
    LabeledPresents (candidateRun positivePad targetStream)
      (verticalPad candidate) (verticalPad target) := by
  exact taggedInterleave_labeledPresents hCandidate
    (verticalizedStream_presents hTarget)

/-! ## Reconstructing the exact run prefix from a finite input history -/

/-- The verticalized occurrence with diagonal index `q`, reconstructed from
a history containing at least the first `q+1` original observations. -/
def verticalizedHistoryValue
    {t : ℕ} (xs : Fin t → α) (q : Fin t) : α × ℕ :=
  (xs ⟨q.val.unpair.1,
      lt_of_le_of_lt (Nat.unpair_left_le q.val) q.isLt⟩,
    q.val.unpair.2 + 1)

/-- At outer time `t`, replay the first `2t` occurrences of the fixed
candidate run.  Every harmful occurrence refers only to the available
history `xs`. -/
def candidateHistory
    (positivePad : Stream (α × ℕ))
    {t : ℕ} (xs : Fin t → α) :
    Fin (2 * t) → Tagged (α × ℕ) :=
  fun n =>
    if heven : n.val % 2 = 0 then
      (positivePad (n.val / 2), true)
    else
      let q : Fin t := ⟨n.val / 2, by
        have hn := n.isLt
        omega⟩
      (verticalizedHistoryValue xs q, false)

theorem candidateHistory_eq_run_prefix
    (positivePad : Stream (α × ℕ))
    (stream : Stream α) (t : ℕ) :
    candidateHistory positivePad (fun k : Fin t => stream k) =
      (fun n : Fin (2 * t) => candidateRun positivePad stream n) := by
  funext n
  by_cases heven : n.val % 2 = 0
  · simp [candidateHistory, candidateRun, taggedInterleave, heven]
  · simp only [candidateHistory, dif_neg heven, candidateRun,
      taggedInterleave, if_neg heven]
    rfl

/-- Replaying `candidateHistory` really queries the safe generator at the
corresponding time on one fixed infinite run. -/
theorem safeOutput_candidateRun_eq_history
    (G : SafeGenerator (α × ℕ))
    (positivePad : Stream (α × ℕ))
    (stream : Stream α) (t : ℕ) :
    safeOutput G (candidateRun positivePad stream) (2 * t) =
      G (2 * t) (candidateHistory positivePad
        (fun k : Fin t => stream k)) := by
  rw [safeOutput, candidateHistory_eq_run_prefix]

/-- The source's vertical-padding dichotomy, now attached to an actual
prefix-compatible labeled run. -/
theorem candidateRun_safe_difference_dichotomy
    {positivePad : Stream (α × ℕ)}
    {stream : Stream α}
    {candidate target : Generic.Language α}
    (hCandidate :
      Generic.Presents positivePad (verticalPad candidate))
    (hTarget : Generic.Presents stream target) :
    LabeledPresents (candidateRun positivePad stream)
        (verticalPad candidate) (verticalPad target) ∧
      ((candidate \ target).Nonempty →
        (verticalPad candidate \ verticalPad target).Infinite) ∧
      (candidate ⊆ target →
        (verticalPad candidate \ verticalPad target).Finite) := by
  refine ⟨candidateRun_labeledPresents hCandidate hTarget, ?_, ?_⟩
  · exact fun h =>
      (verticalPad_diff_infinite_iff_nonempty candidate target).mpr h
  · intro hsub
    have hempty : candidate \ target = ∅ :=
      Set.diff_eq_empty.mpr hsub
    rw [verticalPad_diff, hempty]
    have hpadEmpty : verticalPad (∅ : Set α) = ∅ := by
      ext p
      simp [verticalPad]
    rw [hpadEmpty]
    exact Set.finite_empty

/-- Along the replayed finite histories, a safe generator eventually emits
`none` when the candidate is contained in the target. -/
theorem candidateHistory_eventually_none
    {G : SafeGenerator (α × ℕ)}
    {positivePad : Stream (α × ℕ)}
    {stream : Stream α}
    {candidate target : Generic.Language α}
    (hCandidate :
      Generic.Presents positivePad (verticalPad candidate))
    (hTarget : Generic.Presents stream target)
    (hSafe :
      SafelyGenerates G (verticalPad candidate) (verticalPad target)
        (candidateRun positivePad stream))
    (hsub : candidate ⊆ target) :
    ∃ T, ∀ t, T ≤ t →
      G (2 * t) (candidateHistory positivePad
        (fun k : Fin t => stream k)) = none := by
  have hfinite :
      (verticalPad candidate \ verticalPad target).Finite :=
    (candidateRun_safe_difference_dichotomy hCandidate hTarget).2.2 hsub
  obtain ⟨T, hT⟩ := hSafe.2 hfinite
  refine ⟨T, ?_⟩
  intro t hTt
  have hTtwo : T ≤ 2 * t := by omega
  calc
    G (2 * t) (candidateHistory positivePad
        (fun k : Fin t => stream k)) =
        safeOutput G (candidateRun positivePad stream) (2 * t) :=
      (safeOutput_candidateRun_eq_history G positivePad stream t).symm
    _ = none := (hT (2 * t) hTtwo).2

/-- Along the same fixed run, a strict superset candidate eventually emits a
non-bottom value. -/
theorem candidateHistory_eventually_some
    {G : SafeGenerator (α × ℕ)}
    {positivePad : Stream (α × ℕ)}
    {stream : Stream α}
    {candidate target : Generic.Language α}
    (hCandidate :
      Generic.Presents positivePad (verticalPad candidate))
    (hTarget : Generic.Presents stream target)
    (hSafe :
      SafelyGenerates G (verticalPad candidate) (verticalPad target)
        (candidateRun positivePad stream))
    (hstrict : (candidate \ target).Nonempty) :
    ∃ T, ∀ t, T ≤ t →
      ∃ x, G (2 * t) (candidateHistory positivePad
        (fun k : Fin t => stream k)) = some x := by
  have hinfinite :
      (verticalPad candidate \ verticalPad target).Infinite :=
    (candidateRun_safe_difference_dichotomy hCandidate hTarget).2.1 hstrict
  obtain ⟨T, hT⟩ := hSafe.1 hinfinite
  refine ⟨T, ?_⟩
  intro t hTt
  have hTtwo : T ≤ 2 * t := by omega
  obtain ⟨x, hx, -, -⟩ :=
    hT (2 * t) hTtwo
  refine ⟨x, ?_⟩
  calc
    G (2 * t) (candidateHistory positivePad
        (fun k : Fin t => stream k)) =
        safeOutput G (candidateRun positivePad stream) (2 * t) :=
      (safeOutput_candidateRun_eq_history G positivePad stream t).symm
    _ = some x := hx

/-! ## The repaired identification reduction -/

/-- Candidate `i` passes Algorithm 1's two tests on one finite history:
it contains every positive observation, and the safe generator returns
bottom on the prefix-compatible candidate run. -/
def ReductionAccepts
    (G : SafeGenerator (α × ℕ))
    (C : Generic.LanguageFamily α)
    (positivePad : ℕ → Stream (α × ℕ))
    {t : ℕ} (xs : Fin t → α) (i : ℕ) : Prop :=
  (↑(Generic.sequenceSample xs) : Set α) ⊆ C i ∧
    G (2 * t) (candidateHistory (positivePad i) xs) = none

/-- The in-scope candidates that pass both tests of the repaired
identification algorithm. -/
noncomputable def reductionCandidates
    (G : SafeGenerator (α × ℕ))
    (C : Generic.LanguageFamily α)
    (positivePad : ℕ → Stream (α × ℕ))
    {t : ℕ} (xs : Fin t → α) : Finset ℕ := by
  classical
  exact (Finset.range t).filter fun i =>
    ReductionAccepts G C positivePad xs i

@[simp] theorem mem_reductionCandidates
    {G : SafeGenerator (α × ℕ)}
    {C : Generic.LanguageFamily α}
    {positivePad : ℕ → Stream (α × ℕ)}
    {t : ℕ} {xs : Fin t → α} {i : ℕ} :
    i ∈ reductionCandidates G C positivePad xs ↔
      i < t ∧ ReductionAccepts G C positivePad xs i := by
  classical
  simp [reductionCandidates]

/-- Algorithm 1 with each finite invocation replaced by the corresponding
prefix of a fixed infinite run. -/
noncomputable def identificationFromSafeGenerator
    (G : SafeGenerator (α × ℕ))
    (C : Generic.LanguageFamily α)
    (positivePad : ℕ → Stream (α × ℕ)) :
    GenLimit.Angluin.SemanticIdentifier α :=
  GenLimit.learnerOfFiniteHistory fun _ xs => by
    classical
    let candidates := reductionCandidates G C positivePad xs
    exact GenLimit.Support.leastCandidateWithFallback candidates 0

/-- Every earlier, non-equivalent candidate is eventually rejected, either
by positive-data inconsistency or by a non-bottom safe-generation output. -/
theorem earlierCandidates_eventually_rejected
    {G : SafeGenerator (α × ℕ)}
    {C : Generic.LanguageFamily α}
    {positivePad : ℕ → Stream (α × ℕ)}
    (hPositive : ∀ i,
      Generic.Presents (positivePad i) (verticalPad (C i)))
    (hFamilies :
      SafelyGeneratesFamilies G
        (fun i => verticalPad (C i))
        (fun i => verticalPad (C i)))
    {z : ℕ} {stream : Stream α}
    (hP : Generic.Presents stream (C z))
    (bound : ℕ)
    (hne : ∀ i, i < bound → C i ≠ C z) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < bound →
      ¬ReductionAccepts G C positivePad
        (fun q : Fin t => stream q) i := by
  induction bound with
  | zero =>
      exact ⟨0, by simp⟩
  | succ bound ih =>
      obtain ⟨Tprev, hprev⟩ :=
        ih (fun i hi => hne i (Nat.lt.step hi))
      have hneBound : C bound ≠ C z :=
        hne bound (Nat.lt_succ_self bound)
      by_cases hsub : C z ⊆ C bound
      · have hstrict : (C bound \ C z).Nonempty := by
          by_contra hnot
          have hempty : C bound \ C z = ∅ :=
            Set.not_nonempty_iff_eq_empty.mp hnot
          have hreverse : C bound ⊆ C z :=
            Set.diff_eq_empty.mp hempty
          exact hneBound (Set.Subset.antisymm hreverse hsub)
        have hRun :
            SafelyGenerates G (verticalPad (C bound))
              (verticalPad (C z))
              (candidateRun (positivePad bound) stream) :=
          hFamilies bound z _
            (candidateRun_labeledPresents (hPositive bound) hP)
        obtain ⟨Tcur, hcur⟩ :=
          candidateHistory_eventually_some
            (hPositive bound) hP hRun hstrict
        refine ⟨max Tprev Tcur, ?_⟩
        intro t ht i hi haccept
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hprev t
            (le_trans (Nat.le_max_left _ _) ht) i hi haccept
        · obtain ⟨x, hx⟩ :=
            hcur t (le_trans (Nat.le_max_right _ _) ht)
          rw [haccept.2] at hx
          simp at hx
      · obtain ⟨x, hxTarget, hxCandidate⟩ :=
          Set.not_subset.mp hsub
        obtain ⟨Tcur, hcur⟩ :=
          Generic.eventually_mem_sample_of_presents hP hxTarget
        refine ⟨max Tprev Tcur, ?_⟩
        intro t ht i hi haccept
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hprev t
            (le_trans (Nat.le_max_left _ _) ht) i hi haccept
        · apply hxCandidate
          apply haccept.1
          rw [Generic.sequenceSample_prefix]
          exact hcur t (le_trans (Nat.le_max_right _ _) ht)

/-- The target candidate is eventually in scope, positive-consistent, and
assigned bottom on its fixed padded run. -/
theorem targetCandidate_eventually_accepted
    {G : SafeGenerator (α × ℕ)}
    {C : Generic.LanguageFamily α}
    {positivePad : ℕ → Stream (α × ℕ)}
    (hPositive : ∀ i,
      Generic.Presents (positivePad i) (verticalPad (C i)))
    (hFamilies :
      SafelyGeneratesFamilies G
        (fun i => verticalPad (C i))
        (fun i => verticalPad (C i)))
    {z : ℕ} {stream : Stream α}
    (hP : Generic.Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t →
      ReductionAccepts G C positivePad
        (fun q : Fin t => stream q) z := by
  have hRun :
      SafelyGenerates G (verticalPad (C z))
        (verticalPad (C z))
        (candidateRun (positivePad z) stream) :=
    hFamilies z z _
      (candidateRun_labeledPresents (hPositive z) hP)
  obtain ⟨T, hbottom⟩ :=
    candidateHistory_eventually_none
      (hPositive z) hP hRun Set.Subset.rfl
  refine ⟨T, ?_⟩
  intro t ht
  constructor
  · intro x hx
    rw [Generic.sequenceSample_prefix] at hx
    exact Generic.mem_language_of_mem_sample_of_presents hP hx
  · exact hbottom t ht

/-- On a presentation of a target with no earlier duplicate index, the
repaired algorithm converges to that target's index. -/
theorem identificationFromSafeGenerator_identifies_minimal
    {G : SafeGenerator (α × ℕ)}
    {C : Generic.LanguageFamily α}
    {positivePad : ℕ → Stream (α × ℕ)}
    (hPositive : ∀ i,
      Generic.Presents (positivePad i) (verticalPad (C i)))
    (hFamilies :
      SafelyGeneratesFamilies G
        (fun i => verticalPad (C i))
        (fun i => verticalPad (C i)))
    {z : ℕ} {stream : Stream α}
    (hP : Generic.Presents stream (C z))
    (hminimal : ∀ i, i < z → C i ≠ C z) :
    GenLimit.IdentifiesInLimit C
      (identificationFromSafeGenerator G C positivePad)
      stream (C z) := by
  obtain ⟨Tbad, hbad⟩ :=
    earlierCandidates_eventually_rejected
      hPositive hFamilies hP z hminimal
  obtain ⟨Tgood, hgood⟩ :=
    targetCandidate_eventually_accepted
      hPositive hFamilies hP
  refine ⟨z, rfl, max (max Tbad Tgood) (z + 1), ?_⟩
  intro t ht
  have hTbad : Tbad ≤ t :=
    le_trans (Nat.le_max_left _ _)
      (le_trans (Nat.le_max_left _ _) ht)
  have hTgood : Tgood ≤ t :=
    le_trans (Nat.le_max_right _ _)
      (le_trans (Nat.le_max_left _ _) ht)
  have hzt : z < t := Nat.lt_of_succ_le
    (le_trans (Nat.le_max_right _ _ ) ht)
  let xs : Fin t → α := fun q => stream q
  let candidates :=
    reductionCandidates G C positivePad xs
  have hzmem : z ∈ candidates := by
    exact mem_reductionCandidates.mpr
      ⟨hzt, hgood t hTgood⟩
  have hnonempty : candidates.Nonempty := ⟨z, hzmem⟩
  change
    identificationFromSafeGenerator G C positivePad
      (GenLimit.textPrefix stream t) = z
  rw [GenLimit.textPrefix_eq_ofFn, identificationFromSafeGenerator,
    GenLimit.learnerOfFiniteHistory_ofFn]
  change
    GenLimit.Support.leastCandidateWithFallback candidates 0 = z
  apply Nat.le_antisymm
  · exact GenLimit.Support.leastCandidateWithFallback_le hzmem
  · by_contra hnot
    have hlt :
        GenLimit.Support.leastCandidateWithFallback candidates 0 < z :=
      Nat.lt_of_not_ge hnot
    have hminmem :
        GenLimit.Support.leastCandidateWithFallback candidates 0 ∈ candidates :=
      GenLimit.Support.leastCandidateWithFallback_mem hnonempty
    have haccepted :=
      (mem_reductionCandidates.mp hminmem).2
    exact hbad t hTbad
      (GenLimit.Support.leastCandidateWithFallback candidates 0)
      hlt haccepted

/-- First index denoting the same language as `C z`. -/
noncomputable abbrev firstEquivalentIndex
    (C : Generic.LanguageFamily α) (z : ℕ) : ℕ :=
  GenLimit.Support.leastEquivalentIndex C z

theorem firstEquivalentIndex_spec
    (C : Generic.LanguageFamily α) (z : ℕ) :
    C (firstEquivalentIndex C z) = C z :=
  GenLimit.Support.leastEquivalentIndex_spec C z

theorem firstEquivalentIndex_minimal
    (C : Generic.LanguageFamily α) (z : ℕ) :
    ∀ i, i < firstEquivalentIndex C z → C i ≠ C z := by
  intro i hi
  exact GenLimit.Support.leastEquivalentIndex_ne_of_lt C z hi

/-- Theorem 5.1, semantic core with the source's repeated finite calls
replaced by prefixes of fixed infinite runs.  Duplicate family indices are
handled by converging to the first extensionally equivalent one. -/
theorem theorem_5_1_prefix_compatible
    (G : SafeGenerator (α × ℕ))
    (C : Generic.LanguageFamily α)
    (positivePad : ℕ → Stream (α × ℕ))
    (hPositive : ∀ i,
      Generic.Presents (positivePad i) (verticalPad (C i)))
    (hFamilies :
      SafelyGeneratesFamilies G
        (fun i => verticalPad (C i))
        (fun i => verticalPad (C i))) :
    GenLimit.Angluin.SemanticallyIdentifies
      (identificationFromSafeGenerator G C positivePad) C := by
  intro z stream hP
  let j := firstEquivalentIndex C z
  have hj : C j = C z := firstEquivalentIndex_spec C z
  have hPj : Generic.Presents stream (C j) := by
    rw [hj]
    exact hP
  obtain ⟨q, hq, hconv⟩ :=
    identificationFromSafeGenerator_identifies_minimal
      hPositive hFamilies hPj
        (by
          intro i hi heq
          exact (firstEquivalentIndex_minimal C z i hi)
            (heq.trans hj))
  exact ⟨q, hq.trans hj, hconv⟩

/-! ## Canonical candidate presentations on a countable universe -/

/-- A fixed injective presentation of a padded nonempty language. -/
noncomputable def verticalPadPresentation [Countable α]
    (L : Generic.Language α) (hL : L.Nonempty) :
    Stream (α × ℕ) :=
  GenLimit.Support.infiniteEnumeration
    (verticalPad L) (verticalPad_infinite_of_nonempty hL)

theorem verticalPadPresentation_presents [Countable α]
    (L : Generic.Language α) (hL : L.Nonempty) :
    Generic.Presents (verticalPadPresentation L hL)
      (verticalPad L) := by
  simpa [verticalPadPresentation] using
    GenLimit.Support.infiniteEnumeration_presents
      (verticalPad L) (verticalPad_infinite_of_nonempty hL)

/-- Countable-universe form of the repaired Theorem 5.1 reduction.  The
paper's standing assumption that all languages are infinite supplies the
candidate presentations used by Algorithm 1. -/
theorem theorem_5_1 [Countable α]
    (G : SafeGenerator (α × ℕ))
    (C : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (C i).Infinite)
    (hFamilies :
      SafelyGeneratesFamilies G
        (fun i => verticalPad (C i))
        (fun i => verticalPad (C i))) :
    ∃ M : GenLimit.Angluin.SemanticIdentifier α,
      GenLimit.Angluin.SemanticallyIdentifies M C := by
  let positivePad : ℕ → Stream (α × ℕ) :=
    fun i => verticalPadPresentation (C i) (hInfinite i).nonempty
  refine ⟨identificationFromSafeGenerator G C positivePad, ?_⟩
  apply theorem_5_1_prefix_compatible G C positivePad
  · intro i
    exact verticalPadPresentation_presents
      (C i) (hInfinite i).nonempty
  · exact hFamilies

end GenLimit.SafeGeneration
