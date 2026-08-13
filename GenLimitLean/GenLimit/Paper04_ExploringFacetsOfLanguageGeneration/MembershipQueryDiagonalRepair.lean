import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.MembershipQueryShadow
import GenLimit.Support.EnumerationProgress
import Mathlib.Data.Set.Finite.Lattice

/-!
# Theorem 7: repaired completion and the remaining diagonal certificate

This file formalizes the repair needed by the nontermination branch of
Charikar--Pabbaraju, *Exploring Facets of Language Generation in the Limit*,
arXiv:2411.15364v2, Theorem 7.

The printed proof says that an infinite query loop keeps populating both
languages.  That implication is false when the machine repeats only finitely
many query words.  For a finite partial assignment, the constructions below
complete the two languages with disjoint even/odd tails above the assignment.
Both completed languages are infinite, all recorded answers are preserved,
and their intersection contains only words that the assignment explicitly
put in both languages.

The second half packages the two exact remaining infinite-stage outcomes.
A `MembershipNonterminationCertificate` is a legal infinite language pair and
exact presentation on which one round has no output.  A
`MembershipDiagonalCertificate` covers the alternative in which all phases
terminate: it has an injective common positive prefix of every finite length,
a faithful completed execution at each phase, and an output outside the
completed intersection.  Either certificate contradicts the exact
non-uniform guarantee.  We prove that constructing one of the two for every
deterministic machine implies the literal `TheoremSevenStatement`.

Thus no finite-transcript or presentation-extension step remains implicit.
What is still not proved is the source's global dependent construction and
its split into the terminating and repaired nonterminating outcomes.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## A separated infinite completion of a finite assignment -/

/-- The words on which a partial two-language assignment has made a
decision. -/
def partialAssignmentDomain
    (assignment : PartialTwoLanguageAssignment) : Set ℕ :=
  {x | ∃ bits, assignment x = some bits}

/-- The words explicitly assigned to the left language. -/
def partialAssignmentLeft
    (assignment : PartialTwoLanguageAssignment) : Set ℕ :=
  {x | ∃ bits, assignment x = some bits ∧ bits.1 = true}

/-- The words explicitly assigned to the right language. -/
def partialAssignmentRight
    (assignment : PartialTwoLanguageAssignment) : Set ℕ :=
  {x | ∃ bits, assignment x = some bits ∧ bits.2 = true}

/-- The words explicitly assigned to both languages. -/
def partialAssignmentCommon
    (assignment : PartialTwoLanguageAssignment) : Set ℕ :=
  {x | assignment x = some (true, true)}

/-- Every decided word lies strictly below `cutoff`. -/
def PartialAssignmentBelow
    (assignment : PartialTwoLanguageAssignment) (cutoff : ℕ) : Prop :=
  ∀ x bits, assignment x = some bits → x < cutoff

/-- A finite assignment domain has a strict numerical upper bound. -/
theorem finite_partialAssignmentDomain_below
    {assignment : PartialTwoLanguageAssignment}
    (hfinite : (partialAssignmentDomain assignment).Finite) :
    ∃ cutoff, PartialAssignmentBelow assignment cutoff := by
  rcases hfinite.bddAbove with ⟨bound, hbound⟩
  refine ⟨bound + 1, ?_⟩
  intro x bits hbits
  exact Nat.lt_succ_of_le (hbound ⟨bits, hbits⟩)

/-- Fresh even-offset tail reserved for the left completion. -/
def leftFreshTail (cutoff : ℕ) : Set ℕ :=
  Set.range fun n ↦ cutoff + 2 * n

/-- Fresh odd-offset tail reserved for the right completion. -/
def rightFreshTail (cutoff : ℕ) : Set ℕ :=
  Set.range fun n ↦ cutoff + 2 * n + 1

/-- Complete the left language while preserving all assigned answers. -/
def separatedLeftCompletion
    (assignment : PartialTwoLanguageAssignment) (cutoff : ℕ) : Set ℕ :=
  partialAssignmentLeft assignment ∪ leftFreshTail cutoff

/-- Complete the right language while preserving all assigned answers. -/
def separatedRightCompletion
    (assignment : PartialTwoLanguageAssignment) (cutoff : ℕ) : Set ℕ :=
  partialAssignmentRight assignment ∪ rightFreshTail cutoff

theorem separatedLeftCompletion_infinite
    (assignment : PartialTwoLanguageAssignment) (cutoff : ℕ) :
    (separatedLeftCompletion assignment cutoff).Infinite := by
  have htail : (Set.range fun n : ℕ ↦ cutoff + 2 * n).Infinite :=
    Set.infinite_range_of_injective (fun m n h ↦ by omega)
  apply htail.mono
  intro x hx
  exact Or.inr (by simpa [leftFreshTail] using hx)

theorem separatedRightCompletion_infinite
    (assignment : PartialTwoLanguageAssignment) (cutoff : ℕ) :
    (separatedRightCompletion assignment cutoff).Infinite := by
  have htail :
      (Set.range fun n : ℕ ↦ cutoff + 2 * n + 1).Infinite :=
    Set.infinite_range_of_injective (fun m n h ↦ by omega)
  apply htail.mono
  intro x hx
  exact Or.inr (by simpa [rightFreshTail] using hx)

/-- The separated completions respect every answer in the partial oracle. -/
theorem separatedCompletions_realize
    {assignment : PartialTwoLanguageAssignment} {cutoff : ℕ}
    (hbelow : PartialAssignmentBelow assignment cutoff) :
    LanguagePairRealizes assignment
      (separatedLeftCompletion assignment cutoff)
      (separatedRightCompletion assignment cutoff) := by
  intro x bits hbits
  have hxBelow : x < cutoff := hbelow x bits hbits
  constructor
  · constructor
    · intro hleft
      exact Or.inl ⟨bits, hbits, hleft⟩
    · intro hx
      rcases hx with hxAssigned | hxTail
      · rcases hxAssigned with ⟨other, hother, hleft⟩
        have heq : bits = other :=
          Option.some.inj (hbits.symm.trans hother)
        simpa [heq] using hleft
      · change ∃ n, cutoff + 2 * n = x at hxTail
        rcases hxTail with ⟨n, hn⟩
        rw [← hn] at hxBelow
        omega
  · constructor
    · intro hright
      exact Or.inl ⟨bits, hbits, hright⟩
    · intro hx
      rcases hx with hxAssigned | hxTail
      · rcases hxAssigned with ⟨other, hother, hright⟩
        have heq : bits = other :=
          Option.some.inj (hbits.symm.trans hother)
        simpa [heq] using hright
      · change ∃ n, cutoff + 2 * n + 1 = x at hxTail
        rcases hxTail with ⟨n, hn⟩
        rw [← hn] at hxBelow
        omega

/-- The completions introduce no new common word.  In particular, the two
fresh tails are disjoint, and neither tail can meet the bounded assignment
domain. -/
theorem separatedCompletions_intersection_subset_common
    {assignment : PartialTwoLanguageAssignment} {cutoff : ℕ}
    (hbelow : PartialAssignmentBelow assignment cutoff) :
    separatedLeftCompletion assignment cutoff ∩
        separatedRightCompletion assignment cutoff ⊆
      partialAssignmentCommon assignment := by
  rintro x ⟨hxLeft, hxRight⟩
  rcases hxLeft with hxAssignedLeft | hxTailLeft
  · rcases hxAssignedLeft with ⟨leftBits, hleftBits, hleftTrue⟩
    rcases hxRight with hxAssignedRight | hxTailRight
    · rcases hxAssignedRight with
        ⟨rightBits, hrightBits, hrightTrue⟩
      have heq : leftBits = rightBits :=
        Option.some.inj (hleftBits.symm.trans hrightBits)
      have hrightTrue' : leftBits.2 = true := by
        simpa [heq] using hrightTrue
      have hpair : leftBits = (true, true) := by
        apply Prod.ext
        · simpa using hleftTrue
        · simpa using hrightTrue'
      simpa [partialAssignmentCommon, hpair] using hleftBits
    · have hxBelow : x < cutoff :=
        hbelow x leftBits hleftBits
      change ∃ n, cutoff + 2 * n + 1 = x at hxTailRight
      rcases hxTailRight with ⟨n, hn⟩
      rw [← hn] at hxBelow
      omega
  · change ∃ m, cutoff + 2 * m = x at hxTailLeft
    rcases hxTailLeft with ⟨m, hm⟩
    rcases hxRight with hxAssignedRight | hxTailRight
    · rcases hxAssignedRight with
        ⟨rightBits, hrightBits, _⟩
      have hxBelow : x < cutoff :=
        hbelow x rightBits hrightBits
      rw [← hm] at hxBelow
      omega
    · change ∃ n, cutoff + 2 * n + 1 = x at hxTailRight
      rcases hxTailRight with ⟨n, hn⟩
      omega

/-- Exact repair for the finite-range branch of a nonterminating query
dialogue: a finite partial oracle always has two separated infinite
completions preserving all answers. -/
theorem finitePartialAssignment_has_separated_infinite_completion
    {assignment : PartialTwoLanguageAssignment}
    (hfinite : (partialAssignmentDomain assignment).Finite) :
    ∃ L₀ L₁ : Set ℕ,
      L₀.Infinite ∧ L₁.Infinite ∧
      LanguagePairRealizes assignment L₀ L₁ ∧
      L₀ ∩ L₁ ⊆ partialAssignmentCommon assignment := by
  obtain ⟨cutoff, hbelow⟩ :=
    finite_partialAssignmentDomain_below hfinite
  exact
    ⟨separatedLeftCompletion assignment cutoff,
      separatedRightCompletion assignment cutoff,
      separatedLeftCompletion_infinite assignment cutoff,
      separatedRightCompletion_infinite assignment cutoff,
      separatedCompletions_realize hbelow,
      separatedCompletions_intersection_subset_common hbelow⟩

/-! ## Machine-checked diagnosis of the printed nontermination inference -/

/-- An infinite within-round query dialogue.  At stage `k`, the machine sees
the first `k` answered queries and asks the query recorded at position `k`;
the recorded answer is correct for the completed language pair. -/
def InfiniteRoundQueryRun
    (A : TwoLanguageMembershipAlgorithm) (L₀ L₁ : Set ℕ)
    (history : List TwoLanguageRound) (input : ℕ)
    (run : ℕ → AnsweredTwoLanguageQuery) : Prop :=
  ∀ k,
    A (history, input, List.ofFn fun i : Fin k ↦ run i) =
        Sum.inl (run k).1 ∧
      AnsweredQueryCorrect L₀ L₁ (run k)

/-- Semantic nontermination at one round: after every valid finite answered
trace, the machine asks another query instead of emitting an output. -/
def RoundDiverges
    (A : TwoLanguageMembershipAlgorithm) (L₀ L₁ : Set ℕ)
    (history : List TwoLanguageRound) (input : ℕ) : Prop :=
  ∀ trace,
    QueryTraceValid A L₀ L₁ history input trace →
      ∃ q, A (history, input, trace) = Sum.inl q

theorem RoundDiverges.no_valid_round
    {A : TwoLanguageMembershipAlgorithm} {L₀ L₁ : Set ℕ}
    {history : List TwoLanguageRound} {input : ℕ}
    (hdiverges : RoundDiverges A L₀ L₁ history input) :
    ¬ ∃ round, RoundValid A L₀ L₁ history input round := by
  rintro ⟨round, _, htrace, houtput⟩
  obtain ⟨q, hquery⟩ := hdiverges round.2.1 htrace
  have himpossible :
      (Sum.inl q : TwoLanguageAction) = Sum.inr round.2.2 :=
    hquery.symm.trans houtput
  cases himpossible

/-- A deterministic machine that repeats one query forever. -/
def repeatingQueryAlgorithm
    (q : TwoLanguageQuery) : TwoLanguageMembershipAlgorithm :=
  fun _ ↦ Sum.inl q

/-- Its constant, positively answered infinite transcript. -/
def repeatingAnsweredRun
    (q : TwoLanguageQuery) : ℕ → AnsweredTwoLanguageQuery :=
  fun _ ↦ (q, true)

theorem repeatingQueryAlgorithm_has_infinite_run
    (q : TwoLanguageQuery) (history : List TwoLanguageRound) (input : ℕ) :
    InfiniteRoundQueryRun (repeatingQueryAlgorithm q)
      Set.univ Set.univ history input (repeatingAnsweredRun q) := by
  intro k
  constructor
  · rfl
  · simp [AnsweredQueryCorrect, queriedLanguage, repeatingAnsweredRun]

theorem repeatingQueryAlgorithm_no_valid_round
    (q : TwoLanguageQuery) (L₀ L₁ : Set ℕ)
    (history : List TwoLanguageRound) (input : ℕ) :
    ¬ ∃ round,
      RoundValid (repeatingQueryAlgorithm q) L₀ L₁ history input round := by
  apply RoundDiverges.no_valid_round
  intro trace _
  exact ⟨q, rfl⟩

theorem repeatingAnsweredRun_queryWords_finite
    (q : TwoLanguageQuery) :
    (Set.range fun k ↦ (repeatingAnsweredRun q k).1.2).Finite := by
  simp [repeatingAnsweredRun]

/-- The implication used in the printed prose is false: an actually
nonterminating deterministic round can query only one distinct word. -/
theorem infinite_query_run_need_not_have_infinite_query_range :
    ∃ (A : TwoLanguageMembershipAlgorithm)
        (L₀ L₁ : Set ℕ) (history : List TwoLanguageRound) (input : ℕ)
        (run : ℕ → AnsweredTwoLanguageQuery),
      L₀.Infinite ∧ L₁.Infinite ∧
      InfiniteRoundQueryRun A L₀ L₁ history input run ∧
      (Set.range fun k ↦ (run k).1.2).Finite ∧
      ¬ ∃ round, RoundValid A L₀ L₁ history input round := by
  let q : TwoLanguageQuery := (false, 0)
  exact
    ⟨repeatingQueryAlgorithm q, Set.univ, Set.univ, [], 0,
      repeatingAnsweredRun q,
      Set.infinite_univ, Set.infinite_univ,
      repeatingQueryAlgorithm_has_infinite_run q [] 0,
      repeatingAnsweredRun_queryWords_finite q,
      repeatingQueryAlgorithm_no_valid_round q Set.univ Set.univ [] 0⟩

/-! ## Exact presentations extending a prescribed finite common prefix -/

/-- Follow a finite prefix, then enumerate the whole target.  Repetitions in
the tail are allowed by `Generic.Presents`. -/
noncomputable def finitePrefixThenEnumeration
    {n : ℕ} (xs : Fin n → ℕ)
    (L : Set ℕ) (hL : L.Infinite) : Stream ℕ :=
  fun k ↦
    if hk : k < n then xs ⟨k, hk⟩
    else GenLimit.Support.infiniteEnumeration L hL (k - n)

@[simp] theorem finitePrefixThenEnumeration_prefix
    {n : ℕ} (xs : Fin n → ℕ)
    (L : Set ℕ) (hL : L.Infinite) (k : ℕ) (hk : k < n) :
    finitePrefixThenEnumeration xs L hL k =
      xs ⟨k, hk⟩ := by
  simp [finitePrefixThenEnumeration, hk]

theorem finitePrefixThenEnumeration_presents
    {n : ℕ} {xs : Fin n → ℕ}
    {L : Set ℕ} (hL : L.Infinite)
    (hxs : ∀ i, xs i ∈ L) :
    Presents (finitePrefixThenEnumeration xs L hL) L := by
  apply Set.Subset.antisymm
  · rintro x ⟨k, rfl⟩
    by_cases hk : k < n
    · simpa [finitePrefixThenEnumeration, hk] using
        hxs ⟨k, hk⟩
    · have hmem :
          GenLimit.Support.infiniteEnumeration L hL (k - n) ∈ L :=
        GenLimit.Support.infiniteEnumeration_mem L hL (k - n)
      simpa [finitePrefixThenEnumeration, hk] using hmem
  · intro x hx
    obtain ⟨k, rfl⟩ :=
      GenLimit.Support.infiniteEnumeration_surjective L hL hx
    refine ⟨n + k, ?_⟩
    simp [finitePrefixThenEnumeration]

theorem finitePrefixThenEnumeration_sample
    {n : ℕ} (xs : Fin n → ℕ)
    (L : Set ℕ) (hL : L.Infinite) :
    Generic.sample (finitePrefixThenEnumeration xs L hL) n =
      sequenceSample xs := by
  rw [← Generic.sequenceSample_prefix]
  congr 1
  funext i
  exact finitePrefixThenEnumeration_prefix
    xs L hL i i.isLt

theorem finitePrefixThenEnumeration_sample_card
    {n : ℕ} {xs : Fin n → ℕ}
    (hxsInjective : Function.Injective xs)
    (L : Set ℕ) (hL : L.Infinite) :
    (Generic.sample (finitePrefixThenEnumeration xs L hL) n).card = n := by
  letI : DecidableEq ℕ := Classical.decEq ℕ
  have hinjOn :
      Set.InjOn xs
        ((Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
    intro i _ j _ hij
    exact hxsInjective hij
  rw [finitePrefixThenEnumeration_sample,
    Generic.sequenceSample, Finset.card_image_iff.mpr hinjOn]
  simp

/-! ## The exact remaining infinite-stage certificate -/

/-- The direct obstruction arising when an adaptive phase does not terminate:
on one exact target presentation, the machine has no completed output at the
recorded round. -/
structure MembershipNonterminationCertificate
    (A : TwoLanguageMembershipAlgorithm) where
  leftLanguage : Set ℕ
  rightLanguage : Set ℕ
  leftInfinite : leftLanguage.Infinite
  rightInfinite : rightLanguage.Infinite
  target : Bool
  stream : Stream ℕ
  presents :
    Presents stream (selectedTwoLanguage leftLanguage rightLanguage target)
  time : ℕ
  noOutput :
    ¬ ∃ z,
      MembershipExecutionOutputsAt A
        leftLanguage rightLanguage stream time z

/-- A legal exact presentation with a nonterminating round immediately
contradicts the termination clause of the non-uniform guarantee. -/
theorem MembershipNonterminationCertificate.not_nonuniformGuarantee
    {A : TwoLanguageMembershipAlgorithm}
    (certificate : MembershipNonterminationCertificate A) :
    ¬ NonuniformTwoLanguageMembershipGuarantee A
      certificate.leftLanguage certificate.rightLanguage := by
  intro hguarantee
  rcases hguarantee with ⟨d₀, d₁, hguarantee⟩
  exact certificate.noOutput
    ((hguarantee certificate.target certificate.stream
      certificate.presents certificate.time).1)

/-- The finite execution produced by phase `n`: it consumes the first
`n+1` common positive inputs and records the output of the last round. -/
def CommonPrefixExecutionOutputsAt
    (A : TwoLanguageMembershipAlgorithm) (L₀ L₁ : Set ℕ)
    (commonInput : ℕ → ℕ) (n z : ℕ) : Prop :=
  ∃ rounds : List TwoLanguageRound,
    ExecutionValid A L₀ L₁
      (List.ofFn fun i : Fin (n + 1) ↦ commonInput i) rounds ∧
    ∃ hn : n < rounds.length,
      (rounds.get ⟨n, hn⟩).2.2 = z

/-- The complete semantic object that the terminating branch of the printed
adaptive diagonal is intended to construct.  It deliberately includes final
languages and final-oracle executions, so the earlier finite-shadow theorems
are exactly what a construction proof must use to discharge `execution`. -/
structure MembershipDiagonalCertificate
    (A : TwoLanguageMembershipAlgorithm) where
  leftLanguage : Set ℕ
  rightLanguage : Set ℕ
  leftInfinite : leftLanguage.Infinite
  rightInfinite : rightLanguage.Infinite
  commonInput : ℕ → ℕ
  commonInput_injective : Function.Injective commonInput
  commonInput_mem :
    ∀ n, commonInput n ∈ leftLanguage ∩ rightLanguage
  phaseOutput : ℕ → ℕ
  execution :
    ∀ n, CommonPrefixExecutionOutputsAt A
      leftLanguage rightLanguage commonInput n (phaseOutput n)
  phaseOutput_not_common :
    ∀ n, phaseOutput n ∉ leftLanguage ∩ rightLanguage

theorem commonPrefixExecutionOutputsAt_on_extension
    {A : TwoLanguageMembershipAlgorithm} {L₀ L₁ : Set ℕ}
    {commonInput : ℕ → ℕ} {n z : ℕ}
    (houtput :
      CommonPrefixExecutionOutputsAt A L₀ L₁ commonInput n z)
    (stream : Stream ℕ)
    (hprefix : ∀ k, k < n + 1 → stream k = commonInput k) :
    MembershipExecutionOutputsAt A L₀ L₁ stream n z := by
  rcases houtput with ⟨rounds, hvalid, hn, hz⟩
  refine ⟨rounds, ?_, hn, hz⟩
  have hinputs :
      membershipInputPrefix stream (n + 1) =
        List.ofFn (fun i : Fin (n + 1) ↦ commonInput i) := by
    unfold membershipInputPrefix
    apply List.ofFn_inj.mpr
    funext i
    exact hprefix i i.isLt
  rw [hinputs]
  exact hvalid

/-- A completed adaptive-diagonal certificate is incompatible with the exact
two-language non-uniform guarantee. -/
theorem MembershipDiagonalCertificate.not_nonuniformGuarantee
    {A : TwoLanguageMembershipAlgorithm}
    (certificate : MembershipDiagonalCertificate A) :
    ¬ NonuniformTwoLanguageMembershipGuarantee A
      certificate.leftLanguage certificate.rightLanguage := by
  intro hguarantee
  obtain ⟨d₀, d₁, hendgame⟩ :=
    nonuniformGuarantee_commonPrefix_output hguarantee
  let n := max d₀ d₁
  let xs : Fin (n + 1) → ℕ :=
    fun i ↦ certificate.commonInput i
  let stream₀ : Stream ℕ :=
    finitePrefixThenEnumeration xs
      certificate.leftLanguage certificate.leftInfinite
  let stream₁ : Stream ℕ :=
    finitePrefixThenEnumeration xs
      certificate.rightLanguage certificate.rightInfinite
  have hpresents₀ :
      Presents stream₀ certificate.leftLanguage := by
    apply finitePrefixThenEnumeration_presents
    intro i
    exact (certificate.commonInput_mem i).1
  have hpresents₁ :
      Presents stream₁ certificate.rightLanguage := by
    apply finitePrefixThenEnumeration_presents
    intro i
    exact (certificate.commonInput_mem i).2
  have hprefix₀ :
      ∀ k, k < n + 1 → stream₀ k = certificate.commonInput k := by
    intro k hk
    simpa [stream₀, xs] using
      finitePrefixThenEnumeration_prefix xs
        certificate.leftLanguage certificate.leftInfinite k hk
  have hprefix₁ :
      ∀ k, k < n + 1 → stream₁ k = certificate.commonInput k := by
    intro k hk
    simpa [stream₁, xs] using
      finitePrefixThenEnumeration_prefix xs
        certificate.rightLanguage certificate.rightInfinite k hk
  have hsamePrefix :
      ∀ k, k < n + 1 → stream₀ k = stream₁ k := by
    intro k hk
    exact (hprefix₀ k hk).trans (hprefix₁ k hk).symm
  have houtput :
      MembershipExecutionOutputsAt A
        certificate.leftLanguage certificate.rightLanguage
        stream₀ n (certificate.phaseOutput n) :=
    commonPrefixExecutionOutputsAt_on_extension
      (certificate.execution n) stream₀ hprefix₀
  have hxsInjective : Function.Injective xs := by
    intro i j hij
    apply Fin.ext
    exact certificate.commonInput_injective hij
  have hsampleCard :
      (Generic.sample stream₀ (n + 1)).card = n + 1 := by
    exact finitePrefixThenEnumeration_sample_card
      hxsInjective certificate.leftLanguage certificate.leftInfinite
  have hlarge :
      max d₀ d₁ ≤ (Generic.sample stream₀ (n + 1)).card := by
    rw [hsampleCard]
    exact Nat.le_succ n
  have hcommon :=
    hendgame stream₀ stream₁ n (certificate.phaseOutput n)
      hpresents₀ hpresents₁ hsamePrefix houtput hlarge
  exact certificate.phaseOutput_not_common n hcommon.1

/-- Isolates the exact global case split remaining from the source proof:
either some phase does not terminate on a completed legal instance, or all
phases terminate and yield the common-prefix diagonal certificate. -/
def MembershipAdaptiveDiagonalPrinciple : Prop :=
  ∀ A : TwoLanguageMembershipAlgorithm,
    Nonempty (MembershipNonterminationCertificate A) ∨
      Nonempty (MembershipDiagonalCertificate A)

/-- Once the repaired adaptive case split is constructed for every machine,
the literal Theorem 7 statement follows with no further computability or
presentation assumptions. -/
theorem theoremSeven_of_membershipAdaptiveDiagonal
    (hdiagonal : MembershipAdaptiveDiagonalPrinciple) :
    TheoremSevenStatement := by
  rintro ⟨A, hA⟩
  rcases hdiagonal A with hnontermination | hterminating
  · let certificate := Classical.choice hnontermination
    exact certificate.not_nonuniformGuarantee
      (hA.2 certificate.leftLanguage certificate.rightLanguage
        certificate.leftInfinite certificate.rightInfinite)
  · let certificate := Classical.choice hterminating
    exact certificate.not_nonuniformGuarantee
      (hA.2 certificate.leftLanguage certificate.rightLanguage
        certificate.leftInfinite certificate.rightInfinite)

end GenLimit.CharikarPabbaraju
