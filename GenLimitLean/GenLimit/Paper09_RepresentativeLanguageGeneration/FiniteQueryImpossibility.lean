import GenLimit.Paper09_RepresentativeLanguageGeneration.Definitions
import GenLimit.Core.Text
import Mathlib.Computability.Partrec
import Mathlib.Data.List.OfFn

/-!
# Representative generation from finite membership queries: finite core

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Lemma 4.9 and Appendix D.4.

The source studies a deterministic oracle algorithm which, after a finite
positive history, adaptively queries membership in the unknown target or in a
named group and then returns a code for a possibly infinitely supported
distribution.  The algorithm is required to make only finitely many queries
in every round.

This module records that operational interface and proves the finite
transcript diagonal at the heart of Lemma 4.9.  For a history having at least
half of its distinct observations in the first group, every terminating query
transcript can be preserved while completing the target and binary partition
so that the decoded output is either inconsistent or has representation error
at least `1 / 2`.

The companion module `QueryImpossibility` proves the full statement with a
cleaner infinitary repair: it fixes the target to `Set.univ`, constructs only
the binary partition, and permanently excludes finite high-mass blocks from
the limiting first group.  This module retains the source-facing operational
model and the independent one-round diagonal.
-/

namespace GenLimit.RepresentativeGeneration
namespace MembershipQuery

/-! ## Adaptive query algorithms and completed executions -/

/-- `none` queries target membership; `some i` queries membership in group
`i`.  This product encoding is `Primcodable` whenever the point type is. -/
abbrev Query (α : Type*) := Option ℕ × α

/-- A membership query paired with the Boolean answer returned by the oracle. -/
abbrev AnsweredQuery (α : Type*) := Query α × Bool

/-- A deterministic adaptive query algorithm with coded distribution outputs.

The semantic decoder is intentionally not required to be computable.  The
source explicitly makes no assumption about how a potentially infinitely
supported distribution is represented.  Requiring only the dialogue
transition to be computable therefore avoids introducing an unjustified
computable-real encoding and strengthens the finite-query lower bound. -/
structure Algorithm (α Code : Type*) where
  next :
    List α → List (AnsweredQuery α) →
      Sum (Query α) Code
  decode : Code → DiscreteDistribution α

/-- The set addressed by a target or indexed-group query. -/
def querySet
    (target : Set α) (groups : ℕ → Set α)
    (q : Query α) : Set α :=
  match q.1 with
  | none => target
  | some i => groups i

/-- Correctness of one recorded oracle answer. -/
def AnswerCorrect
    (target : Set α) (groups : ℕ → Set α)
    (qa : AnsweredQuery α) : Prop :=
  qa.2 = true ↔ qa.1.2 ∈ querySet target groups qa.1

/-- Every entry in a finite trace is exactly the next adaptive query selected
from the preceding trace and carries the correct oracle answer. -/
def TraceValid
    (M : Algorithm α Code)
    (target : Set α) (groups : ℕ → Set α)
    (history : List α) (trace : List (AnsweredQuery α)) : Prop :=
  ∀ (k : ℕ) (hk : k < trace.length),
    let qa := trace.get ⟨k, hk⟩
    M.next history (trace.take k) = Sum.inl qa.1 ∧
      AnswerCorrect target groups qa

/-- A valid finite query dialogue followed by an output code.  Absence of
such a trace is the source's possible infinite-query execution. -/
def TerminatesWith
    (M : Algorithm α Code)
    (target : Set α) (groups : ℕ → Set α)
    (history : List α) (trace : List (AnsweredQuery α))
    (code : Code) : Prop :=
  TraceValid M target groups history trace ∧
    M.next history trace = Sum.inr code

/-- The first `t` positive inputs, in chronological order, using the shared
ordered-prefix representation from Core. -/
abbrev inputPrefix
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) : List ℕ :=
  GenLimit.textPrefix stream t

/-- The algorithm terminates after the first `t` observations with this output
code and some finite, correctly answered adaptive query trace. -/
def OutputsAt
    (M : Algorithm ℕ Code)
    (target : Set ℕ) (groups : ℕ → Set ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ)
    (code : Code) : Prop :=
  ∃ trace, TerminatesWith M target groups
    (inputPrefix stream t) trace code

/-- Operational fixed-tolerance representative generation in the limit.

Termination and representation hold on every nonempty input history.
Consistency is eventually required along every exact presentation of the
target.  Quantifying over every valid output code is harmless for the
deterministic dialogue and avoids building uniqueness into the definition. -/
def AlphaLimitGuarantee
    (M : Algorithm ℕ Code)
    (target : Set ℕ) (groups : ℕ → Set ℕ)
    (alpha : ℝ) : Prop :=
  (∀ stream t, 0 < t →
      ∃ code, OutputsAt M target groups stream t code) ∧
  (∀ stream t, 0 < t → ∀ code,
      OutputsAt M target groups stream t code →
        groupSupDistance (M.decode code)
            (GenLimit.Generic.sample stream t) groups ≤
          ENNReal.ofReal alpha) ∧
  ∀ stream,
    GenLimit.Generic.Presents stream target →
      ∃ T, ∀ t, T ≤ t → ∀ code,
        OutputsAt M target groups stream t code →
          SupportedOn (M.decode code)
            (target \
              (GenLimit.Generic.sample stream t : Set ℕ))

/-! ## Binary partitions and the source-facing statement -/

/-- Embed a two-set partition into the repository's countable group indexing.
Queries to every index at least two receive a negative answer. -/
def binaryGroups (firstGroup : Set ℕ) : ℕ → Set ℕ
  | 0 => firstGroup
  | 1 => firstGroupᶜ
  | _ => ∅

@[simp]
theorem binaryGroups_zero (A : Set ℕ) :
    binaryGroups A 0 = A :=
  rfl

@[simp]
theorem binaryGroups_one (A : Set ℕ) :
    binaryGroups A 1 = Aᶜ :=
  rfl

theorem binaryGroups_pairwise (A : Set ℕ) :
    ∀ i j, i ≠ j →
      Disjoint (binaryGroups A i) (binaryGroups A j) := by
  intro i j hij
  rcases i with _ | i
  · rcases j with _ | j
    · exact (hij rfl).elim
    · rcases j with _ | j
      · exact disjoint_compl_right
      · simp [binaryGroups]
  · rcases i with _ | i
    · rcases j with _ | j
      · exact disjoint_compl_left
      · rcases j with _ | j
        · exact (hij rfl).elim
        · simp [binaryGroups]
    · simp [binaryGroups]

theorem iUnion_binaryGroups (A : Set ℕ) :
    (⋃ i, binaryGroups A i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ A
  · exact Set.mem_iUnion.mpr ⟨0, hx⟩
  · exact Set.mem_iUnion.mpr ⟨1, hx⟩

theorem binaryGroups_isCountablePartition (A : Set ℕ) :
    IsCountablePartition (binaryGroups A) :=
  ⟨binaryGroups_pairwise A, iUnion_binaryGroups A⟩

/-- One computable dialogue machine would have to work for every infinite
target and every binary partition. -/
def UniversalBinaryAlgorithm
    (M : Algorithm ℕ ℕ) (alpha : ℝ) : Prop :=
  Computable₂ M.next ∧
    ∀ target firstGroup : Set ℕ,
      target.Infinite →
        AlphaLimitGuarantee M target
          (binaryGroups firstGroup) alpha

/-- Published Lemma 4.9 as a source-facing proposition.  Its finite transcript core is
proved below and the full theorem is proved in `QueryImpossibility`. -/
def finiteQuery_impossibility_statement : Prop :=
  ∀ alpha : ℝ, 0 < alpha → alpha < 1 / 2 →
    ¬ ∃ M : Algorithm ℕ ℕ,
      UniversalBinaryAlgorithm M alpha

/-! ## Finite transcript invariance -/

/-- The finite set of points mentioned in a query trace. -/
def queriedPoints
    (trace : List (AnsweredQuery ℕ)) : Finset ℕ :=
  (trace.map fun qa => qa.1.2).toFinset

theorem query_point_mem_queriedPoints
    {trace : List (AnsweredQuery ℕ)} {k : ℕ}
    (hk : k < trace.length) :
    (trace.get ⟨k, hk⟩).1.2 ∈ queriedPoints trace := by
  simp only [queriedPoints, List.mem_toFinset, List.mem_map]
  exact
    ⟨trace.get ⟨k, hk⟩,
      List.get_mem trace ⟨k, hk⟩, rfl⟩

/-- A finite adaptive dialogue is unchanged if the target and every group are
modified only away from points that dialogue queried. -/
theorem traceValid_of_agree_on_queried
    {M : Algorithm ℕ Code}
    {target₀ target₁ : Set ℕ}
    {groups₀ groups₁ : ℕ → Set ℕ}
    {history : List ℕ} {trace : List (AnsweredQuery ℕ)}
    (hvalid : TraceValid M target₀ groups₀ history trace)
    (htarget : ∀ x, x ∈ queriedPoints trace →
      (x ∈ target₀ ↔ x ∈ target₁))
    (hgroups : ∀ i x, x ∈ queriedPoints trace →
      (x ∈ groups₀ i ↔ x ∈ groups₁ i)) :
    TraceValid M target₁ groups₁ history trace := by
  intro k hk
  have hpoint :=
    query_point_mem_queriedPoints (trace := trace) hk
  have hold := hvalid k hk
  refine ⟨hold.1, ?_⟩
  unfold AnswerCorrect at hold ⊢
  have hagree :
      ∀ q : Query ℕ, q.2 ∈ queriedPoints trace →
        (q.2 ∈ querySet target₀ groups₀ q ↔
          q.2 ∈ querySet target₁ groups₁ q) := by
    rintro ⟨kind, x⟩ hx
    cases kind with
    | none => exact htarget x hx
    | some i => exact hgroups i x hx
  exact hold.2.trans (hagree _ hpoint)

/-! ## Completing the adversarial partial group assignment -/

/-- Complete the group answers after a finite transcript: observed `red`
points and every still-unassigned point enter the first group; queried points
outside `red` remain in the complementary second group. -/
def completedFirstGroup
    (sample red queried : Finset ℕ) : Set ℕ :=
  (red : Set ℕ) ∪
    ((sample ∪ queried : Finset ℕ) : Set ℕ)ᶜ

theorem queried_mem_completedFirstGroup_iff
    {sample red queried : Finset ℕ}
    {x : ℕ} (hx : x ∈ queried) :
    x ∈ completedFirstGroup sample red queried ↔
      x ∈ red := by
  simp only [completedFirstGroup, Set.mem_union,
    Set.mem_compl_iff, Finset.coe_union,
    Finset.mem_coe]
  constructor
  · rintro (hxred | hxnot)
    · exact hxred
    · exact False.elim (hxnot (Or.inr hx))
  · exact Or.inl

theorem completedFirstGroup_agrees_on_queried
    {sample red queried : Finset ℕ}
    {x : ℕ} (hx : x ∈ queried) :
    (x ∈ (red : Set ℕ) ↔
      x ∈ completedFirstGroup sample red queried) :=
  (queried_mem_completedFirstGroup_iff hx).symm

theorem binaryGroups_agree_on_queried
    {sample red queried : Finset ℕ}
    {x : ℕ} (hx : x ∈ queried) (i : ℕ) :
    (x ∈ binaryGroups (red : Set ℕ) i ↔
      x ∈ binaryGroups
        (completedFirstGroup sample red queried) i) := by
  have hfirst :=
    completedFirstGroup_agrees_on_queried
      (sample := sample) (red := red) hx
  rcases i with _ | i
  · exact hfirst
  · rcases i with _ | i
    · exact not_congr hfirst
    · simp [binaryGroups]

theorem sample_filter_completedFirstGroup
    {sample red queried : Finset ℕ}
    (hred : red ⊆ sample) :
    @Finset.filter ℕ
        (fun x =>
          x ∈ completedFirstGroup sample red queried)
        (fun x => Classical.propDecidable
          (x ∈ completedFirstGroup sample red queried))
        sample = red := by
  classical
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxsample, hxred | hxoutside⟩
    · exact hxred
    · exact False.elim
        (hxoutside
          (Finset.mem_union_left queried hxsample))
  · intro hxred
    exact ⟨hred hxred, Or.inl hxred⟩

theorem empirical_completedFirstGroup_half
    {sample red queried : Finset ℕ}
    (hsample : sample.Nonempty)
    (hred : red ⊆ sample)
    (hhalf : sample.card ≤ 2 * red.card) :
    (1 / 2 : ℝ) ≤
      empiricalGroupProbability sample
        (binaryGroups
          (completedFirstGroup sample red queried)) 0 := by
  classical
  rw [empiricalGroupProbability]
  simp only [hsample, if_true, binaryGroups_zero]
  rw [sample_filter_completedFirstGroup hred]
  have hcardPositive : (0 : ℝ) < sample.card := by
    exact_mod_cast Finset.card_pos.mpr hsample
  rw [le_div_iff₀ hcardPositive]
  have hhalfReal :
      (sample.card : ℝ) ≤ 2 * red.card := by
    exact_mod_cast hhalf
  nlinarith

theorem target_remove_unqueried_agrees
    {queried : Finset ℕ} {x y : ℕ}
    (hx : x ∉ queried) (hy : y ∈ queried) :
    (y ∈ (Set.univ : Set ℕ) ↔
      y ∈ Set.univ \ {x}) := by
  simp only [Set.mem_univ, true_iff, Set.mem_diff,
    Set.mem_singleton_iff, true_and]
  intro hyx
  subst y
  exact hx hy

/-! ## The finite diagonal -/

/-- Kernel-checked finite-transcript core of published Lemma 4.9.

Initially every target query is answered positively, while indexed group
queries are answered according to the binary partition generated by `red`.
If the decoded output gives positive mass to an unqueried point, that point is
removed from the target without changing any recorded answer.  Otherwise,
consistency puts all positive output mass on queried second-group points, so
the representation error is at least one half.

This theorem is deliberately local to one completed round.  Its conclusion
preserves the exact adaptive trace and output code.  The full companion proof
uses the same invariance principle inside a simpler target-`univ`,
finite-mass-blocking construction. -/
theorem finiteTranscript_diagonal
    (M : Algorithm ℕ Code)
    (history : List ℕ) (red : Finset ℕ)
    (trace : List (AnsweredQuery ℕ)) (code : Code)
    (hsample : history.toFinset.Nonempty)
    (hred : red ⊆ history.toFinset)
    (hhalf : history.toFinset.card ≤ 2 * red.card)
    (hterm :
      TerminatesWith M Set.univ
        (binaryGroups (red : Set ℕ))
        history trace code) :
    ∃ target firstGroup : Set ℕ,
      target.Infinite ∧
      (history.toFinset : Set ℕ) ⊆ target ∧
      IsCountablePartition (binaryGroups firstGroup) ∧
      TerminatesWith M target (binaryGroups firstGroup)
        history trace code ∧
      (¬ SupportedOn (M.decode code)
          (target \ (history.toFinset : Set ℕ)) ∨
        ENNReal.ofReal (1 / 2 : ℝ) ≤
          groupSupDistance (M.decode code)
            history.toFinset (binaryGroups firstGroup)) := by
  classical
  let sample := history.toFinset
  let queried := queriedPoints trace
  let firstGroup :=
    completedFirstGroup sample red queried
  let μ := M.decode code
  have hgroupsAgree :
      ∀ i y, y ∈ queriedPoints trace →
        (y ∈ binaryGroups (red : Set ℕ) i ↔
          y ∈ binaryGroups firstGroup i) := by
    intro i y hy
    exact binaryGroups_agree_on_queried hy i
  have htermUniv :
      TerminatesWith M Set.univ
        (binaryGroups firstGroup)
        history trace code := by
    refine
      ⟨traceValid_of_agree_on_queried
          hterm.1 ?_ hgroupsAgree,
        hterm.2⟩
    intro y _
    simp
  by_cases hunseen :
      SupportedOn μ
        (Set.univ \ (sample : Set ℕ))
  · by_cases hqueried :
        SupportedOn μ (queried : Set ℕ)
    · refine
        ⟨Set.univ, firstGroup, Set.infinite_univ, ?_,
          binaryGroups_isCountablePartition firstGroup,
          htermUniv, Or.inr ?_⟩
      · intro y _
        simp
      · have hsupportedComplement :
            SupportedOn μ firstGroupᶜ := by
          intro y hmass
          have hyUnseen := hunseen y hmass
          have hyQueried := hqueried y hmass
          have hyNotSample : y ∉ sample :=
            hyUnseen.2
          have hyNotRed : y ∉ red := by
            intro hyRed
            exact hyNotSample (hred hyRed)
          have hyNotFirst : y ∉ firstGroup := by
            intro hyFirst
            rcases hyFirst with hyRed | hyOutside
            · exact hyNotRed hyRed
            · exact hyOutside
                (Finset.mem_union_right
                  sample hyQueried)
          exact hyNotFirst
        have hmassZero :
            groupMass μ firstGroup = 0 := by
          apply
            groupMass_eq_zero_of_supportedOn_of_disjoint
              hsupportedComplement
          exact disjoint_compl_left
        have hemp :
            (1 / 2 : ℝ) ≤
              empiricalGroupProbability sample
                (binaryGroups firstGroup) 0 := by
          exact
            empirical_completedFirstGroup_half
              hsample hred hhalf
        have hcoordinate :=
          coordinate_le_groupSupDistance μ sample
            (binaryGroups firstGroup) 0
        have hempNonnegative :=
          empiricalGroupProbability_nonnegative sample
            (binaryGroups firstGroup) 0
        rw [inducedGroupProbability, binaryGroups_zero,
          hmassZero, zero_sub, abs_neg,
          abs_of_nonneg hempNonnegative] at hcoordinate
        exact
          (ENNReal.ofReal_le_ofReal hemp).trans
            hcoordinate
    · simp only [SupportedOn] at hqueried
      push_neg at hqueried
      obtain ⟨x, hxMass, hxNotQueried⟩ :=
        hqueried
      have hxUnseen := hunseen x hxMass
      let target : Set ℕ := Set.univ \ {x}
      have htargetAgree :
          ∀ y, y ∈ queriedPoints trace →
            (y ∈ (Set.univ : Set ℕ) ↔
              y ∈ target) := by
        intro y hy
        exact
          target_remove_unqueried_agrees
            hxNotQueried hy
      have htermTarget :
          TerminatesWith M target
            (binaryGroups firstGroup)
            history trace code := by
        refine
          ⟨traceValid_of_agree_on_queried
              hterm.1 htargetAgree hgroupsAgree,
            hterm.2⟩
      refine
        ⟨target, firstGroup, ?_, ?_,
          binaryGroups_isCountablePartition firstGroup,
          htermTarget, Or.inl ?_⟩
      · dsimp [target]
        rw [← Set.compl_eq_univ_diff]
        exact (Set.finite_singleton x).infinite_compl
      · intro y hySample
        exact
          ⟨Set.mem_univ y,
            fun hyx => hxUnseen.2 (hyx ▸ hySample)⟩
      · intro hsupported
        have hxTargetUnseen :=
          hsupported x hxMass
        exact hxTargetUnseen.1.2 rfl
  · refine
      ⟨Set.univ, firstGroup, Set.infinite_univ, ?_,
        binaryGroups_isCountablePartition firstGroup,
        htermUniv, Or.inl ?_⟩
    · intro y _
      simp
    · simpa [sample, μ] using hunseen

end MembershipQuery
end GenLimit.RepresentativeGeneration
