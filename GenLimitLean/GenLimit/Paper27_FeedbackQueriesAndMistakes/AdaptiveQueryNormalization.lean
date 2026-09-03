import GenLimit.Paper27_FeedbackQueriesAndMistakes.QueryFeedback

/-!
# Finite adaptive membership-query normalization

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*Language Generation with Feedback: Queries and Mistakes*, ICML 2026.

The query development elsewhere in this directory uses a finite nonadaptive
table.  This file checks the source-facing semantic reduction behind that
normal form.  A finite adaptive binary query tree can be expanded by asking
every query at every node in advance.  The resulting complete answer table
contains answers for both branches; evaluating the table follows only the
branch selected by the answer at the current node.

This is an extensional, per-history normalization.  It makes no claim that
the complete table is query-efficient, and it does not identify an adaptive
tree of arbitrary size with the repository's particular `(t+1)^2` square
budget at the same round.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-- A finite binary membership-query decision tree.  The first subtree is
followed after a `false` answer and the second after a `true` answer. -/
inductive FiniteAdaptiveQueryTree (α β : Type*)
  | leaf : β → FiniteAdaptiveQueryTree α β
  | branch :
      α →
      FiniteAdaptiveQueryTree α β →
      FiniteAdaptiveQueryTree α β →
      FiniteAdaptiveQueryTree α β

/-- The number of membership-query nodes in a finite adaptive tree. -/
def adaptiveQueryNodeCount :
    FiniteAdaptiveQueryTree α β → ℕ
  | .leaf _ => 0
  | .branch _ falseTree trueTree =>
      1 + adaptiveQueryNodeCount falseTree +
        adaptiveQueryNodeCount trueTree

/-- The nonadaptive preorder plan obtained by listing every query in the
tree, including queries on branches that the truthful run will not follow. -/
def adaptiveQueryPlan :
    FiniteAdaptiveQueryTree α β → List α
  | .leaf _ => []
  | .branch query falseTree trueTree =>
      query ::
        (adaptiveQueryPlan falseTree ++ adaptiveQueryPlan trueTree)

@[simp] theorem adaptiveQueryPlan_length
    (tree : FiniteAdaptiveQueryTree α β) :
    (adaptiveQueryPlan tree).length = adaptiveQueryNodeCount tree := by
  induction tree with
  | leaf output =>
      rfl
  | branch query falseTree trueTree ihFalse ihTrue =>
      simp [adaptiveQueryPlan, adaptiveQueryNodeCount, ihFalse, ihTrue,
        Nat.add_assoc, Nat.add_comm]

/-- A complete finite table stores an answer at every branch node, including
both recursively unchosen subtrees. -/
inductive CompleteAdaptiveAnswerTable :
    FiniteAdaptiveQueryTree α β → Type
  | leaf {output : β} :
      CompleteAdaptiveAnswerTable (.leaf output)
  | branch
      {query : α}
      {falseTree trueTree : FiniteAdaptiveQueryTree α β}
      (answer : Bool)
      (falseAnswers : CompleteAdaptiveAnswerTable falseTree)
      (trueAnswers : CompleteAdaptiveAnswerTable trueTree) :
      CompleteAdaptiveAnswerTable
        (.branch query falseTree trueTree)

/-- Preorder serialization of a complete answer table. -/
def completeAdaptiveAnswerList :
    {tree : FiniteAdaptiveQueryTree α β} →
      CompleteAdaptiveAnswerTable tree → List Bool
  | .leaf _, .leaf => []
  | .branch _ _ _, .branch answer falseAnswers trueAnswers =>
      answer ::
        (completeAdaptiveAnswerList falseAnswers ++
          completeAdaptiveAnswerList trueAnswers)

@[simp] theorem completeAdaptiveAnswerList_length
    {tree : FiniteAdaptiveQueryTree α β}
    (table : CompleteAdaptiveAnswerTable tree) :
    (completeAdaptiveAnswerList table).length =
      adaptiveQueryNodeCount tree := by
  induction table with
  | leaf =>
      rfl
  | branch answer falseAnswers trueAnswers ihFalse ihTrue =>
      simp [completeAdaptiveAnswerList, adaptiveQueryNodeCount,
        ihFalse, ihTrue, Nat.add_assoc, Nat.add_comm]

/-- Fill the complete table truthfully by querying every node in advance. -/
noncomputable def truthfulCompleteAdaptiveAnswerTable
    (target : Set α) :
    (tree : FiniteAdaptiveQueryTree α β) →
      CompleteAdaptiveAnswerTable tree
  | .leaf _ => .leaf
  | .branch query falseTree trueTree =>
      .branch
        (membershipAnswer target query)
        (truthfulCompleteAdaptiveAnswerTable target falseTree)
        (truthfulCompleteAdaptiveAnswerTable target trueTree)

/-- The serialized truthful table is exactly the pointwise membership-answer
map over the finite nonadaptive query plan. -/
theorem truthfulCompleteAdaptiveAnswerList_eq_map
    (target : Set α)
    (tree : FiniteAdaptiveQueryTree α β) :
    completeAdaptiveAnswerList
        (truthfulCompleteAdaptiveAnswerTable target tree) =
      (adaptiveQueryPlan tree).map (membershipAnswer target) := by
  induction tree with
  | leaf output =>
      rfl
  | branch query falseTree trueTree ihFalse ihTrue =>
      simp [truthfulCompleteAdaptiveAnswerTable,
        completeAdaptiveAnswerList, adaptiveQueryPlan, ihFalse, ihTrue]

/-- Evaluate an adaptive tree against a membership oracle. -/
noncomputable def evaluateAdaptiveQueryTree
    (target : Set α) :
    FiniteAdaptiveQueryTree α β → β
  | .leaf output => output
  | .branch query falseTree trueTree =>
      if membershipAnswer target query = true then
        evaluateAdaptiveQueryTree target trueTree
      else
        evaluateAdaptiveQueryTree target falseTree

/-- Evaluate a tree using a complete answer table.  Answers stored below the
unchosen branch remain unused. -/
def evaluateCompleteAdaptiveAnswerTable :
    (tree : FiniteAdaptiveQueryTree α β) →
      CompleteAdaptiveAnswerTable tree → β
  | .leaf output, .leaf => output
  | .branch _ falseTree trueTree,
      .branch answer falseAnswers trueAnswers =>
      if answer = true then
        evaluateCompleteAdaptiveAnswerTable trueTree trueAnswers
      else
        evaluateCompleteAdaptiveAnswerTable falseTree falseAnswers

/-- Exact finite adaptive-to-nonadaptive normalization: precomputing the
truthful answers at every node preserves the adaptive output. -/
theorem evaluateComplete_truthful_eq_evaluateAdaptive
    (target : Set α)
    (tree : FiniteAdaptiveQueryTree α β) :
    evaluateCompleteAdaptiveAnswerTable tree
        (truthfulCompleteAdaptiveAnswerTable target tree) =
      evaluateAdaptiveQueryTree target tree := by
  induction tree with
  | leaf output =>
      rfl
  | branch query falseTree trueTree ihFalse ihTrue =>
      simp only [truthfulCompleteAdaptiveAnswerTable,
        evaluateCompleteAdaptiveAnswerTable, evaluateAdaptiveQueryTree]
      split_ifs <;> assumption

/-! ## Ordered positive-history wrapper -/

/-- An auxiliary within-round adaptive query strategy whose finite tree may
depend on the complete ordered positive history visible at the current round.
The source model instead asks one query across each round. -/
structure PositiveSequenceAdaptiveSetQueryStrategy (α : Type*) where
  tree :
    ∀ t, (Fin t → α) →
      FiniteAdaptiveQueryTree α (Set α)

/-- The output of the adaptive interaction at one ordered history. -/
noncomputable def positiveSequenceAdaptiveSetQueryOutput
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Set α :=
  evaluateAdaptiveQueryTree target
    (strategy.tree t (fun i => stream i))

/-- The same output obtained by materializing the complete answer table
before evaluating the selected branch. -/
noncomputable def positiveSequenceCompleteTableQueryOutput
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Set α :=
  let tree := strategy.tree t (fun i => stream i)
  evaluateCompleteAdaptiveAnswerTable tree
    (truthfulCompleteAdaptiveAnswerTable target tree)

theorem positiveSequenceAdaptive_output_eq_completeTable
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceAdaptiveSetQueryOutput
        strategy target stream t =
      positiveSequenceCompleteTableQueryOutput
        strategy target stream t := by
  simp only [positiveSequenceAdaptiveSetQueryOutput,
    positiveSequenceCompleteTableQueryOutput]
  exact
    (evaluateComplete_truthful_eq_evaluateAdaptive target
      (strategy.tree t (fun i => stream i))).symm

/-- Eventual generation for the adaptive-tree semantics. -/
def PositiveSequenceAdaptiveSetQuerySucceedsOn
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      (positiveSequenceAdaptiveSetQueryOutput
        strategy target stream t).Infinite ∧
      positiveSequenceAdaptiveSetQueryOutput
        strategy target stream t ⊆ target

/-- The same eventual property evaluated through complete nonadaptive
tables. -/
def PositiveSequenceCompleteTableQuerySucceedsOn
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      (positiveSequenceCompleteTableQueryOutput
        strategy target stream t).Infinite ∧
      positiveSequenceCompleteTableQueryOutput
        strategy target stream t ⊆ target

/-- Complete-table expansion preserves eventual set generation, not merely
the output at one fixed history. -/
theorem positiveSequenceAdaptive_succeedsOn_iff_completeTable
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (target : Set α) :
    PositiveSequenceAdaptiveSetQuerySucceedsOn strategy target ↔
      PositiveSequenceCompleteTableQuerySucceedsOn strategy target := by
  constructor
  · intro hAdaptive stream hPresents
    obtain ⟨T, hT⟩ := hAdaptive stream hPresents
    refine ⟨T, ?_⟩
    intro t hTt
    rw [← positiveSequenceAdaptive_output_eq_completeTable]
    exact hT t hTt
  · intro hComplete stream hPresents
    obtain ⟨T, hT⟩ := hComplete stream hPresents
    refine ⟨T, ?_⟩
    intro t hTt
    rw [positiveSequenceAdaptive_output_eq_completeTable]
    exact hT t hTt

def PositiveSequenceAdaptiveSetQueryGenerates
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ target, target ∈ targets →
    PositiveSequenceAdaptiveSetQuerySucceedsOn strategy target

def PositiveSequenceCompleteTableQueryGenerates
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ target, target ∈ targets →
    PositiveSequenceCompleteTableQuerySucceedsOn strategy target

theorem positiveSequenceAdaptive_generates_iff_completeTable
    (strategy : PositiveSequenceAdaptiveSetQueryStrategy α)
    (targets : LanguageClass α) :
    PositiveSequenceAdaptiveSetQueryGenerates strategy targets ↔
      PositiveSequenceCompleteTableQueryGenerates strategy targets := by
  constructor
  · intro h target htarget
    exact
      (positiveSequenceAdaptive_succeedsOn_iff_completeTable
        strategy target).mp (h target htarget)
  · intro h target htarget
    exact
      (positiveSequenceAdaptive_succeedsOn_iff_completeTable
        strategy target).mpr (h target htarget)

end GenLimit.FeedbackQueries
