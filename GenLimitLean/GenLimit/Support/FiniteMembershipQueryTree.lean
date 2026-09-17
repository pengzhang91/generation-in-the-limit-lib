import Mathlib.Data.List.Basic

/-!
# Finite adaptive membership-query trees

This module contains the paper-independent tree kernel shared by Papers 08
and 27.  A branch stores one query, followed by the subtree for a `false`
answer and the subtree for a `true` answer.  The oracle and the leaf result
type are parameters, so the same tree supports Boolean detectors as well as
set-valued feedback strategies.
-/

namespace GenLimit.Support.FiniteMembershipQueryTree

/-- A finite binary adaptive-query tree. -/
inductive Tree (α β : Type*) where
  | leaf : β → Tree α β
  | branch : α → Tree α β → Tree α β → Tree α β

/-- The number of query nodes in a finite tree. -/
@[simp] def nodeCount : Tree α β → ℕ
  | .leaf _ => 0
  | .branch _ falseTree trueTree =>
      1 + nodeCount falseTree + nodeCount trueTree

/-- List every query in preorder, including queries on both branches. -/
@[simp] def queryPlan : Tree α β → List α
  | .leaf _ => []
  | .branch query falseTree trueTree =>
      query :: (queryPlan falseTree ++ queryPlan trueTree)

@[simp] theorem queryPlan_length (tree : Tree α β) :
    (queryPlan tree).length = nodeCount tree := by
  induction tree with
  | leaf output =>
      rfl
  | branch query falseTree trueTree ihFalse ihTrue =>
      simp [queryPlan, nodeCount, ihFalse, ihTrue, Nat.add_assoc, Nat.add_comm]

/-- Evaluate a tree with a Boolean answer oracle. -/
@[simp] def evaluate (answer : α → Bool) : Tree α β → β
  | .leaf output => output
  | .branch query falseTree trueTree =>
      if answer query = true then
        evaluate answer trueTree
      else
        evaluate answer falseTree

end GenLimit.Support.FiniteMembershipQueryTree
