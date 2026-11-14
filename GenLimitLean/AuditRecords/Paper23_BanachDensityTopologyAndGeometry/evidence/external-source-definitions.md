# Neutral external definition supplement

Exact source-definition excerpts from the pinned Mathlib dependency, with doc comments removed. No theorem proofs or source-paper interpretations. Typeclass context is shown in each class declaration; Order.pred uses variables {α : Type*} [Preorder α] [PredOrder α]. Function-iteration notation is Nat.iterate. This supplement does not modify the frozen Stage 1 inputs.

## Mathlib/Order/SuccPred/Basic.lean:59

```lean
class PredOrder (α : Type*) [Preorder α] where
  pred : α → α
  pred_le : ∀ a, pred a ≤ a
  min_of_le_pred {a} : a ≤ pred a → IsMin a
  le_pred_of_lt {a b} : a < b → a ≤ pred b
```

## Mathlib/Order/SuccPred/Archimedean.lean:29

```lean
class IsPredArchimedean (α : Type*) [Preorder α] [PredOrder α] : Prop where
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, pred^[n] b = a
```

## Mathlib/Order/Max.lean:168

```lean
def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b
```

## Mathlib/Order/SuccPred/Basic.lean:564

```lean
def pred : α → α :=
  PredOrder.pred
```

## Mathlib/Logic/Function/Iterate.lean:41

```lean
notation:max f "^["n"]" => Nat.iterate f n
```
