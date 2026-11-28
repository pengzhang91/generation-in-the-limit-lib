import IRStatement.Check
import GenLimit.Core.Basic
import GenLimit.Core.GenericGeneration
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Find

/-!
# Formal vocabulary of the IR statement reader

Three Lean devices give formal meaning to English phrases that have no single
library constant. Each is reviewed once, here, and then used by every reading.
The kernel comparison in `#check_statement` decides whether a reading that uses
them agrees with the declared theorem.
-/

namespace IRStatement
open Lean Elab Term Meta

/-- "the sequence that lists the elements of `A` in increasing order":
the least element of `A`, then repeatedly the least element above the previous one.
The infinitude proof only guarantees that each search succeeds. -/
def increasingEnumeration (A : Set ℕ) [DecidablePred (· ∈ A)] (h : A.Infinite) : ℕ → ℕ
  | 0 => Nat.find h.nonempty
  | k + 1 => Nat.find (h.exists_gt (increasingEnumeration A h k))

/-- "{stream(n) : n < t}": the finite set of the first `t` terms of a stream.
The library has two definitions of this set, both `(Finset.range t).image stream`.
`GenLimit.sample` (universe `ℕ`) decides equality computably, while
`GenLimit.Generic.sample` uses classical decidability. Instance resolution picks the
one that matches the element type, so one English phrase covers both. -/
class FirstTerms (α : Type u) where
  firstTerms : (ℕ → α) → ℕ → Finset α

instance (priority := high) natFirstTerms : FirstTerms ℕ := ⟨GenLimit.sample⟩
noncomputable instance (priority := low) genericFirstTerms {α : Type u} : FirstTerms α :=
  ⟨GenLimit.Generic.sample⟩

/-- `depends_only% [x, y, …] P` elaborates `P` after checking that the displayed names are
exactly the variables then in scope, in order. Hypotheses, instance arguments and local
definitions are not counted: a choice cannot usefully depend on a proof, and a local
definition depends only on earlier variables. The check runs at elaboration time and
leaves no trace in the term, so it cannot affect the kernel comparison. It makes the
English phrase "depending only on x, y, …" part of what is checked. -/
syntax (name := dependsOnly) "depends_only% " "[" ident,* "]" term:max : term

@[term_elab dependsOnly] def elabDependsOnly : TermElab := fun stx expected? => do
  let listed := stx[2].getSepArgs.map (·.getId)
  let mut visible := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || d.isLet || d.binderInfo.isInstImplicit then continue
    if ← isProp d.type then continue
    visible := visible.push d.userName
  unless visible == listed do
    throwErrorAt stx "the reading says the choice depends only on {listed}, \
      but the variables in scope are {visible}"
  elabTerm stx[4] expected?

end IRStatement
