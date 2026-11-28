import Lean

/-!
# Definition statements for the glossary

`#ir_glossary c` adds the theorem `IRGlossary.c`, which states what `c` means:
* `∀ x₁ … xₙ, c x₁ … xₙ ↔ body` when `c x₁ … xₙ` is a proposition, and
* `∀ x₁ … xₙ, c x₁ … xₙ = body` otherwise,

where `fun x₁ … xₙ => body` is the value of `c`. The proof is `Iff.rfl` or `rfl` under the
binders, so the kernel accepts the theorem only if `body` is the definition of `c`, unfolded
once. The glossary reading of `c` is then checked against this theorem like any other reading.
Only plain definitions qualify: not theorems, axioms, opaque constants, structure
projections or definitions by recursion (their values are not their equations).
-/

namespace IRStatement.Glossary
open Lean Meta Elab Command

/-- The name of the definition statement of `c`. -/
def statementName (c : Name) : Name := `IRGlossary ++ c

elab "#ir_glossary " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let .defnInfo d := (← getConstInfo c) | throwError "{c} is not a definition"
  if (← liftCoreM <| isProjectionFn c) then throwError "{c} is a structure projection"
  -- A compiled recursion or pattern match is not the definition as written.
  let compiled (n : Name) : Bool :=
    let last := n.components.getLast?.map (·.toString) |>.getD ""
    n == c || n.isInternal || last.startsWith "match_" || last.startsWith "proof_" ||
      ["brecOn", "rec", "recOn", "casesOn", "below", "fix", "fixF"].contains last
  if (d.value.find? fun e => e.isConst && compiled e.constName!).isSome || env.contains (c ++ `_unsafe_rec) then
    throwError "{c} is defined by recursion or pattern matching"
  let us := d.levelParams.map Level.param
  let (type, proof, kind) ← liftTermElabM do
    lambdaTelescope (d.value.instantiateLevelParams d.levelParams us) fun xs body => do
      let lhs := mkAppN (.const c us) xs
      if ← isProp lhs then
        return (← mkForallFVars xs (mkIff lhs body),
                ← mkLambdaFVars xs (mkApp (.const ``Iff.refl []) lhs), "prop")
      else
        let kind := if (← whnf (← inferType lhs)).isSort then "type" else "data"
        return (← mkForallFVars xs (← mkEq lhs body), ← mkLambdaFVars xs (← mkEqRefl lhs), kind)
  liftCoreM <| addDecl <| .thmDecl { name := statementName c, levelParams := d.levelParams, type, value := proof }
  -- Where the definition is, and what it defines: a proposition, a type, or other data.
  let main ← getMainModule
  let file := match env.getModuleIdxFor? c with
    | some i => env.header.moduleNames[i.toNat]!.toString
    | none => main.toString
  let line := (← liftCoreM <| findDeclarationRanges? c).map (·.range.pos.line) |>.getD 0
  logInfo (Json.compress (Json.arr #["definition", toJson c.toString, toJson kind, toJson file, toJson line]))

end IRStatement.Glossary
