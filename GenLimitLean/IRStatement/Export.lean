import Lean

/-!
# Structural export for the IR statement reader

`#ir_export decl unfolding c₁ c₂ …` prints the full elaborated type of `decl` as a JSON
tree. It keeps the structure of every subterm, so that the Python selector can choose
GF constructions by the shape of the expression. Each listed definition is delta-expanded
where it occurs; the node `unfolded` records the constant and its explicit arguments next
to the body.

Node shapes (all JSON arrays):
* `["forall", name, binderInfo, domainIsProp, usesBinder, dom, body]`
* `["exists", name, domainIsProp, dom, body]`
* `["and" | "or" | "iff", a, b]`, `["not", a]`
* `["let", name, type, value, body]`, `["lam", name, dom, body, bodyIsProp]`
* `["var", name, [explicit args]]` — a local, possibly applied
* `["const", name, [explicit args]]` — a constant, possibly applied; a membership `Membership.mem` adds
  the head constant of its collection type as a fourth element. An argument of a constant that is a
  proof is `["proof", parameter name, tree, provable]`, where `provable` says whether `hiddenTactic`
  proves the argument's type in its local context, so that a reading may leave the proof to Lean
* `["nat", n]`, `["sort", text]`, `["unfolded", const, [explicit args], body]`
-/

namespace IRStatement.Export
open Lean Meta Elab Command

private def arr (xs : List Json) : Json := Json.arr xs.toArray

/-- How a reading proves a proof argument that it does not show and that is not a hypothesis in
scope. `reader.py` writes the same tactic into the readings' Lean form. -/
def hiddenTactic : String := "first | assumption | linarith | positivity | simp_all +zetaDelta"

/-- Whether `hiddenTactic` proves `ty` in the current local context. Nothing is kept: the state,
including any message the attempt logs, is restored. -/
private def tacticProves (ty : Expr) : TermElabM Bool := do
  let .ok stx := Parser.runParserCategory (← getEnv) `tactic hiddenTactic | return false
  let saved ← saveState
  let ok ← try
      let goal ← mkFreshExprMVar ty
      let rest ← Tactic.run goal.mvarId! (Tactic.evalTactic stx)
      pure (rest.isEmpty && !(← MonadLog.hasErrors))
    catch _ => pure false
  saved.restore
  return ok

private def text (e : Expr) : MetaM String := do
  if let .sort (.succ (.param _)) := e then return "Type _"
  return toString (← ppExpr e)

/-- Explicit arguments of an application, in order. Implicit and instance
arguments are recovered by Lean when the reading is elaborated again. An explicit argument
that is a proof comes with the name of its parameter, so that a reading may leave it to Lean
as a named argument `(h := by assumption)`. -/
private def explicitArgs (f : Expr) (args : Array Expr) : MetaM (Array (Expr × Option Name)) := do
  let info ← getFunInfoNArgs f args.size
  let mut ty ← inferType f
  let mut out := #[]
  for h : i in [0:args.size] do
    let explicit := match info.paramInfo[i]? with
      | some p => p.binderInfo.isExplicit
      | none => true
    ty ← whnf ty
    let param := if ty.isForall then some ty.bindingName! else none
    ty := if ty.isForall then ty.bindingBody!.instantiate1 args[i] else ty
    if explicit then
      let proof ← isProof args[i]
      out := out.push (args[i], if proof then param else none)
  return out

/-- An explicit argument: `["proof", parameter, tree, provable]` for a proof, else its tree. -/
private def argTree (tree : Expr → TermElabM Json) (a : Expr × Option Name) : TermElabM Json := do
  match a.2 with
  | some n => return Json.arr #[toJson "proof", toJson n.toString, ← tree a.1,
      toJson (← tacticProves (← inferType a.1))]
  | none => tree a.1

partial def tree (unfold : Array Name) (e : Expr) : TermElabM Json := do
  let e := e.consumeMData
  let fresh (n : Name) (prop : Bool) : TermElabM Name := do
    let base := if n.isInternal || n.isAnonymous then (if prop then `h else `x) else n.eraseMacroScopes
    return (← getLCtx).getUnusedName base
  match e with
  | .forallE n dom body bi =>
    let prop ← isProp dom
    let name ← fresh n prop
    let domJ ← tree unfold dom
    withLocalDecl name bi dom fun x => do
      let bodyJ ← tree unfold (body.instantiate1 x)
      let info := if bi.isInstImplicit then "inst" else if bi.isImplicit then "implicit"
        else if bi.isStrictImplicit then "strict" else "default"
      return arr [toJson "forall", toJson name.toString, toJson info, toJson prop,
        toJson body.hasLooseBVars, domJ, bodyJ]
  | .lam n dom body bi =>
    let name ← fresh n (← isProp dom)
    let domJ ← tree unfold dom
    withLocalDecl name bi dom fun x => do
      let b := body.instantiate1 x
      return arr [toJson "lam", toJson name.toString, domJ, ← tree unfold b, toJson (← isProp b)]
  | .letE n ty value body _ =>
    let name ← fresh n false
    let tyJ ← tree unfold ty
    let valJ ← tree unfold value
    withLetDecl name ty value fun x => do
      return arr [toJson "let", toJson name.toString, tyJ, valJ, ← tree unfold (body.instantiate1 x)]
  | .sort _ => return arr [toJson "sort", toJson (← text e)]
  | .lit (.natVal n) => return arr [toJson "nat", toJson n]
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      if let some n := e.getAppArgs[1]!.rawNatLit? then return arr [toJson "nat", toJson n]
    let f := e.getAppFn
    let args := e.getAppArgs
    -- An unfolded body may apply a λ-argument, as in `(fun i => …) i`; read its β-reduct.
    if f.isLambda then
      return ← tree unfold e.headBeta
    if let .const c _ := f then
      if c == ``Exists && args.size == 2 then
        if let .lam n dom body bi := args[1]! then
          let prop ← isProp dom
          let name ← fresh n prop
          let domJ ← tree unfold dom
          return ← withLocalDecl name bi dom fun x => do
            return arr [toJson "exists", toJson name.toString, toJson prop, domJ,
              ← tree unfold (body.instantiate1 x)]
      for (k, tag) in [(``And, "and"), (``Or, "or"), (``Iff, "iff")] do
        if c == k && args.size == 2 then
          return arr [toJson tag, ← tree unfold args[0]!, ← tree unfold args[1]!]
      if c == ``Not && args.size == 1 then
        return arr [toJson "not", ← tree unfold args[0]!]
      let shown ← (← explicitArgs f args).mapM (argTree (tree unfold))
      -- A membership also records the head of its collection type (Set, Finset, List, …),
      -- so that the selector combines `x ∈ A ∧ x ∉ B` into `x ∈ A ∖ B` only for sets.
      if c == ``Membership.mem && args.size ≥ 2 then
        let head := (← whnfR args[1]!).getAppFn.constName?.map toString |>.getD ""
        return arr [toJson "const", toJson c.toString, Json.arr shown, toJson head]
      if unfold.contains c then
        if let some body ← delta? e (· == c) then
          return arr [toJson "unfolded", toJson c.toString, Json.arr shown, ← tree unfold body.headBeta]
      return arr [toJson "const", toJson c.toString, Json.arr shown]
    if f.isFVar then
      let shown ← (← explicitArgs f args).mapM (fun a => tree unfold a.1)
      return arr [toJson "var", toJson (← text f), Json.arr shown]
    -- Anything else (projections, literals, metadata-free oddities) is kept as text, so the
    -- selector can report it rather than the export failing.
    return arr [toJson "other", toJson (← text e)]

elab "#ir_export " decl:ident " unfolding " cs:ident* : command => do
  let info ← getConstInfo (← resolveGlobalConstNoOverload decl)
  -- A listed definition that this declaration's imports do not contain is simply not unfolded.
  let unfold ← cs.filterMapM fun c => do
    try some <$> liftCoreM (realizeGlobalConstNoOverloadWithInfo c) catch _ => pure none
  let json ← liftTermElabM <| tree unfold info.type
  logInfo (Json.compress (arr [toJson info.name.toString, json]))

end IRStatement.Export
