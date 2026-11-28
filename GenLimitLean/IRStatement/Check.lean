import Lean.Elab.Command
import Lean.Elab.SyntheticMVars
import Lean.Util.Sorry

open Lean Elab Command

/--
`#check_statement name against P` checks that the kernel considers the full declared
type of `name` definitionally equal to the proposition `P`. Write all theorem
parameters as binders in `P`. The declaration's universe names are in scope.
-/
def IRStatement.checkReading (info : ConstantInfo) (prop : Syntax) : CommandElabM Unit := do
  let name := info.name
  liftTermElabM do
    Term.withLevelNames info.levelParams do
      let candidate ← Term.elabTermEnsuringType prop (some (mkSort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      let candidate ← instantiateMVars candidate
      if candidate.hasExprMVar || candidate.hasFVar || candidate.hasSorry then
        throwErrorAt prop "the statement must be closed and contain no holes or sorry"

      -- Only inferred universe levels in the candidate may be instantiated.
      -- The reference type is taken verbatim from the environment with rigid levels.
      if candidate.hasLevelMVar then
        discard <| Meta.withTransparency .all <| Meta.isDefEq candidate info.type
      let candidate ← instantiateMVars candidate
      if candidate.hasLevelMVar then
        throwErrorAt prop "unresolved universe levels in statement for '{name}'; specify the universes"

      let env ← getEnv
      discard <| ofExceptKernelException (Kernel.check env {} candidate)
      unless ← ofExceptKernelException (Kernel.isDefEq env {} candidate info.type) do
        withOptions (fun opts => opts.setBool `pp.universes true) do
          throwErrorAt prop m!"statement mismatch for '{name}'\n  IR:   {candidate}\n  Lean: {info.type}"

elab "#check_statement " decl:ident " against " prop:term : command => do
  let info ← getConstInfo (← resolveGlobalConstNoOverload decl)
  IRStatement.checkReading info prop
