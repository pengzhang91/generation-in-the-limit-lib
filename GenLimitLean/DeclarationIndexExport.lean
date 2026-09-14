import GenLimit
import Lean.Elab.Command
import Lean.PrivateName
import Lean.Util.FoldConsts
import Lean.Util.Path

/-!
# Declaration-level index export

This standalone exporter reads the compiled `GenLimit` environment and emits
one JSON record for every public, user-facing project declaration.  The
companion `scripts/build_declaration_index.py` enriches these records with
claim-registry links and writes the tracked retrieval index under
`registry/generated/`.

The exporter deliberately excludes private names, implementation-detail
names, recursors, quotient internals, and standard generated eliminator,
injectivity, constructor-index, and size declarations.  It records exact
pretty-printed types, defining modules, source positions, direct project
dependencies, and direct abbreviation targets.  Source positions are null for
the small number of useful elaborator-generated equation declarations that do
not carry a declaration range.  The exporter does not infer paper
correspondence or source faithfulness.
-/

open Lean Elab Command

private def projectModule (moduleName : Name) : Bool :=
  moduleName == `GenLimit || (`GenLimit).isPrefixOf moduleName

private def generatedDeclarationName (declaration : Name) : Bool :=
  let rendered := declaration.toString
  [ ".below"
  , ".brecOn"
  , ".casesOn"
  , ".congr_simp"
  , ".ctorElim"
  , ".ctorElimType"
  , ".ctorIdx"
  , ".decEq"
  , ".elim"
  , ".ibelow"
  , ".inj"
  , ".injEq"
  , ".noConfusion"
  , ".noConfusionType"
  , ".ofNat"
  , ".ofNat_ctorIdx"
  , ".recOn"
  , ".sizeOf_spec"
  , ".toCtor"
  , ".toCtorIdx"
  ].any rendered.endsWith

private def declarationModule? (environment : Environment)
    (declaration : Name) : Option Name := do
  let moduleIndex ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[moduleIndex.toNat]?

private def publicDeclarationName (declaration : Name) : Bool :=
  (`GenLimit).isPrefixOf declaration &&
    !isPrivateName declaration &&
    !declaration.hasMacroScopes &&
    !declaration.isInternalDetail &&
    !generatedDeclarationName declaration

private def publicProjectDeclaration (environment : Environment)
    (declaration : Name) : Bool :=
  publicDeclarationName declaration &&
    (declarationModule? environment declaration).any projectModule

private def declarationKind? (environment : Environment)
    (information : ConstantInfo) : Option String :=
  if Meta.isInstanceCore environment information.name then
    some "instance"
  else
    match information with
    | .thmInfo _ => some "theorem"
    | .defnInfo value =>
        if environment.isProjectionFn value.name then
          some "projection"
        else
          match value.hints with
          | .abbrev => some "abbrev"
          | _ => some "definition"
    | .opaqueInfo _ => some "opaque"
    | .inductInfo value =>
        if isStructure environment value.name then
          some "structure"
        else
          some "inductive"
    | .ctorInfo _ => some "constructor"
    | .axiomInfo _ => some "postulate"
    | .quotInfo _ | .recInfo _ => none

private def declarationSafety (information : ConstantInfo) : String :=
  match information with
  | .defnInfo value =>
      match value.safety with
      | .safe => "safe"
      | .unsafe => "unsafe"
      | .partial => "partial"
  | _ => if information.isUnsafe then "unsafe" else "safe"

private def directProjectDependencies (environment : Environment)
    (declaration : Name) (expression : Expr) : Array Name := Id.run do
  let candidates := (expression.getUsedConstants.filter fun dependency =>
        dependency != declaration &&
          publicProjectDeclaration environment dependency &&
          (environment.find? dependency).any fun information =>
            (declarationKind? environment information).isSome)
    |>.qsort Name.lt
  let mut result := #[]
  for candidate in candidates do
    if result.back? != some candidate then
      result := result.push candidate
  return result

private partial def expressionHeadConstant? : Expr → Option Name
  | .const name _ => some name
  | .app function _ => expressionHeadConstant? function
  | .lam _ _ body _ => expressionHeadConstant? body
  | .letE _ _ _ body _ => expressionHeadConstant? body
  | .mdata _ body => expressionHeadConstant? body
  | _ => none

private def directAbbreviationTarget? (environment : Environment)
    (information : ConstantInfo) : Option Name := do
  let .defnInfo value := information | none
  let .abbrev := value.hints | none
  let target ← expressionHeadConstant? value.value
  if target != information.name &&
      publicProjectDeclaration environment target &&
      (environment.find? target).any fun targetInformation =>
        (declarationKind? environment targetInformation).isSome then
    some target
  else
    none

private def renderDeclarationType (type : Expr) : CommandElabM String := do
  let rendered ← liftTermElabM <| Meta.ppExpr type
  return rendered.pretty 120

private def namesToJson (names : Array Name) : Json :=
  toJson (names.toList.map Name.toString)

private def optionalNameToJson : Option Name → Json
  | some name => toJson name.toString
  | none => Json.null

private def optionalStringToJson : Option String → Json
  | some value => toJson value
  | none => Json.null

private def optionalNatToJson : Option Nat → Json
  | some value => toJson value
  | none => Json.null

elab "export_declaration_index" : command => do
  let environment ← getEnv
  let mut declarations := #[]
  for moduleName in environment.header.moduleNames do
    if projectModule moduleName then
      let modulePath ← liftIO <| findOLean moduleName
      let (moduleData, _) ← liftIO <| readModuleData modulePath
      for name in moduleData.constNames do
        if publicDeclarationName name then
          if let some information := environment.find? name then
            if (declarationKind? environment information).isSome then
              declarations := declarations.push name
  let sortedDeclarations := declarations.qsort Name.lt
  declarations := #[]
  for declaration in sortedDeclarations do
    if declarations.back? != some declaration then
      declarations := declarations.push declaration
  for declaration in declarations do
    let some information := environment.find? declaration
      | throwError "declaration disappeared while exporting: {declaration}"
    let some moduleName := declarationModule? environment declaration
      | throwError "cannot determine defining module for {declaration}"
    let some kind := declarationKind? environment information
      | throwError "unsupported declaration kind for {declaration}"
    let typeDependencies :=
      directProjectDependencies environment declaration information.type
    let bodyDependencies :=
      match information.value? true with
      | some value => directProjectDependencies environment declaration value
      | none => #[]
    let sourceLine :=
      (← findDeclarationRanges? declaration).map fun ranges =>
        ranges.selectionRange.pos.line
    let docstring ← findDocString? environment declaration false
    let payload := Json.mkObj
      [ ("name", toJson declaration.toString)
      , ("kind", toJson kind)
      , ("module", toJson moduleName.toString)
      , ("source_line", optionalNatToJson sourceLine)
      , ("type", toJson (← renderDeclarationType information.type))
      , ("type_dependencies", namesToJson typeDependencies)
      , ("body_dependencies", namesToJson bodyDependencies)
      , ("direct_abbreviation_target",
          optionalNameToJson (directAbbreviationTarget? environment information))
      , ("docstring", optionalStringToJson docstring)
      , ("safety", toJson (declarationSafety information))
      ]
    liftIO <| IO.println s!"DECLARATION_INDEX {payload.compress}"

export_declaration_index
