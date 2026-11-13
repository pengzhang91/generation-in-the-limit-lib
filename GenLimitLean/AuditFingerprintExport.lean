import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper00_LanguageIdentification
import GenLimit.Paper01_LanguageGeneration.Semantic
import GenLimit.Paper01_LanguageGeneration.Results.Overview
import GenLimit.Paper01_LanguageGeneration.Results.Transport
import GenLimit.Paper02_LearningTheory.Results.Overview
import GenLimit.Paper03_HallucinationAndModeCollapse.Results.Overview
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Results.Overview
import GenLimit.Paper06_NoisyExamples.Results.Overview
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Overview
import GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview
import GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Overview
import GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview
import GenLimit.Paper28_ContrastiveGeneration.Results.Overview
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.Results.Overview
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Overview
import GenLimit.Paper31_BoundedMemory.Results.Overview
import GenLimit.Paper39_DenseGeneration.Results.Overview
import Lean.Elab.Command

/-!
# Human-audit applicability fingerprint export

This file exports normalized Lean expressions for declarations explicitly
listed as anchors of a completed human audit.  The companion Python checker
hashes those expressions with SHA-256 and compares them with the last reviewed
baseline under `AuditRecords/Human/Fingerprints/`.

Theorem anchors export only their types.  Definition anchors export both type
and value, so proof-only changes to a theorem do not invalidate a statement
or construction fingerprint.  Audit scopes that include proof-body
correspondence still require a separate manual maintenance assessment.
-/

open Lean Elab Command

/-- Remove expression metadata and semantically irrelevant local binder names
before producing a structural representation. -/
private partial def normalizeAuditExpr : Expr → Expr
  | .mdata _ body => normalizeAuditExpr body
  | .app fn arg =>
      .app (normalizeAuditExpr fn) (normalizeAuditExpr arg)
  | .lam _ domain body binderInfo =>
      .lam .anonymous (normalizeAuditExpr domain)
        (normalizeAuditExpr body) binderInfo
  | .forallE _ domain body binderInfo =>
      .forallE .anonymous (normalizeAuditExpr domain)
        (normalizeAuditExpr body) binderInfo
  | .letE _ type value body nonDep =>
      .letE .anonymous (normalizeAuditExpr type)
        (normalizeAuditExpr value) (normalizeAuditExpr body) nonDep
  | .proj typeName index structureExpr =>
      .proj typeName index (normalizeAuditExpr structureExpr)
  | expression => expression

private def emitAuditExpression
    (auditId aspect : String) (declaration : Name)
    (expression : Expr) : CommandElabM Unit := do
  let normalized := normalizeAuditExpr expression
  let payload := Json.mkObj
    [ ("audit_id", toJson auditId)
    , ("aspect", toJson aspect)
    , ("declaration", toJson declaration.toString)
    , ("expression", toJson (toString (repr normalized)))
    ]
  logInfo m!"AUDIT_FINGERPRINT {payload.compress}"

private def resolveAuditDeclaration
    (declarationSyntax : Syntax) : CommandElabM ConstantInfo := do
  let name ← liftCoreM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo declarationSyntax
  getConstInfo name

syntax (name := emitAuditType)
  "emit_audit_type " str ident : command

elab_rules : command
  | `(emit_audit_type $auditId:str $declaration:ident) => do
      let info ← resolveAuditDeclaration declaration
      emitAuditExpression auditId.getString "type" info.name info.type

syntax (name := emitAuditDefinition)
  "emit_audit_definition " str ident : command

elab_rules : command
  | `(emit_audit_definition $auditId:str $declaration:ident) => do
      let info ← resolveAuditDeclaration declaration
      emitAuditExpression auditId.getString "type" info.name info.type
      match info.value? true with
      | some value =>
          emitAuditExpression auditId.getString "value" info.name value
      | none =>
          throwError
            "definition audit anchor {info.name} has no exportable value"

/-!
## P01 main Theorems 2.1--2.2, Level 1

The 25 September 2026 review covers the finite-query and fixed-sample
statements, their defining interfaces, and their explicit-equivalence
transports.  Definition bodies are fingerprinted recursively to preserve the
meaning of the concrete outputs.  Supporting proof-certificate declarations
contribute only their types; this dependency tracking does not extend the
human audit to construction or proof correspondence.  The separate semantic
Level 3 record remains unchanged.
-/

emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Generic.Language
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Generic.Presents
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Generic.Stream
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Generic.sample
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.Accepted
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.ProducesFromSample
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.acceptedDecidable
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.acceptedSet
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.acceptedSetMembershipDecidable
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.consistentIndices
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.enumerateAccepted
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.enumerateAccepted.match_1
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.FiniteFamily.ProducesFromSample
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.FiniteFamily.encodeSample
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.FiniteFamily.outputOfEquiv
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.GeneratesInLimit
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.IndexedOracleFamily.language
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.IndexedOracleFamily.query
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.encodeFamily
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.generatorOfEquiv
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Language
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.LanguageFamily
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.ConsistentAt
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.ConsistentOnFinset
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.FinitelyCriticalAt
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.GeneratesInLimit
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.HasConsistent
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.MachineState.counter
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.MachineState.output
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.Stop
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.consistentAtDecidable
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.consistentCandidates
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.consistentOnFinsetDecidable
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.criticalCandidates
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.criticalFailures
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.finitePrefix
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.finitelyCriticalAtDecidable
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.hasConsistentDecidable
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.inconsistentSamples
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.kmGenerator
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.language
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.processRound
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.query
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.roundCounter
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.run
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.run.match_1
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.selected
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.stopDecidable
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Presents
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Support.renameLanguage
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.Support.renameStream
emit_audit_definition "P01-main-theorems-2-1-2-2-level1" GenLimit.sample
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.enumerateAccepted._proof_1
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.enumerateAccepted._proof_2
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.FiniteFamily.enumerateAccepted_proof_irrel
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Results.theorem_2_1
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Results.theorem_2_1_of_equiv
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Results.theorem_2_2
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Results.theorem_2_2_of_equiv
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.IndexedOracleFamily
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.IndexedOracleFamily.mk
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.encodeFamily._proof_1
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.KM.Transport.encodeFamily._proof_2
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.MachineState
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.MachineState.mk
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.criticalCandidates_nonempty
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.mk
emit_audit_type "P01-main-theorems-2-1-2-2-level1" GenLimit.OracleFamily.stop_exists

/-!
## P01 semantic Level 3 prototype

The completed human audit covers the round-dependent semantic construction,
its public main theorem, and the displayed intermediate mathematical steps.
The anchors below protect the statement and construction dimensions.  The
proof-body correspondence dimension remains a manual maintenance judgment.
-/

emit_audit_definition "P01-semantic-level3" GenLimit.Language
emit_audit_definition "P01-semantic-level3" GenLimit.LanguageFamily
emit_audit_definition "P01-semantic-level3" GenLimit.Presents
emit_audit_definition "P01-semantic-level3" GenLimit.sample
emit_audit_definition "P01-semantic-level3" GenLimit.Consistent
emit_audit_type "P01-semantic-level3" GenLimit.OracleFamily.mk
emit_audit_definition "P01-semantic-level3" GenLimit.Critical
emit_audit_definition "P01-semantic-level3" GenLimit.KM.Semantic.criticalIndices
emit_audit_definition "P01-semantic-level3" GenLimit.KM.Semantic.focus
emit_audit_definition "P01-semantic-level3" GenLimit.KM.Semantic.fresh
emit_audit_definition "P01-semantic-level3" GenLimit.KM.Semantic.generator
emit_audit_definition "P01-semantic-level3" GenLimit.KM.Semantic.GeneratesInLimit

emit_audit_type "P01-semantic-level3" GenLimit.critical_subset_of_le
emit_audit_type "P01-semantic-level3" GenLimit.target_eventually_critical
emit_audit_type "P01-semantic-level3" GenLimit.KM.Semantic.focus_spec
emit_audit_type "P01-semantic-level3" GenLimit.KM.Semantic.fresh_spec
emit_audit_type "P01-semantic-level3" GenLimit.KM.Semantic.generator_spec
emit_audit_type "P01-semantic-level3" GenLimit.KM.Semantic.kleinbergMullainathan_main

/-!
## P01 round-dependent semantic construction, Level 2

The 18 October 2026 review covers the theorem specification and Section 4
construction, including the shared greatest-candidate and least-fresh
selectors.  It explicitly excludes theorem proof bodies and proof-step
correspondence; the historical Level 3 baseline above remains needs-review.
The shared selector bodies are separate anchors because the paper-facing
definitions now delegate to them.
-/

emit_audit_definition "P01-semantic-level2" GenLimit.Language
emit_audit_definition "P01-semantic-level2" GenLimit.LanguageFamily
emit_audit_definition "P01-semantic-level2" GenLimit.Presents
emit_audit_definition "P01-semantic-level2" GenLimit.sample
emit_audit_definition "P01-semantic-level2" GenLimit.Consistent
emit_audit_type "P01-semantic-level2" GenLimit.OracleFamily.mk
emit_audit_definition "P01-semantic-level2" GenLimit.Critical
emit_audit_definition "P01-semantic-level2" GenLimit.KM.Semantic.criticalIndices
emit_audit_definition "P01-semantic-level2" GenLimit.KM.Semantic.focus
emit_audit_definition "P01-semantic-level2" GenLimit.KM.Semantic.fresh
emit_audit_definition "P01-semantic-level2" GenLimit.KM.Semantic.generator
emit_audit_definition "P01-semantic-level2" GenLimit.KM.Semantic.GeneratesInLimit
emit_audit_definition "P01-semantic-level2" GenLimit.Support.greatestCandidateWithFallback
emit_audit_definition "P01-semantic-level2" GenLimit.Support.leastFreshFromInfinite
emit_audit_type "P01-semantic-level2" GenLimit.KM.Semantic.kleinbergMullainathan_main

/-!
## P0A semantic characterization, Level 1

The completed human audit covers the statement of the semantic analogue of
Angluin's Theorem 1.  These anchors protect that theorem type and the semantic
definitions on which its meaning depends.  They deliberately exclude the
effective theorem, its corollaries, the characterization proof body, and the
internal learner construction.
-/

emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Generic.Language
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Generic.Stream
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Generic.Presents
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Learner
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.textPrefix
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.StabilizesTo
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.IdentifiesInLimit
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Angluin.SemanticIdentifier
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Angluin.SemanticallyIdentifies
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Angluin.SemanticallyInferrable
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Angluin.IsTellTale
emit_audit_definition "P0A-semantic-characterization-level1" GenLimit.Angluin.ConditionTwo

emit_audit_type "P0A-semantic-characterization-level1" GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo

/-!
## P02 named ordinary-generation results

The completed audit covers Proposition 2.1 and Theorems 2.4, 2.5, 3.3, 3.5,
and 3.10.  The 18 October 2026 narrow review renews statement and definition
applicability after the finite-history interface migration.  It adds explicit
anchors for the shared operator, the optional closure interface, and the six
public theorem specifications.  It does not review construction or proof
correspondence, or extend to the supporting Section 3 lemmas and corollaries,
prompted generation, prediction, or Appendix C.
-/

emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.Language
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.LanguageClass
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.Stream
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.Generator
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.Presents
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.StreamIn
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.sequenceSample
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.sample
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.output
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.CorrectAt
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.UUS
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.IsLimitGenerator
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.GeneratableInLimit
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.IsUniformGeneratorAt
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.UniformlyGeneratable
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.IsNonuniformGenerator
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.NonuniformlyGeneratable
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.versionSpace
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.commonCore
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.closure
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.IsClosureWitness
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.ClosureDimensionAtMost
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.HasClosureDimension
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.HasFiniteClosureDimension
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.HasInfiniteClosureDimension
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.IsNondecreasingCover
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.IsFiniteCover
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.UUS
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.GeneratableInLimit
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.UniformlyGeneratable
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.NonuniformlyGeneratable
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.closure
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.IsNondecreasingCover
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.IsFiniteCover
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.IsClosureWitness
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.ClosureDimensionAtMost
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.HasClosureDimension
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.HasFiniteClosureDimension
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.HasInfiniteClosureDimension
emit_audit_definition "P02-named-section2-3-results" GenLimit.LiRamanTewari.GenerationHierarchyStrictOn

emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.proposition_2_1
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.theorem_2_4
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.theorem_2_5
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_in_limit
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.exists_countable_nonuniform_not_uniform_class
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.exists_generatable_in_limit_not_nonuniformly_generatable
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.Results.proposition_2_1
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.Results.theorem_2_4
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.Results.theorem_2_5
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.Results.theorem_3_3
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.Results.theorem_3_5
emit_audit_type "P02-named-section2-3-results" GenLimit.LiRamanTewari.Results.theorem_3_10

/-!
## P02 Theorem 3.3 specification, Level 1 (25 September 2026)

This separate scope records Shuangping Li's statement-level review after the
finite-history interface migration. It does not renew the older multi-result
P02 scope or certify theorem proof bodies or the generator construction.
-/

emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.Language
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.Stream
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.Generator
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.StreamIn
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.sample
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.output
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.UUS
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.IsUniformGeneratorAt
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.UniformlyGeneratable
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.versionSpace
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.commonCore
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.IsClosureWitness
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.ClosureDimensionAtMost
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.HasClosureDimension
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.Generic.HasFiniteClosureDimension
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.LiRamanTewari.UUS
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.LiRamanTewari.UniformlyGeneratable
emit_audit_definition "P02-theorem-3-3-level1" GenLimit.LiRamanTewari.HasFiniteClosureDimension

emit_audit_type "P02-theorem-3-3-level1" GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension

/-!
## P02 Theorem 3.5 specification, Level 1 (25 September 2026)

This scope guards the theorem statement and its semantic definitions only.
It does not renew the broader P02 audit or certify proof correspondence.
-/

emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.Language
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.Stream
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.Generator
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.StreamIn
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.sample
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.output
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.UUS
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.IsNonuniformGenerator
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.NonuniformlyGeneratable
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.IsNondecreasingCover
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.versionSpace
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.commonCore
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.IsClosureWitness
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.ClosureDimensionAtMost
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.HasClosureDimension
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.Generic.HasFiniteClosureDimension
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.LiRamanTewari.UUS
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.LiRamanTewari.NonuniformlyGeneratable
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.LiRamanTewari.IsNondecreasingCover
emit_audit_definition "P02-theorem-3-5-level1" GenLimit.LiRamanTewari.HasFiniteClosureDimension

emit_audit_type "P02-theorem-3-5-level1" GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover

/-!
## P02 Theorem 3.10 specification, Level 1 (25 September 2026)

This scope guards the theorem statement and its semantic definitions only.
It does not renew the broader P02 audit or certify proof correspondence.
-/

emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.Language
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.Stream
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.Generator
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.Presents
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.sample
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.output
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.UUS
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.IsLimitGenerator
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.GeneratableInLimit
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.IsFiniteCover
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.versionSpace
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.commonCore
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.IsClosureWitness
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.ClosureDimensionAtMost
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.HasClosureDimension
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.Generic.HasFiniteClosureDimension
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.LiRamanTewari.UUS
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.LiRamanTewari.GeneratableInLimit
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.LiRamanTewari.IsFiniteCover
emit_audit_definition "P02-theorem-3-10-level1" GenLimit.LiRamanTewari.HasFiniteClosureDimension

emit_audit_type "P02-theorem-3-10-level1" GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_in_limit

/-! ## P04 overview Theorems 1--4 and detailed Theorem 7

The 19 October review renewed Theorems 1, 3, and 4. The 21 October
Level 1 review of detailed Theorem 7 renews the adaptive-query specification
and overview Theorem 2, completing the combined statement/definition scope.
-/

emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.Language
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.LanguageClass
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.LanguageFamily
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.Stream
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.Generator
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.Presents
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.StreamIn
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.sequenceSample
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.sample
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.output
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.CorrectAt
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.UUS
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.IsNonuniformGenerator
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.NonuniformlyGeneratable

emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.TwoLanguageQuery
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.AnsweredTwoLanguageQuery
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.TwoLanguageAction
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.TwoLanguageRound
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.TwoLanguageMembershipAlgorithm
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.AnsweredQuery
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.Action
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.Round
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.Algorithm
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.QueryTraceValid
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.RoundValid
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.ExecutionValid
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.inputPrefix
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Support.AdaptiveMembershipDialogue.ExecutionOutputsAt
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.queriedLanguage
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.AnsweredQueryCorrect
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.QueryTraceValid
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.RoundValid
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.ExecutionValid
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.membershipInputPrefix
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.MembershipExecutionOutputsAt
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.selectedTwoLanguage
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.selectedThreshold
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.NonuniformTwoLanguageMembershipGuarantee
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.UniversalTwoLanguageMembershipGenerator
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.TheoremSevenStatement

emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.ExhaustiveAlgorithm
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.generatorAt
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.exhaustiveOutput
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.generatedBefore
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.generateOnly
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.ExhaustiveCorrectAt
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.IsExhaustiveGenerator
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.IsAngluinTellTale
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.WeakAngluinExistence
emit_audit_definition "P04-overview-theorems-1-4" _root_.Language
emit_audit_definition "P04-overview-theorems-1-4" _root_.Language.IsRegular

emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_1
emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_2
emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_3
emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_4
emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_7

/-! ## P04 overview Theorems 1, 3, and 4, Level 1

The 19 October 2026 review renews these three statements and their defining
interfaces after the finite-history extraction. These dated anchors remain
separate from the combined scope renewed on 21 October. This narrower scope
does not cover the adaptive membership-query model or proof correspondence.
-/

emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.Language
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.Stream
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.Generator
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.Presents
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.sequenceSample
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.sample
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.output
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.Generic.UUS
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.IsNonuniformGenerator
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.NonuniformlyGeneratable
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.ExhaustiveAlgorithm
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.generatorAt
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.exhaustiveOutput
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.generatedBefore
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.generateOnly
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.ExhaustiveCorrectAt
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.IsExhaustiveGenerator
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable
emit_audit_definition "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.WeakAngluinExistence
emit_audit_definition "P04-overview-theorems-1-3-4-level1" _root_.Language
emit_audit_definition "P04-overview-theorems-1-3-4-level1" _root_.Language.IsRegular

emit_audit_type "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.Results.theorem_1
emit_audit_type "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.Results.theorem_3
emit_audit_type "P04-overview-theorems-1-3-4-level1" GenLimit.CharikarPabbaraju.Results.theorem_4

/-! ## P04 overview Theorem 5, Level 1

The 21 October 2026 review covers the feedback characterization statement
and its defining game semantics. Strategy structures, their fields, the
interaction, distinct samples, consistent languages, and finite GF dimension
are guarded separately from the earlier Theorems 1--4 scope. Proof bodies and
the construction of a winning strategy remain outside this Level 1 review.
-/

emit_audit_definition "P04-theorem-5-level1" GenLimit.Generic.Language
emit_audit_definition "P04-theorem-5-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P04-theorem-5-level1" GenLimit.Generic.Stream
emit_audit_definition "P04-theorem-5-level1" GenLimit.Generic.Presents
emit_audit_definition "P04-theorem-5-level1" GenLimit.Generic.sequenceSample
emit_audit_definition "P04-theorem-5-level1" GenLimit.Generic.sample
emit_audit_definition "P04-theorem-5-level1" GenLimit.Generic.UUS

emit_audit_type "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackRound
emit_audit_type "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackRound.mk
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackRound.input
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackRound.query
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackRound.answer
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackRound.output
emit_audit_type "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackGeneratorStrategy
emit_audit_type "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackGeneratorStrategy.mk
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackGeneratorStrategy.query
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackGeneratorStrategy.output
emit_audit_type "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackAdversaryStrategy
emit_audit_type "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackAdversaryStrategy.mk
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackAdversaryStrategy.input
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackAdversaryStrategy.answer

emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackNextRound
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackHistory
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackRound
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackInput
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackQuery
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackAnswer
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackOutput
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackSampleThrough
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.FeedbackAdversaryConsistent
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackConsistentLanguagesThrough
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.feedbackEffectiveIntersection
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.IsUniformFeedbackGeneratorAt
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.UniformlyGeneratableWithFeedback
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.GFDimensionAtLeast
emit_audit_definition "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.HasFiniteGFDimension

emit_audit_type "P04-theorem-5-level1" GenLimit.CharikarPabbaraju.Results.theorem_5

/-! ## P06 Section 3 theorem specifications

The 26 September 2026 Level 1 renewal unfolds the shared occurrence-noise,
eventual-correctness, finite-history, and intersection interfaces.  These
anchors preserve the four reviewed statements and their defining meanings;
proof bodies, constructions, and quantitative results remain outside scope.
-/

emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.Language
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.Stream
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.Generator
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.Presents
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.StreamIn
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.sequenceSample
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.sample
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.output
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.UUS
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.IsNonuniformGenerator
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.NonuniformlyGeneratable
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.IsFiniteCover
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.ViolationIndices
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.FinitelyManyViolations
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.ViolationsAtMost
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.OccurrenceContaminatedPresentation
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.IsPresentationwiseEventuallyCorrect
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Support.classIntersection
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.commonIntersection
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.HasFiniteNoise
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.IsUniformNoiseIndependentGeneratorAt
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.UniformNoiseIndependentGeneratable
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.positivePart
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.negativePart
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.noisyVersionSpace
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.noisyCommonCore
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.NoisyClosureWitnessAt
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.FiniteNoisyClosureDimensionAt
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.HasNoiseAtMost
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.IsUniformNoiseDependentGenerator
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.UniformNoiseDependentGeneratable
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.NoisyPresentation
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.IsNoisyLimitGenerator
emit_audit_definition "P06-section3-theorems-level1" GenLimit.NoisyExamples.NoisilyGeneratableInLimit

emit_audit_type "P06-section3-theorems-level1" GenLimit.NoisyExamples.theorem_3_1
emit_audit_type "P06-section3-theorems-level1" GenLimit.NoisyExamples.theorem_3_3
emit_audit_type "P06-section3-theorems-level1" GenLimit.NoisyExamples.theorem_3_9
emit_audit_type "P06-section3-theorems-level1" GenLimit.NoisyExamples.theorem_3_10

/-! ## P10 overview Theorems 3.1--3.3

The 25 September 2026 Level 1 renewal includes the shared finite-history
interface, the standing UUS convention through the three companion theorem
types, and the semantic definitions of their named witness classes.  The
definition anchors close all project-local references in the reviewed
statements; theorem proof bodies remain outside this scope.
-/

emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.Language
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.LanguageClass
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.Stream
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.Generator
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.Presents
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.StreamIn
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.sequenceSample
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.sample
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.output
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.CorrectAt
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.UUS
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.IsUniformGeneratorAt
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.UniformlyGeneratable
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.IsNonuniformGenerator
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.NonuniformlyGeneratable
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.versionSpace
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.commonCore
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Support.InjectivePresentation
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.InjectivePresentation
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.IsLimitGeneratorOnInjectivePresentations
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.NoAdversaryInputSchedule
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.IsUniformNoAdversaryInputScheduleAt
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.IsNonuniformNoAdversaryInputSchedule
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.LiRamanTewari.commonCore
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.LiRamanTewari.EventuallyUnboundedClosure
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.negativeIntegers
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.positiveIntegers
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.negativeCode
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.signedDeletionLanguage
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.infiniteNegativeFinitePositiveClass
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem43FirstLanguage
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem43FirstClass
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.negativePrefix
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem43SecondLanguage
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem43SecondClass

emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_1
emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_2
emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_3
emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_1_witness_uus
emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_2_witness_uus
emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_3_witness_uus

/-!
## P0 arbitrary-text semantic theory, Level 2

This scope follows the completed audit from the ordered-text Core through the
finite-language learner, locking, finite tell-tales, and the Section 8
superfinite obstruction.  Theorem proof bodies remain outside the automatic
fingerprint even though the human record covers the displayed proof chain.
-/

emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Language
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.LanguageFamily
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Presents
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.sample
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Consistent
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.textPrefix
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Learner
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.learnerOfFiniteHistory
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.StabilizesTo
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.IdentifiesInLimit

emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.Naming
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.Naming.mk
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.TextLearner
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IdentifiesOnText
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IdentifiesLanguage
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IdentifiesClass
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IdentifiableWith
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.familyNaming
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IdentifiesFamily
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.semanticNaming
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.SemanticallyIdentifiesClass
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.SemanticallyIdentifiable
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.semanticLearner
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.PositiveCompatible
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finiteLanguages
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finiteNaming
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finiteLearner
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.HistoryIn
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IsStabilizing
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IsLocking
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Generic.IsFiniteTellTale
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IsTellTale
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.ContainsAllFiniteLanguages
emit_audit_definition "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.IsSuperfinite

emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.textPrefix_length
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.textPrefix_zero
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.textPrefix_succ
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.textPrefix_prefix
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.textPrefix_eq_ofFn
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.mem_textPrefix_iff
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.textPrefix_toFinset
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.learnerOfFiniteHistory_ofFn
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.learnerOfFiniteHistory_textPrefix
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.identifiesClass_semanticLearner
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.identifiableWith_implies_semanticallyIdentifiable
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.positiveCompatible_iff_toFinset_subset
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.positiveCompatible_textPrefix_iff_consistent
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.mem_finiteLanguages
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finite_subset_eventually_subset_sample
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.eventually_sample_eq_of_finite
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finiteLearner_identifiesOnText
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finiteLearner_identifiesFiniteLanguages
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finiteLanguages_identifiableWith
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finiteLanguages_semanticallyIdentifiable
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.HistoryIn.mono
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.historyIn_textPrefix
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.exists_presentation_of_nonempty
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.exists_stabilizing_of_identifiesLanguage
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.exists_locking_of_identifiesLanguage
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finite_tellTale_of_semantic_identification
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finite_tellTale_of_semanticallyIdentifiable
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.all_finite_and_infinite_not_semanticallyIdentifiable
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.superfinite_not_identifiableWith
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.superfinite_not_text_identifiable
emit_audit_type "P0-arbitrary-text-semantic-level2" GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable

/-! ## P39 recursive criticality and focus definitions -/

emit_audit_definition "P39-criticality-and-focus-definitions" GenLimit.Language
emit_audit_definition "P39-criticality-and-focus-definitions" GenLimit.LanguageFamily
emit_audit_definition "P39-criticality-and-focus-definitions" GenLimit.Presents
emit_audit_definition "P39-criticality-and-focus-definitions" GenLimit.sample
emit_audit_definition "P39-criticality-and-focus-definitions" GenLimit.Consistent
emit_audit_definition "P39-criticality-and-focus-definitions" GenLimit.RecursiveCritical
emit_audit_definition "P39-criticality-and-focus-definitions" GenLimit.IsFocus

/-! ## P39 patient-scope state-machine construction -/

emit_audit_definition "P39-patient-machine-construction" GenLimit.Language
emit_audit_definition "P39-patient-machine-construction" GenLimit.LanguageFamily
emit_audit_definition "P39-patient-machine-construction" GenLimit.Presents
emit_audit_definition "P39-patient-machine-construction" GenLimit.sample
emit_audit_definition "P39-patient-machine-construction" GenLimit.Consistent
emit_audit_type "P39-patient-machine-construction" GenLimit.OracleFamily
emit_audit_type "P39-patient-machine-construction" GenLimit.OracleFamily.mk
emit_audit_definition "P39-patient-machine-construction" GenLimit.RecursiveCritical
emit_audit_definition "P39-patient-machine-construction" GenLimit.IsFocus
emit_audit_type "P39-patient-machine-construction" GenLimit.PatientMachine.MoveKind
emit_audit_type "P39-patient-machine-construction" GenLimit.PatientMachine.MoveKind.rec
emit_audit_type "P39-patient-machine-construction" GenLimit.PatientMachine.State
emit_audit_type "P39-patient-machine-construction" GenLimit.PatientMachine.State.mk
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.initialState
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.consistentIndices
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.criticalIndices
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.survivingCriticalIndices
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.highestCritical
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.highestSurvivor
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.lowestConsistentInScope
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.lowestConsistent
emit_audit_type "P39-patient-machine-construction" GenLimit.PatientMachine.Decision
emit_audit_type "P39-patient-machine-construction" GenLimit.PatientMachine.Decision.mk
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.backtrackDecision
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.stableDecision
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.decide
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.Available
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.leastAvailable
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.processRound
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.run
emit_audit_definition "P39-patient-machine-construction" GenLimit.PatientMachine.output
emit_audit_type "P39-patient-machine-construction" GenLimit.PatientMachine.output_available

/-! ## P39 exact-presentation main result -/

emit_audit_definition "P39-exact-presentation-main" GenLimit.Language
emit_audit_definition "P39-exact-presentation-main" GenLimit.LanguageFamily
emit_audit_definition "P39-exact-presentation-main" GenLimit.Presents
emit_audit_type "P39-exact-presentation-main" GenLimit.OracleFamily.mk
emit_audit_definition "P39-exact-presentation-main" GenLimit.GeneratorFirst
emit_audit_definition "P39-exact-presentation-main" GenLimit.PatientScope.prefixFinset
emit_audit_definition "P39-exact-presentation-main" GenLimit.PatientScope.prefixCount
emit_audit_definition "P39-exact-presentation-main" GenLimit.PatientScope.relativeLowerDensity
emit_audit_definition "P39-exact-presentation-main" GenLimit.PatientMachine.output
emit_audit_definition "P39-exact-presentation-main" GenLimit.PatientMachine.patientLowerDensity
emit_audit_type "P39-exact-presentation-main" GenLimit.PatientMachine.patientScope_lowerDensity_half
emit_audit_type "P39-exact-presentation-main" GenLimit.PatientMachine.patientScope_generation_and_lowerDensity

/-! ## P39 partial-enumeration Lemma 3.16 and Theorem 3.17 -/

/- These aliases exist only in this audit exporter so the immutable historical
anchor names can still be compared with the current v2 theorem types. They
are not part of the P39 library or its public results facade. -/
alias GenLimit.PartialEnumeration.lemma_3_16_generation :=
  GenLimit.PartialEnumeration.lemma_B_2_generation
alias GenLimit.PartialEnumeration.theorem_3_17_lowerDensity :=
  GenLimit.PartialEnumeration.theorem_B_3_lowerDensity
alias GenLimit.PartialEnumeration.theorem_3_17 :=
  GenLimit.PartialEnumeration.theorem_B_3
alias GenLimit.PartialEnumeration.section_3_3_generation_and_lowerDensity :=
  GenLimit.PartialEnumeration.theorem_B_3_with_generation

emit_audit_definition "P39-partial-enumeration-level2" GenLimit.Language
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.LanguageFamily
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.Presents
emit_audit_type "P39-partial-enumeration-level2" GenLimit.OracleFamily.mk
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.GeneratorFirst
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PatientScope.prefixFinset
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PatientScope.prefixCount
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PatientScope.relativeLowerDensity
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PatientMachine.output
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.codeSupport
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.codedIntersection
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.GoodCode
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.closureCode
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.closureIndex
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.closure
emit_audit_definition "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.partialPatientLowerDensity
emit_audit_type "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.lemma_3_16_generation
emit_audit_type "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.theorem_3_17_lowerDensity
emit_audit_type "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.theorem_3_17
emit_audit_type "P39-partial-enumeration-level2" GenLimit.PartialEnumeration.section_3_3_generation_and_lowerDensity

/-!
## P21 arXiv v2 Overview, Level 1

Peng Zhang reported completion on 1 November 2026 for all 20 Overview
theorem statements at checkpoint 7bdc137. These anchors guard statement
types and their project-local defining interfaces. Supporting certificate
types preserve definition applicability; proof bodies and separate
construction correspondence are outside the recorded Level 1 scope.
-/

emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.GeneratableInLimit
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.Generator
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.IsLimitGenerator
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.IsNondecreasingCover
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.IsNonuniformGenerator
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.IsUniformGeneratorAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.Language
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.NonuniformlyGeneratable
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.Presents
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.Stream
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.StreamIn
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.UniformlyGeneratable
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.commonCore
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.output
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.sample
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.sequenceSample
emit_audit_definition "P21-v2-overview-level1" GenLimit.Generic.versionSpace
emit_audit_definition "P21-v2-overview-level1" GenLimit.LiRamanTewari.GeneratableInLimit
emit_audit_definition "P21-v2-overview-level1" GenLimit.LiRamanTewari.NonuniformlyGeneratable
emit_audit_definition "P21-v2-overview-level1" GenLimit.LiRamanTewari.UniformlyGeneratable
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.CoveringNumberAtLeast
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.CoveringNumberEq
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.Distance
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.DistanceDominatedBy
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.GeneratableInLimitAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HasFiniteInternalCover
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HasFiniteScaleClosureDimension
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.IsExample48CausalCandidate
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.axisPoint
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48A
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48CausalGenerator
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48Disturbing
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48G
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48Language
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48LanguageClass
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48Optimal
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48U
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48U._proof_1
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48USet
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.example48Zero
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.InClosedNeighborhood
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.IsDoublingDistance
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.IsDoublingDistance._proof_1
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.IsLimitGeneratorAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.IsNondecreasingMetricCover
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.IsNonuniformGeneratorAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.IsScaleClosureWitness
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.IsUniformGeneratorAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.MetricCorrectAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.MetricPresentation
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.MutuallyLipschitzDominated
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.NonuniformlyGeneratableAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.RealLineThreshold.languageClass
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.RealLineThreshold.positiveEvenIntegers
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.RealLineThreshold.primePairSupport
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.RealLineThreshold.realDistance
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.corollary_3_2
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.corollary_3_4
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.corollary_4_3
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.example_4_11
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.example_4_5
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.example_4_8
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.example_4_9
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.example_B_3
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.lemma_C_1
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.lemma_C_2
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.proposition_D_1
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_3_1
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_3_3
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_3_5
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_4_1
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_4_10
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_4_2
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_4_4
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_4_6
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.Results.theorem_4_7
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.RowDiagonal.Criterion
emit_audit_type "P21-v2-overview-level1" GenLimit.MetricSpaces.RowDiagonal.Criterion.mk
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.RowDiagonal.future
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.RowDiagonal.observations
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.RowDiagonal.prior
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.RowDiagonal.stopped
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.UniformlyGeneratableAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.UniformlyUnboundedSupportAt
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.closedNeighborhood
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.commonCore
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.discreteDistance
emit_audit_definition "P21-v2-overview-level1" GenLimit.MetricSpaces.versionSpace

/-!
## P03 Theorems 3.1--3.3, Level 1

Peng Zhang reported completion on 2 November 2026 at checkpoint 82c0869.
These anchors guard the three Overview statement types and their defining
interfaces. Supporting certificate types preserve definition applicability;
construction and proof correspondence and the separate Additional result
are outside this Level 1 scope.
-/

emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Angluin.ConditionTwo
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Angluin.IsEnumeratedTellTale
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Angluin.IsTellTale
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Angluin.SemanticIdentifier
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Angluin.SemanticallyIdentifies
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Angluin.SemanticallyInferrable
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Angluin.enumeratedSet
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.DiscreteIID.positiveGeometric
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.DiscreteIID.positiveGeometric._proof_1
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.DiscreteIID.positiveGeometric._proof_2
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.DiscreteIID.positiveGeometric._proof_3
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.DiscreteIID.probability
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.DiscreteIID.samples
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.DiscreteIID.samples.match_1
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Generic.Language
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Generic.Presents
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Generic.Stream
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.AchievesBreadthRate
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.AchievesIdentificationRate
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.AdmissibleSublinearExponent
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.AdmissibleSublinearExponent.mk
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.CertifiedBreadthPositiveBranch
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.DecidableMOP
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.ExponentialBreadth
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.ExponentialGenerates
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.GenerationNontrivial
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.GenerationTable
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.HasComputableSampler
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.IdentifiableInLimit
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.NoBreadthRate
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.NoIdentificationRate
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.NontrivialCollection
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.OracleMOP
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.Results.theorem_3_1
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.Results.theorem_3_2
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.Results.theorem_3_3
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.StatisticalGenerator
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.StatisticalIdentifier
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.UniformDecidableMOP
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.ValidDistribution
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.answerAt
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.breadthError
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.certifiedKM
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.decodedTell
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.deterministicIdentifier
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.emissionCode
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.exactFreshSampler
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.familyMembership
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationAccept
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationAnswer
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationConsistent
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationCritical
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationError
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationHasConsistent
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationOracle
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationPost
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationPost_computable
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationProgram
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationProgram_terminates
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationQueries
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationQueries_primrec
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.generationSubset
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.identificationError
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.identificationOracle
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.identificationPost
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.identificationPost_computable
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.identificationProgram
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.identificationQueries
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.identificationQueries_primrec
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.identifiedBreadth
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.instDecidableGenerationAccept
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.instDecidableGenerationHasConsistent
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.memberCode
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerIndex
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerPost
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerPost_computable
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerProgram
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerProgram_terminates
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerQueries
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerQueries_primrec
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerSample
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.samplerSeed
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.seededFreshSample
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.tableEligible
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.HallucinationModeCollapse.tellTaleBreadthGenerator
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.IdentifiesInLimit
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Language
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.LanguageFamily
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Learner
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.MembershipOracle
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.MembershipOracle.mk
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.MembershipOracle.query
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.OracleFamily
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.OracleFamily.language
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.OracleFamily.mk
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.OracleFamily.query
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.OracleFamily.query_spec
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.StabilizesTo
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram.Terminates
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram.mk
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram.output
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram.partialRun
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram.queries
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram.run
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram.run_dom
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.OracleSearchProgram.stage
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.Support.TruthTableProgram
emit_audit_type "P03-theorems-3-1-3-3-level1" GenLimit.Support.TruthTableProgram.mk
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.TruthTableProgram.output
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.TruthTableProgram.queries
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.TruthTableProgram.run
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.enumeratedSet
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.firstTrue
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.firstTrue.match_1
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.Support.tableLookup
emit_audit_definition "P03-theorems-3-1-3-3-level1" GenLimit.textPrefix

/-!
## P39 arXiv v2 Theorems 3.15 and B.3, Level 1

Peng Zhang reported completion on 7 November 2026 at checkpoint 3f0aa55.
These anchors guard the two Overview density statements and their recursive
project-local defining dependencies, including the Core increasing-order
density specialization. Supporting certificate types preserve definition
meaning only. Construction/proof correspondence, the separate optimality
upper bound, and other P39 statements are outside this Level 1 scope.
The four historical P39 manifests retain their original needs-review baselines.
-/

emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.Consistent
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.DenseGeneration.Results.theorem_3_15
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.DenseGeneration.Results.theorem_B_3
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.GeneratorFirst
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage.enumeration
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage.increasing
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage.increasing._proof_1
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage.increasing._proof_2
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage.lowerDensity
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage.mk
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage.prefixCount
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.Language
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.LanguageFamily
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.OracleFamily
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.OracleFamily.infinite'
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.OracleFamily.language
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.OracleFamily.mk
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.OracleFamily.query
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PartialEnumeration.GoodCode
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PartialEnumeration.closure
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PartialEnumeration.closure._proof_1
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PartialEnumeration.closure._proof_2
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PartialEnumeration.closureCode
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PartialEnumeration.codeSupport
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PartialEnumeration.codedIntersection
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PartialEnumeration.partialPatientLowerDensity
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.Available
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.Decision
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.Decision.focus
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.Decision.mk
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.Decision.move
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.Decision.scope
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.Decision.tau
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.MoveKind
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.MoveKind.backtrack
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.MoveKind.expand
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.MoveKind.initial
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.MoveKind.stay
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.State
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.State.age
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.State.focus
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.State.lastOutput
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.State.mk
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.State.scope
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.State.tau
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.State.used
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.available_exists
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.backtrackDecision
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.consistentIndices
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.criticalIndices
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.decide
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.highestCritical
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.highestSurvivor
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.initialState
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.leastAvailable
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.lowestConsistent
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.lowestConsistentInScope
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.output
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.patientLowerDensity
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.processRound
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.run
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.run.match_1
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.stableDecision
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientMachine.survivingCriticalIndices
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.PatientScope.relativeLowerDensity
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.Presents
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.RecursiveCritical
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.RecursiveCritical._proof_1
emit_audit_type "P39-v2-theorems-3-15-B-3-level1" GenLimit.RecursiveCritical._proof_2
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.RecursiveCritical.match_1
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.Support.greatestCandidateWithFallback
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.Support.leastCandidateWithFallback
emit_audit_definition "P39-v2-theorems-3-15-B-3-level1" GenLimit.sample

/-!
## P22 arXiv v2 Theorems 4.1, 5.1, 6.1, 6.6, and 7.3, Level 1

Shuangping Li completed this review on 12 November 2026 at checkpoint 6062058.
These anchors guard the six Overview statements for Theorems 4.1, 5.1, 6.1
(semantic and finite-query forms), 6.6, and 7.3, and their recursive
project-local defining dependencies. Supporting certificate types preserve
definition meaning only. Theorem 7.1 (`theorem_7_1_of_algorithm3` and the
over-strong-obligation diagnostic), construction/proof correspondence, and
other P22 statements are outside this Level 1 scope.
-/

emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.GeneratableInLimit
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.Generator
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.IsLimitGenerator
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.IsNonuniformGenerator
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.IsUniformGeneratorAt
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.Language
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.NonuniformlyGeneratable
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.Presents
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.Stream
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.StreamIn
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.UUS
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.output
emit_audit_definition "P22-v2-overview-level1" GenLimit.Generic.sample
emit_audit_definition "P22-v2-overview-level1" GenLimit.Language
emit_audit_definition "P22-v2-overview-level1" GenLimit.LanguageFamily
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.AnsweredReplayMembershipQuery
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily.CarriedWitnessProtectionState
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.CarriedWitnessProtectionState.cutoff
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily.CarriedWitnessProtectionState.mk
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.CarriedWitnessProtectionState.output
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.CarriedWitnessProtectionState.pastOutputs
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.CarriedWitnessProtectionState.sure
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.CarriedWitnessProtectionUsesFiniteQueries
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.HasReplayActive
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.ReplayConsistentAt
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.ReplayFinitelyCriticalAt
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.ReplayMembershipQuery
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.ReplayMembershipTrace
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.ReplayMembershipTraceValid
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily.WitnessProtectionState
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily.WitnessProtectionState.mk
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.WitnessProtectionState.pastOutputs
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.WitnessProtectionState.sure
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.carriedWitnessProtectionGenerator
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.carriedWitnessProtectionInitial
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.carriedWitnessProtectionProcessRound
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.carriedWitnessProtectionRun
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.carriedWitnessProtectionRun.match_1
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.finitePrefix
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.hasReplayActiveDecidable
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.language
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily.mk
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.query
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayActive
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayActivePairs
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayAdmissible
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily.replayAdmissible_eventually_nonempty_from
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayCarriedRoundCutoff
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayCarriedRoundOutput
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily.replayCarriedRoundOutput._proof_1
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayCarriedStart
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayConsistentAtDecidable
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayCriticalCandidates
emit_audit_type "P22-v2-overview-level1" GenLimit.OracleFamily.replayCriticalCandidates_nonempty
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayDifferencePrefix
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayFinitelyCriticalAtDecidable
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replaySelected
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayWitnessValue
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.replayWitnesses
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.witnessProtectionFallback
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.witnessProtectionPrefixStream
emit_audit_definition "P22-v2-overview-level1" GenLimit.OracleFamily.witnessProtectionSureUpdate
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.CountableDomainOracleFamily
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.CountableDomainOracleFamily.language
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.CountableDomainOracleFamily.mk
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.GeneratableInLimitWithReplay
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.HardHypothesis
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.HardHypothesis.minusOne
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.HardHypothesis.minusTwo
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.HardHypothesis.plusOne
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.HardHypothesis.plusTwo
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.HardPoint
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.IsLimitReplayGenerator
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.IsNonuniformReplayGenerator
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.IsProperLimitReplayGenerator
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.IsProperReplayEnumeration
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.IsProperReplaySequence
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.IsReplayEnumeration
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.IsReplaySequence
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.IsUniformReplayGeneratorAt
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.LimitReplayPoint
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.NonuniformlyGeneratableWithReplay
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.ProperCorrectAt
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.ProperGenerator
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.ProperlyGeneratableInLimitWithReplay
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.Results.theorem_4_1
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.Results.theorem_5_1
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.Results.theorem_6_1
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.Results.theorem_6_1_finite_query
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.Results.theorem_6_6
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.Results.theorem_7_3
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.cutoffLanguage
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.instDecidableEqHardHypothesis
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.instDecidableEqHardHypothesis._proof_1
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.instDecidableEqHardHypothesis._proof_2
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.instFintypeHardHypothesis
emit_audit_type "P22-v2-overview-level1" GenLimit.Replay.instFintypeHardHypothesis._proof_1
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.nonuniformHardClass
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.properOutput
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.upperLanguage
emit_audit_definition "P22-v2-overview-level1" GenLimit.Replay.upperLanguage.match_1

/-!
## P23 arXiv v2 Claims 3.3, 3.5, 3.6, 4.4, 4.11 (repaired), 4.18, 4.20, and 7.1, Level 1

Shuangping Li completed this review on 13 November 2026 at checkpoint 6062058.
These anchors guard the eight `Results/Overview.lean` aliases for Claims 3.3,
3.5, 3.6, 4.4, 4.11 (repaired convergent-proper-tower form), 4.18, 4.20, and
7.1, and their recursive project-local defining dependencies. Construction and
proof correspondence, Theorems 4.1, 4.5, 5.1, 5.5, 5.8, and 5.9, and other P23
statements are outside this Level 1 scope.
-/

emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.AdmissibleWindowBound
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.FiniteRankAtMost
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.HasFiniteCBRank
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Nice
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.PerfectTower
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Results.claim_3_3
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Results.claim_3_5
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Results.claim_3_6
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Results.claim_4_11_repaired
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Results.claim_4_18
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Results.claim_4_20
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Results.claim_4_4
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.Results.claim_7_1
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.UniversallyUnbounded
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.banachMinimum
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.lowerBanachDensity
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.lowerWindowDensity
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.prefixLCA
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.prefixLCA.match_1
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.prefixLCAChangeIndices
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.windowCount
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.windowMinimum
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.Banach.windowRatio
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower.mk
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.FixesAt
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.IsLimitPoint
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.KWOpen
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.PerfectTower
emit_audit_type "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.PerfectTower.mk
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.Point
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.RelativeLimitPoint
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.basicNeighborhood
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.cbDerivative
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.cbDerivative.match_1
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.cbLevel
emit_audit_definition "P23-v2-overview-level1" GenLimit.KleinbergWei.TowerTopology.derivative
emit_audit_definition "P23-v2-overview-level1" GenLimit.Language
emit_audit_definition "P23-v2-overview-level1" GenLimit.Presents

/-!
## P27 ICML 2026 Theorems 3.1--3.4 and 3.9--3.10, Corollaries 3.6--3.8, Level 1

Shuangping Li completed this review on 13 November 2026 at checkpoint a19851f.
These anchors guard twelve `Results/Overview.lean` statements: Theorems
3.1--3.4, Corollaries 3.6--3.8, the set-to-element direction of Theorem 3.9,
the Appendix Lemma A.8 counterexample, and the Theorem 3.10 components A.9,
A.12, and A.13, with their recursive project-local defining dependencies.
The private existence lemma behind `sourceFirst` cannot be named here; the
`sourceFirst` value anchor still records its use. `theorem_3_9_of_selfLocking`
(whose premise fails even for a one-language class), Appendix Theorems A.10
and A.11, construction/proof correspondence, and other P27 statements are
outside this Level 1 scope.
-/

emit_audit_definition "P27-overview-level1" GenLimit.Angluin.ListWithin
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.CountableInnerCover
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.CountableInnerCover.mk
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EventuallyCorrectMistakeFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EventuallyCorrectMistakeGeneratable
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EventuallyCorrectMistakeGenerates
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EventuallyCorrectMistakeSucceedsOn
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EventuallyCorrectQueryFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EventuallyCorrectQueryGeneratable
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EventuallyCorrectQueryGenerates
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EventuallyCorrectQuerySucceedsOn
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.EverywhereFresh
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.FiniteInnerCover
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.FiniteInnerCover.mk
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.HasCountableInnerCover
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.HasFiniteInnerCover
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.IsSelfLockingHistory
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.NoFeedbackCorrectOnList
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.NoFeedbackLockingGap.IsSpike
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.NoFeedbackLockingGap.basePresentation
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.NoFeedbackLockingGap.generator
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.NoFeedbackLockingGap.spikeHistory
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.NoFeedbackLockingGap.target
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.NoFeedbackLockingGap.target_infinite
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.corollary_3_6
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.corollary_3_7
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.corollary_3_8
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_1
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_10_countableInnerCover_example
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_10_finiteInnerCover_sufficient
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_10_noFiniteInnerCover_example
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_2
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_3
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_4
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_9_appendix_A_8_gap
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.Results.theorem_3_9_set_to_element
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementMistakeCorrect
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementMistakeGeneratable
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementMistakeGenerates
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementMistakeStrategy
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementMistakeSucceedsOn
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementQueryGeneratable
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementQueryGenerates
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementQueryStrategy
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementQueryStrategy.mk
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementQueryStrategy.output
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementQueryStrategy.query
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceElementQuerySucceedsOn
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceQueryPolicy
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetMistakeCorrect
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetMistakeGeneratable
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetMistakeGenerates
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetMistakeStrategy
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetMistakeStrategy.mk
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetMistakeStrategy.output
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetMistakeSucceedsOn
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetQueryGeneratable
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetQueryGenerates
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetQueryStrategy
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetQueryStrategy.mk
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetQueryStrategy.output
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetQueryStrategy.query
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.SourceSetQuerySucceedsOn
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleElementMistakeGeneratable
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleElementMistakeGenerates
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleElementMistakeStrategy
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleElementMistakeSucceedsOn
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleSetQueryGeneratable
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleSetQueryGenerates
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy.mk
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy.output
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy.query
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.ZeroExampleSetQuerySucceedsOn
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.eventuallyCorrectMistakeOutput
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.eventuallyCorrectQueryOutput
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.membershipAnswer
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.noFeedbackOutputOnList
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceCanonicalRank
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceElementFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceElementFeedbackRun
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceElementFeedbackStep
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceElementOutput
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceElementQueryFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceElementQueryOutput
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceElementReply
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.sourceElementReply._proof_1
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceFirst
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.sourceFirst._proof_1
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceQueryFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceQueryFeedback.match_1
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetFeedbackRun
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetFeedbackStep
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetFirst
emit_audit_type "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetFirst._proof_1
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetOutput
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetQueryFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetQueryOutput
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.sourceSetReply
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.streamPrefix
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.zeroExampleMistakeFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.zeroExampleMistakeFeedback.match_1
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.zeroExampleMistakeOutput
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.zeroExampleQueryFeedback
emit_audit_definition "P27-overview-level1" GenLimit.FeedbackQueries.zeroExampleQueryOutput
emit_audit_definition "P27-overview-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P27-overview-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P27-overview-level1" GenLimit.Generic.GeneratableInLimit
emit_audit_definition "P27-overview-level1" GenLimit.Generic.GeneratesSetInLimitOn
emit_audit_definition "P27-overview-level1" GenLimit.Generic.Generator
emit_audit_definition "P27-overview-level1" GenLimit.Generic.IsInfiniteSetGenerator
emit_audit_definition "P27-overview-level1" GenLimit.Generic.IsLimitGenerator
emit_audit_definition "P27-overview-level1" GenLimit.Generic.IsSetLimitGenerator
emit_audit_definition "P27-overview-level1" GenLimit.Generic.Language
emit_audit_definition "P27-overview-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P27-overview-level1" GenLimit.Generic.Presents
emit_audit_definition "P27-overview-level1" GenLimit.Generic.SetCorrectAt
emit_audit_definition "P27-overview-level1" GenLimit.Generic.SetGeneratableInLimit
emit_audit_definition "P27-overview-level1" GenLimit.Generic.SetGenerator
emit_audit_definition "P27-overview-level1" GenLimit.Generic.Stream
emit_audit_definition "P27-overview-level1" GenLimit.Generic.UUS
emit_audit_definition "P27-overview-level1" GenLimit.Generic.output
emit_audit_definition "P27-overview-level1" GenLimit.Generic.sample
emit_audit_definition "P27-overview-level1" GenLimit.Generic.sequenceSample
emit_audit_definition "P27-overview-level1" GenLimit.Generic.setOutput
emit_audit_definition "P27-overview-level1" GenLimit.Support.freshFromInfinite
emit_audit_type "P27-overview-level1" GenLimit.Support.freshFromInfinite._proof_1
emit_audit_definition "P27-overview-level1" GenLimit.textPrefix

/-!
## P28 arXiv v1 Overview, Level 1

Shuangping Li completed this review on 13 November 2026 at checkpoint c828be2.
These anchors guard all 19 `Results/Overview.lean` aliases (15 distinct
statements) and their recursive project-local defining dependencies.
Construction/proof correspondence, the full Theorem 5.13 inclusion diamond,
and P28 results outside the Overview are outside this Level 1 scope.
-/

emit_audit_definition "P28-overview-level1" GenLimit.Angluin.SemanticIdentifier
emit_audit_definition "P28-overview-level1" GenLimit.Angluin.SemanticallyIdentifies
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.AllProperNontrivial
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.CommonCrossing
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ContrastiveClosureDimensionAtMost
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ContrastiveClosureDimensionEquals
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ContrastiveGenerator
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ContrastiveIdentifier
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ContrastivelyGeneratable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ContrastivelyIdentifiable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ContrastivelyIdentifies
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ContrastivelyIdentifiesFrom
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.Crosses
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Edge
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.Edge.left
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Edge.mk
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.Edge.right
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.Edge.unordered
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Edge.unordered._proof_1
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.FiniteContrastiveClosureDimension
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.FinitelyCorruptionContrastivelyIdentifiable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.GeneratesFrom
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.Incident
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.Incomparable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IncomparablePairsOverlap
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.InfiniteSafeCores
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IsContrastivePresentation
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IsContrastivelyHollow
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IsEventualCore
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IsFiniteFamilyIntersection
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IsKCorruptedContrastivePresentation
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IsKCorruptedTextPresentation
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IsLeastPositiveUniformThreshold
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.IsSharedPresentation
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.KContrastivelyIdentifiable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.KContrastivelyIdentifiesFrom
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.KTextIdentifiable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.KTextIdentifiesFrom
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.NonuniformlyContrastivelyGeneratable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.NonuniformlyContrastivelyGenerates
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.NotEliminableFrom
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.OverlappingCover
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.ProperNontrivialSupport
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.proposition_4_2
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.proposition_5_11
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.proposition_5_12
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.proposition_5_8
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.proposition_6_3_defect_infimum
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.proposition_6_3_zero_defect
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_4_3
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_4_7
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_5_13_disjoint_witness
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_5_13_punctured_witness
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_5_14_disjoint_witness
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_5_14_punctured_witness
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_5_4
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_5_4_quantitative
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_5_4_sharp_sample_complexity
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_5_5
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_6_5
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_6_6
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.Results.theorem_6_8
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.TextIdentifiable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratable
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratableAt
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratesAt
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.UnorderedCrosses
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.UnorderedEdge
emit_audit_type "P28-overview-level1" GenLimit.ContrastiveGeneration.UnorderedEdge.mk
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.UnorderedEdge.vertices
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.bothNegative
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.bothPositive
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.cleanWrongCutViolationCounts
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.coSingletonFamily
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.coSingletonSupport
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.commonVertices
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.contrastiveIdentifierOutput
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.defectNumber
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.disjointFamily
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.disjointFamily.match_1
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.distinctUnorderedEdges
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.edgeClosure
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.edgeVersionSpace
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.evenSupport
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.forcedWrongCutViolationInfimum
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.gOnly
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.generatorOutput
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.hOnly
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.instInfSetENat_genLimit
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.oddSupport
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.positiveDefectSet
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.puncturedCore
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.puncturedFamily
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.puncturedFamily.match_1
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.robustBlock
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.robustBlockFamily
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.robustBlockPoint
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.robustBlockSupport
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.robustCommonCore
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.seenPrefix
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.streamPrefix
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.unorderedClosure
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.unorderedVersionSpace
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.unorderedVertices
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.wrongCutViolationCount
emit_audit_definition "P28-overview-level1" GenLimit.ContrastiveGeneration.wrongCutViolationTimes
emit_audit_definition "P28-overview-level1" GenLimit.Generic.CorrectAt
emit_audit_definition "P28-overview-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P28-overview-level1" GenLimit.Generic.GeneratableInLimit
emit_audit_definition "P28-overview-level1" GenLimit.Generic.Generator
emit_audit_definition "P28-overview-level1" GenLimit.Generic.IsLimitGenerator
emit_audit_definition "P28-overview-level1" GenLimit.Generic.IsNondecreasingCover
emit_audit_definition "P28-overview-level1" GenLimit.Generic.Language
emit_audit_definition "P28-overview-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P28-overview-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P28-overview-level1" GenLimit.Generic.OccurrenceContaminatedPresentationAtMost
emit_audit_definition "P28-overview-level1" GenLimit.Generic.Presents
emit_audit_definition "P28-overview-level1" GenLimit.Generic.Stream
emit_audit_definition "P28-overview-level1" GenLimit.Generic.ViolationIndices
emit_audit_definition "P28-overview-level1" GenLimit.Generic.output
emit_audit_definition "P28-overview-level1" GenLimit.Generic.sample
emit_audit_definition "P28-overview-level1" GenLimit.IdentifiesInLimit
emit_audit_definition "P28-overview-level1" GenLimit.Learner
emit_audit_definition "P28-overview-level1" GenLimit.StabilizesTo
emit_audit_definition "P28-overview-level1" GenLimit.textPrefix

/-!
## P29 arXiv v1 Theorems 4.1, 5.1, and 6.1 and Lemmas 6.2--6.3, Level 1

Shuangping Li completed this review on 13 November 2026 at checkpoint c828be2.
These anchors guard seven `Results/Overview.lean` statements and their
recursive project-local defining dependencies. `theorem_6_4_proof_diagnostic`
(an arithmetic identity, not a source statement), Theorem 6.4 itself,
construction/proof correspondence, and other P29 statements are outside
this Level 1 scope.
-/

emit_audit_definition "P29-overview-level1" GenLimit.Generic.Stream
emit_audit_definition "P29-overview-level1" GenLimit.Generic.sample
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.DyadicUpperBudget
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.DyadicUpperBudget._proof_1
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.FirstActivated
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.LastMistakeBefore
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.MistakeTrace
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.NonuniformComplexityAtMost
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.Results.lemma_6_2
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.Results.lemma_6_3
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.Results.theorem_4_1
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.Results.theorem_5_1
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.Results.theorem_5_1_order_diagnostic
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.Results.theorem_6_1
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.Results.theorem_6_1_displayed_bound
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.TotalMistakesAtMost
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.countableSemanticGenerated
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.countableSemanticWeight
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.countableTargetTrace
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.disjointPairLanguage
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.disjointPairLanguage._proof_1
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.exists_fresh_of_infinite
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.exists_fresh_weightedScore_maximizer
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.finiteClassIntersection
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.finiteSemanticGenerated
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.finiteSemanticWeight
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.finiteSemanticWeight.match_1
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.finiteTargetTrace
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.freshWeightedMaximizer
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.infiniteFreshWeightedMaximizer
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.initialPrefixWeight
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.mistakeCount
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.modifiedGreedyCandidates
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.modifiedGreedyCandidates.match_1
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.modifiedGreedyConsistent
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.modifiedGreedyFiniteIntersection
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.modifiedGreedyGenerated
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.modifiedGreedyGenerated._proof_1
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.paperDoublingActiveCount
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.polynomialPrior
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.polynomialPriorLogBudget
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.polynomialPriorLogBudget._proof_1
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.polynomialPriorLogBudget._proof_2
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.updateWeight
emit_audit_type "P29-overview-level1" GenLimit.MistakeBounded.updateWeight._proof_1
emit_audit_definition "P29-overview-level1" GenLimit.MistakeBounded.weightedScore

/-!
## P30 arXiv v2 Theorem 4 and Appendix Theorem 12, Level 1

Shuangping Li completed this review on 13 November 2026 at checkpoint c828be2.
These anchors guard the four totalized-GCG `Results/Overview.lean` statements
for Theorem 4 / Appendix Theorem 12 and their recursive project-local defining
dependencies. Lean's `id` deadline is one step stricter than the source's
identity deadline. The density-endgame and turn-taking wrappers (whose
premises are equivalent to their conclusions), `appendix_D_rate_core`, the
Theorems 1--2 counting core, the Lemma 2 endgame, construction/proof
correspondence, and other P30 statements are outside this Level 1 scope.
-/

emit_audit_definition "P30-theorem-4-level1" GenLimit.Consistent
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.BadStrictCritical
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.FirstOccurrence
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.StrictCritical
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.boundaryCandidates
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.firstBadStrictCritical
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.guessIndex
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.guessIndex.match_1
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.scopedFocus
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.scopedStrictCriticalIndices
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.selectIndex
emit_audit_type "P30-theorem-4-level1" GenLimit.KleinbergWei.DensityMeasures.selectIndex._proof_1
emit_audit_type "P30-theorem-4-level1" GenLimit.KleinbergWei.OrderedLanguage
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.OrderedLanguage.carrier
emit_audit_definition "P30-theorem-4-level1" GenLimit.KleinbergWei.OrderedLanguage.enumeration
emit_audit_type "P30-theorem-4-level1" GenLimit.KleinbergWei.OrderedLanguage.mk
emit_audit_definition "P30-theorem-4-level1" GenLimit.Language
emit_audit_definition "P30-theorem-4-level1" GenLimit.LanguageFamily
emit_audit_definition "P30-theorem-4-level1" GenLimit.Presents
emit_audit_definition "P30-theorem-4-level1" GenLimit.Support.greatestCandidateWithFallback
emit_audit_type "P30-theorem-4-level1" GenLimit.TimeSensitive.CanonicallyOrderedFamily
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.CanonicallyOrderedFamily.guess
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.CanonicallyOrderedFamily.language
emit_audit_type "P30-theorem-4-level1" GenLimit.TimeSensitive.CanonicallyOrderedFamily.mk
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.CanonicallyOrderedFamily.order
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.OnTimeUnusedRank
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.Results.theorem_12_totalized_gcg
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.Results.theorem_12_totalized_gcg_lower
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.Results.theorem_4_totalized_gcg
emit_audit_type "P30-theorem-4-level1" GenLimit.TimeSensitive.Results.theorem_4_totalized_gcg_lower
emit_audit_type "P30-theorem-4-level1" GenLimit.TimeSensitive.TotalizedGCGState
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.TotalizedGCGState.initial
emit_audit_type "P30-theorem-4-level1" GenLimit.TimeSensitive.TotalizedGCGState.mk
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.TotalizedGCGState.outputs
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.TotalizedGCGState.stage
emit_audit_type "P30-theorem-4-level1" GenLimit.TimeSensitive.exists_onTimeUnusedRank
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.gcgThreshold
emit_audit_type "P30-theorem-4-level1" GenLimit.TimeSensitive.gcgThreshold._proof_1
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.greedyRoundOutput
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.greedyUsed
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.onTimeUnused
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.onTimeUnusedRank
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.outputHistoryStream
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.sequencePrefix
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.timelyDensity
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.timelyElements
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.totalizedGCGOutput
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.totalizedGCGRun
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.totalizedGCGRun.match_1
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.totalizedGCGStep
emit_audit_type "P30-theorem-4-level1" GenLimit.TimeSensitive.totalizedGCG_theorem_4
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.totalizedRoundActive
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.totalizedRoundOutput
emit_audit_definition "P30-theorem-4-level1" GenLimit.TimeSensitive.upperTimelyDensity
emit_audit_definition "P30-theorem-4-level1" GenLimit.sample

/-!
## P31 arXiv v1 Overview, Level 1

Shuangping Li completed this review on 13 November 2026 at checkpoint c828be2.
These anchors guard all 13 `Results/Overview.lean` aliases and their recursive
project-local defining dependencies. Theorems 4.1 and 4.10 are order-robust:
the adversary picks the target's density order after the generator. The
source's fixed-order upper bounds, construction/proof correspondence, and P31
results outside the Overview are outside this Level 1 scope.
-/

emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.AlmostContained
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.AlmostEquivalent
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.ApproximatelyIdentifiesRun
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.ArbitraryPresentationMemorylessGeneratable
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.BufferSetGenerator
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.BufferSetGenerator.mk
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.BufferSetGenerator.output
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.BufferSetGenerator.update
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.BufferState
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.BufferUpperDensityGuarantee
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.DistinctWindow
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.ElementCorrectAt
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.EventuallyAlmostContainedHypotheses
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.ExactlyIdentifiesRun
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.FinitelyRepeating
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.FinitelyRepeatingMemorylessGeneratable
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.FullInformationIndexLearner
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IncrementalElementGeneratesRun
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IncrementalIndexGeneratesRun
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IncrementalLearner
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IncrementallyApproximatelyIdentifiable
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IncrementallyElementGenerable
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IncrementallyExactlyIdentifiableOnFinitelyRepeating
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IncrementallyIndexGenerableOnFinitelyRepeating
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.InfiniteSingletonCores
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IsArbitraryPresentationMemorylessGenerator
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IsFinitelyRepeatingElementGeneratorOn
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IsFinitelyRepeatingIndexGenerator
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IsFinitelyRepeatingMemorylessGenerator
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IsRepetitionFreeBufferGeneratorOn
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.IsRepetitionFreeWindowGeneratorOn
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.MemorylessElementGenerator
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.MemorylessIndexGenerator
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.MemorylessSetGenerator
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.MemorylessUpperDensityGuarantee
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.proposition_5_1
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.proposition_A_2
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_1_1
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_3_1
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_3_2
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_4_10_order_robust
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_4_15_order_robust
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_4_1_order_robust
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_4_2_order_robust
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_5_2
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_A_1
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_A_4_semantic
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.Results.theorem_A_5_nat_semantic
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.ValidSetOutput
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.ValidWindowOutput
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.WindowSetGenerator
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.WindowSetGenerator.mk
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.WindowSetGenerator.output
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.WindowUpperDensityGuarantee
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.adaptiveBufferLowerValue
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.appendixTriangleLanguages
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.appendixTriangleLanguages.match_1
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.bufferAdmissibleUpperDensities
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.bufferMinimaxUpperDensity
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.bufferOutputAt
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.bufferRunUpperDensity
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.bufferState
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.bufferState.match_1
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.elementHistoryPrefix
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.emptyBufferState
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.emptyBufferState._proof_1
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.exactObstructionCore
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.exactObstructionLanguages
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.exactObstructionLanguages.match_1
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.incrementalRun
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.incrementalRun.match_1
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.indexLanguageOne
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.indexLanguageZero
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.indexLanguages
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.indexLanguages.match_1
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.memorylessAdmissibleUpperDensities
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.memorylessMinimaxUpperDensity
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.memorylessRunUpperDensity
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.singletonCore
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.windowAdmissibleUpperDensities
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.windowAt
emit_audit_type "P31-overview-level1" GenLimit.BoundedMemory.windowAt._proof_2
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.windowMinimaxUpperDensity
emit_audit_definition "P31-overview-level1" GenLimit.BoundedMemory.windowRunUpperDensity
emit_audit_definition "P31-overview-level1" GenLimit.Generic.Language
emit_audit_definition "P31-overview-level1" GenLimit.Generic.Presents
emit_audit_definition "P31-overview-level1" GenLimit.Generic.Stream
emit_audit_definition "P31-overview-level1" GenLimit.Generic.sample
emit_audit_type "P31-overview-level1" GenLimit.KleinbergWei.OrderedLanguage
emit_audit_definition "P31-overview-level1" GenLimit.KleinbergWei.OrderedLanguage.carrier
emit_audit_definition "P31-overview-level1" GenLimit.KleinbergWei.OrderedLanguage.enumeration
emit_audit_definition "P31-overview-level1" GenLimit.KleinbergWei.OrderedLanguage.lowerDensity
emit_audit_type "P31-overview-level1" GenLimit.KleinbergWei.OrderedLanguage.mk
emit_audit_definition "P31-overview-level1" GenLimit.KleinbergWei.OrderedLanguage.prefixCount
emit_audit_definition "P31-overview-level1" GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
emit_audit_definition "P31-overview-level1" GenLimit.KleinbergWei.OrderedLanguage.upperDensity
emit_audit_definition "P31-overview-level1" GenLimit.Language
