import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper00_LanguageIdentification
import GenLimit.Paper01_LanguageGeneration.Semantic
import GenLimit.Paper01_LanguageGeneration.Results.Overview
import GenLimit.Paper01_LanguageGeneration.Results.Transport
import GenLimit.Paper02_LearningTheory.Results.Overview
import GenLimit.Paper02_LearningTheory.Results.Background
import GenLimit.Paper03_HallucinationAndModeCollapse.Results.Overview
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Results.Overview
import GenLimit.Paper05_HallucinationsBreadthAndStability.Results.Overview
import GenLimit.Paper06_NoisyExamples.Results.Overview
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Results.Overview
import GenLimit.Paper08_HallucinationDetection.Results.Overview
import GenLimit.Paper09_RepresentativeLanguageGeneration.Results.Overview
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Overview
import GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Results.Overview
import GenLimit.Paper14_ListLanguageIdentification.Results.Overview
import GenLimit.Paper15_PartialEnumeration.Results.Overview
import GenLimit.Paper17_InfiniteContamination.Results.Overview
import GenLimit.Paper19_EffectOfNoise.Results.Overview
import GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview
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
## P01 Theorem 7.1, Level 1

Peng Zhang reported completion on 8 November 2026 at checkpoint 6062058.
The public and canonical string theorem types and their recursive defining
dependencies preserve statement applicability. Supporting proof certificates
contribute only their types. This does not audit construction/proof
correspondence, separately strengthened or transported statements, or renew
the historical semantic Level 3 scope.
-/

emit_audit_definition "P01-theorem-7-1-level1" GenLimit.Language
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.LanguageFamily
emit_audit_type "P01-theorem-7-1-level1" GenLimit.OracleFamily
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.sample
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.Generic.Language
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.Generic.Presents
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.Generic.Stream
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.Generic.sample
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.ConsistentAt
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.FinitelyCriticalAt
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.HasConsistent
emit_audit_type "P01-theorem-7-1-level1" GenLimit.OracleFamily.MachineState
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.consistentAtDecidable
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.consistentCandidates
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.criticalCandidates
emit_audit_type "P01-theorem-7-1-level1" GenLimit.OracleFamily.criticalCandidates_nonempty
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.criticalFailures
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.finitePrefix
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.finitelyCriticalAtDecidable
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.hasConsistentDecidable
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.inconsistentSamples
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.language
emit_audit_type "P01-theorem-7-1-level1" GenLimit.OracleFamily.mk
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.query
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.selected
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.Support.renameLanguage
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.Support.renameStream
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.GeneratesInLimit
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.Robust
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.RobustPrompt
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.candidates
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.encodedMatches
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.generator
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.generatorOfEquiv
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.processRound
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.roundCounter
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.run
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Prompted.stop_exists
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Prompted.theorem_7_1
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Results.theorem_7_1
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Transport.IndexedOracleFamily
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Transport.encodeFamily
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.MachineState.counter
emit_audit_type "P01-theorem-7-1-level1" GenLimit.OracleFamily.MachineState.mk
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.OracleFamily.MachineState.output
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Prompted.generatorOfEquiv._proof_1
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Prompted.processRound._proof_1
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Prompted.run._proof_1
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Prompted.run.match_1
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Transport.IndexedOracleFamily.language
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Transport.IndexedOracleFamily.mk
emit_audit_definition "P01-theorem-7-1-level1" GenLimit.KM.Transport.IndexedOracleFamily.query
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Transport.encodeFamily._proof_1
emit_audit_type "P01-theorem-7-1-level1" GenLimit.KM.Transport.encodeFamily._proof_2

/-!
## P05 three semantic statements, Level 1

Peng Zhang reported this review on 12 November 2026 against the non-P38
working tree: semantic Theorem 3.3, Theorem 3.8 sufficiency only, and the
Nat-universe approximate-breadth clause of Theorem 3.15. The following
anchors guard those statement types and their project-local defining
interfaces. Construction and proof correspondence, other clauses, and
source-conflict findings are outside this human audit.
-/

emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.Angluin.ConditionTwo
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.Angluin.IsTellTale
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.ApproximateBreadthCorrectAt
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.ApproximateBreadthGeneratable
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.ExactBreadthCorrectAt
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.ExactBreadthGeneratable
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.IsExactBreadthGenerator
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.IsStableGenerator
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.IsWeakTellTale
emit_audit_type "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.Results.theorem_3_15_approximate_semantic
emit_audit_type "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.Results.theorem_3_3_semantic
emit_audit_type "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.Results.theorem_3_8_sufficiency_semantic
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.SupportAlgorithm
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.WeakAngluinCondition
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.BreadthCharacterizations.supportAt
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.Generic.IsWeakTellTale
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.Generic.Language
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.Generic.Presents
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.Generic.Stream
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.Generic.sample
emit_audit_definition "P05-semantic-theorems-3-3-3-8-3-15-level1" GenLimit.textPrefix

/-!
## P07 Theorem 2.1, Level 1

Peng Zhang reported a Level 1 review on 12 November 2026 against the current
non-P38 tree. The public and canonical theorem_2_1 statements have identical
normalized types. Recursive definition bodies, including the fixed semantic
selector, and supporting proof-certificate types preserve statement meaning;
this maintenance does not extend the review to construction or proof
correspondence. Other P07 theorems and density guarantees remain outside scope.
-/

emit_audit_definition "P07-theorem-2-1-level1" GenLimit.Consistent
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.AccurateAt
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.BadStrictCritical
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.FirstOccurrence
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.IndexValidInLimit
emit_audit_type "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_1
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.StrictCritical
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.boundaryCandidates
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.firstBadStrictCritical
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.guessIndex
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.guessIndex.match_1
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.scopedFocus
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.scopedStrictCriticalIndices
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.selectIndex
emit_audit_type "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.selectIndex._proof_1
emit_audit_type "P07-theorem-2-1-level1" GenLimit.KleinbergWei.DensityMeasures.theorem_2_1
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.Language
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.LanguageFamily
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.Presents
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.Support.greatestCandidateWithFallback
emit_audit_definition "P07-theorem-2-1-level1" GenLimit.sample

/-!
## P08 Theorems 2.1 and 2.3, Level 1

Peng Zhang reported a Level 1 review on 12 November 2026 against the current
non-P38 tree. The public and canonical statements are guarded together with
their recursive defining dependencies, including the finite query-tree
constructors and evaluator. This preserves the positive-data identification
and detection interfaces and the complete, exactly labeled domain-enumeration
model. It does not certify detector constructions or proof correspondence.
-/

emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Angluin.SemanticIdentifier
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Angluin.SemanticallyIdentifies
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Angluin.SemanticallyInferrable
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Generic.Language
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Generic.Presents
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Generic.Stream
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.DetectableWithNegativeExamples
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.Detector
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.DetectorCorrectAt
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.DetectsHallucinations
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.DetectsWithNegativeExamples
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.HallucinationDetectable
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.IdentifiableInLimit
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.IsLabeledEnumeration
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.LabeledStream
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.NegativeDetectorCorrectAt
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.NegativeExampleDetector
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.OracleTree
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.OracleTree.definitionsPropDecidable
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.OracleTree.eval
emit_audit_type "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.Results.theorem_2_1
emit_audit_type "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.Results.theorem_2_3
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.detectorOutput
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.negativeDetectorOutput
emit_audit_type "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.theorem_2_1
emit_audit_type "P08-theorems-2-1-2-3-level1" GenLimit.HallucinationDetection.theorem_2_3
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.IdentifiesInLimit
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Learner
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.StabilizesTo
emit_audit_type "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.Tree
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.Tree.below
emit_audit_type "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.Tree.branch
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.Tree.brecOn
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.Tree.casesOn
emit_audit_type "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.Tree.leaf
emit_audit_type "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.Tree.rec
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.evaluate
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.Support.FiniteMembershipQueryTree.nodeCount.match_1
emit_audit_definition "P08-theorems-2-1-2-3-level1" GenLimit.textPrefix

/-!
## P09 Theorems 3.3 and 3.7, Level 1

Peng Zhang reported a Level 1 statement and relevant-definition review on
12 November 2026. The two Published statements and their recursive local
defining dependencies are guarded. Theorem 3.3 uses bounded group-closure
witness cardinalities; Theorem 3.7 retains its stronger arbitrary-domain,
arbitrary-group-family statement. This does not audit constructions, proof
correspondence, numerical optimality, or the Section 4 corrections.
-/

emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.IsNondecreasingCover
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.Language
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.Stream
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.StreamIn
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.UUS
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.commonCore
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.sample
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.Generic.versionSpace
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.AlphaRepresentativeUniformlyGeneratable
emit_audit_type "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.DiscreteDistribution
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.DiscreteDistribution.mass
emit_audit_type "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.DiscreteDistribution.mk
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.HasFiniteGroupClosureDimension
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.IsAlphaRepresentative
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.IsConsistentAt
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.IsConsistentFrom
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.IsCountablePartition
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.IsGroupClosureWitness
emit_audit_type "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.Published.theorem_3_3
emit_audit_type "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.Published.theorem_3_7
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.RandomizedGenerator
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.RepresentativelyNonuniformlyGeneratable
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.commonCore
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.consistentHypotheses
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.distributionAt
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.empiricalGroupProbability
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.empiricalMassOnGroupIndices
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.groupClosureConditionOne
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.groupClosureConditionTwo
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.groupMass
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.groupSupDistance
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.inducedGroupProbability
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.restrictedMass
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.unavailableGroups
emit_audit_definition "P09-theorems-3-3-3-7-level1" GenLimit.RepresentativeGeneration.unseenClosure

/-!
## P12 all Overview theorems and their definitions, Level 1

Peng Zhang reported review of all eight current Overview statements and all
definitions needed to interpret them on 12 November 2026, in work/non-p38.
The eight types and recursive project-local defining dependencies are guarded.
Supporting proof-certificate types preserve definition meaning only; this is
not a separate audit of constructions, proof bodies, or detailed results.
-/

emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.Generator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.InjectiveValueContaminatedPresentation
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.IsNondecreasingCover
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.IsPresentationwiseEventuallyCorrect
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.IsTargetwiseEventuallyCorrect
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.IsUniformEventuallyCorrect
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.Language
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.Presents
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.SetDifferenceAtMost
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.Stream
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.StreamIn
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.UUS
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.ValuesOutsideAtMost
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.output
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Generic.sample
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.CompatibleResponses
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.CorrectAt
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.EnumerationWithOmissionsAtMost
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.ExactEnumeration
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.FeedbackCorrectAt
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.FeedbackGenerator
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.FeedbackGenerator.mk
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.FeedbackGenerator.output
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.FeedbackGenerator.query
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.FeedbackIdentifier
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.GeneratableInLimitWithOmissions
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.GeneratableInLimitWithQueries
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.GeneratableInLimitWithTotalFeedback
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutRepetitions
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.GeneratesInLimitWithoutSamples
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.HasAtMostQueries
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.HasIncreasingInfiniteCoreCover
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.InfiniteOmissionEnumeration
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsIncreasingInfiniteCoreCover
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsLimitFeedbackGeneratorWithQueries
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsLimitGeneratorWithOmissions
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsLimitGeneratorWithoutRepetitions
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsLimitTotalFeedbackGenerator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsNoisyLimitGenerator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsNonuniformGenerator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsNonuniformInfiniteOmissionGenerator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsNonuniformNoisyGenerator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsUniformGenerator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsUniformInfiniteOmissionGenerator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.IsUniformNoisyGenerator
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.MandatoryQueryMachine
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.MandatoryQueryMachine.mk
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.MandatoryQueryMachine.output
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.MandatoryQueryMachine.query
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.NoisilyGeneratableInLimit
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.NoisyEnumeration
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.NoisyEnumerationWithLevel
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.NonuniformlyGeneratableWithoutRepetitions
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.NonuniformlyIdentifiableWithFeedback
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.NonuniformlyIdentifiesWithFeedback
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.NonuniformlyNoisilyGeneratable
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.Results.theorem_1_1
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.Results.theorem_1_2
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.Results.theorem_1_3
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.Results.theorem_1_4
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.Results.theorem_1_5
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.Results.theorem_1_6
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.Results.theorem_1_7
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.Results.theorem_1_8
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.TotalFeedbackCorrectAt
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.TotalFeedbackGenerator
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutRepetitions
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutSamples
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.UniformlyGeneratesWithoutSamples
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.UniformlyNoisilyGeneratable
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.WithoutSamplesGenerator
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.WithoutSamplesGenerator.mk
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.WithoutSamplesGenerator.output
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualFeedbackOutput
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualFeedbackResponse
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualFeedbackResponse._proof_1
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualFeedbackResponse._proof_2
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualFeedbackResponse.match_1
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualIdentifierOutput
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualMandatoryQueryOutput
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualMandatoryQueryResponse
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualMandatoryQueryResponse._proof_1
emit_audit_type "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualMandatoryQueryResponse._proof_2
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.actualTotalFeedbackOutput
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.feedbackQuery
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.languageIntersection
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.membershipAnswer
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.observedThrough
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.NoiseLossFeedback.outputAt
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Support.InjectivePresentation
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Support.MissingAtMost
emit_audit_definition "P12-overview-theorems-1-1-to-1-8-level1" GenLimit.Support.classIntersection

/-!
## P13 Overview Theorems 1, 4, 5, 6, and 8, Level 1

Peng Zhang reported review of these five statements and all definitions
needed to interpret them on 13 November 2026. Theorem 9's representative
endgame is explicitly excluded. Concrete generator and canonical-complexity
definitions are guarded for their denotational meaning, including the noisy
empty-candidate repair. Supporting proof-certificate types do not constitute
separate construction or proof-correspondence audits.
-/

emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.Generic.Generator
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.Generic.Language
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.Generic.sequenceSample
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.NoisyExamples.negativePart
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.AchievesNoisyTimeVector
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.AchievesTimeVector
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.FiniteIntersectionCandidate
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.FiniteSublevels
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.HistoryGenerator
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.ImprovesSomewhere
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.InsertionSplit
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.InsertionSplit.left
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.InsertionSplit.mk
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.InsertionSplit.right
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.IsUnboundedScheduler
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.MatchesPrefix
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.MaxScoreBound
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoiseContainedAt
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyArgmaxBound
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyInsertionSplit
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyInsertionSplit.left
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyInsertionSplit.mk
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyInsertionSplit.right
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyOrderArgmaxBounds
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyProcedureSampleCandidate
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyProcedureStage
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyProcedureStage.complexity
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyProcedureStage.mk
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyProcedureStage.order
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyProcedureStage.witness
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyProcedureStage.witnessSet
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyRealizableTimeVectors
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.NoisyWitnessCandidate
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.OrderMaxScoreBounds
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.ParetoOptimal
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.PositiveTimeVector
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.PrefixParetoOptimal
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.ProcedureStage
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.ProcedureStage.complexity
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.ProcedureStage.mk
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.ProcedureStage.order
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.ProcedureStage.witness
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.RealizableTimeVectors
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.Results.theorem_1
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.Results.theorem_4
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.Results.theorem_5
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.Results.theorem_6
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.Results.theorem_8
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.TimeVector
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.WorseSomewhere
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalComplexity
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyComplexity
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage._proof_1
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage._proof_2
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage._proof_4
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage._proof_5
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage._proof_6
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage._proof_7
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage._proof_8
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalNoisyProcedureStage.match_1
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalProcedureStage
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalProcedureStage._proof_1
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalProcedureStage._proof_2
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalProcedureStage._proof_4
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalProcedureStage._proof_5
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalProcedureStage._proof_6
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.canonicalProcedureStage.match_1
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.exists_maximal_finiteIntersectionCandidate
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.exists_maximal_noisyWitness_of_exists
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_1
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_11
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_12
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_13
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_2
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_4
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_5
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_6
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_7
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendNoisyProcedureStage._proof_9
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage._proof_1
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage._proof_11
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage._proof_12
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage._proof_3
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage._proof_4
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage._proof_5
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage._proof_6
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.extendProcedureStage._proof_7
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.finiteIntersectionScore
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.greedyListScan
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.greedyListScanBy
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.greedyListScanBy.match_1
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.greedyListStepBy
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.indexedIntersection
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.insertionScope
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.insertionScore
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisyExceptions
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisyGreedyAccept
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisyGreedyScan
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisyInsertionScope
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisyInsertionScore
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisySchedulerGenerator
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisySchedulerGenerator._proof_1
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisySchedulerScanOrder
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.noisySchedulerTimeVector
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.procedureStepComplexity
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.procedureStepWitness
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.schedulerEntryTime
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.schedulerEntryTime._proof_1
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.schedulerGenerator
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.schedulerGenerator._proof_1
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.schedulerScanOrder
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.schedulerTimeVector
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.setComplexity
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.setNoisyWitnessSet
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.setWitness
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.standardGreedyAccept
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.totalNoisyStepComplexity
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.totalNoisyStepSample
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.totalNoisyStepWitness
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.ParetoGeneration.variantCanonicalTime
emit_audit_definition "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.Support.freshFromInfinite
emit_audit_type "P13-overview-theorems-1-4-5-6-8-level1" GenLimit.Support.freshFromInfinite._proof_1

/-!
## P14 Overview Theorems 1 and 2, Level 1

Peng Zhang reported review of both Overview statements and all definitions
needed to interpret them on 13 November 2026. The scope includes exact
positive presentations, behavioral list correctness, recursive k-Angluin
predicates, and relative-Angluin covers. It excludes algorithm-construction
and proof correspondence, detailed theorem statements as separate claims,
and the statistical branch. Shared definitions receive no cross-paper credit.
-/

emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.Generic.Language
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.Generic.LanguageFamily
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.Generic.Presents
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.Generic.Stream
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.CoversAllIndices
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.HasAngluinStratification
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.IdentifiesFrom
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.IsRelativeTellTale
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.KAngluinCondition
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.ListIdentifiable
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.ListIdentifier
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.ListIdentifies
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.Psi
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.Psi.match_1
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.RelativeConditionTwo
emit_audit_type "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.Results.theorem_1
emit_audit_type "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.Results.theorem_2
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.TargetInGuess
emit_audit_definition "P14-overview-theorems-1-and-2-level1" GenLimit.ListIdentification.listOutput

/-!
## P15 all Overview theorems (1.5, 1.7, 1.8, and 1.9), Level 1

Peng Zhang reported review of all four current Overview statements and all
definitions needed to interpret them on 13 November 2026. Canonical endpoint
types are also guarded as equivalent presentations of the same four claims.
Named finite-scope and Algorithm-1 functions are included for statement
meaning, without separate construction/proof correspondence. Supporting
results, conditional density endpoints, and partial-text topology are outside
scope. Full-text TD neighborhoods and the language-valued learner are included.
-/

emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Angluin.ExtensionalIdentifier
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Angluin.ExtensionalIdentifies
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Angluin.ExtensionallyIdentifiable
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Consistent
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.FreshGeneratesInLimit
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Generic.Language
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Generic.Presents
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Generic.Stream
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.IdentifiesInLimit
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.FullTopology.FullOpen
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.FullTopology.IdentifiableOnFullTexts
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.FullTopology.Point
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TDPoint
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TDSpace
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.FullTopology.basicOpen
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.FullTopology.theorem_4_9_fullText
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.GeneratesFromPartialEnumeration
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.IdentifiedIntersectionState
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.IdentifiedIntersectionState.chain
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.IdentifiedIntersectionState.mk
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.IsGreatestRuleTwoCandidate
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_5
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_7
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_8
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_9
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.RuleTwoCandidate
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.SemiIndexGenerates
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.SemiIndexTraceGenerates
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.admissibleScopes
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.algorithmOneChosen
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.algorithmOneChosen.match_1
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.consistencyChainState
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.consistencyIntersectionState
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.consistencyIntersectionState._proof_1
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.freshOutput
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.intersectionOf
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.prefixIntersection
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.ruleTwoResetIndex
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.selectedIndices
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.selectedIntersection
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.selectedIntersection_infinite
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.selectedScope
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.selectedScope._proof_1
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.theorem_1_7
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.theorem_1_8
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.KleinbergWei.PartialEnumeration.theorem_2_1
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Language
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.LanguageFamily
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Learner
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Presents
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.StabilizesTo
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Support.freshFromInfinite
emit_audit_type "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.Support.freshFromInfinite._proof_1
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.sample
emit_audit_definition "P15-overview-theorems-1-5-1-7-1-8-1-9-level1" GenLimit.textPrefix

/-!
## P17 all Overview theorems, Level 1

Peng Zhang reported Level 1 review of all nine current Overview statements
and their recursively needed definitions on 13 November 2026. The working
tree includes the canonical-order Theorem-6.18 transfer. Named algorithm
definitions are guarded for statement meaning; construction/proof review is
excluded. Supporting results and omitted parameter cases are not added.
-/

emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.FinitelyManyViolations
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.Generator
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.IsInfiniteSetGenerator
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.Language
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.Presents
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.SetGenerator
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.Stream
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.StreamIn
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.ViolationIndices
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.historyThenFallback
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.output
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.sample
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Generic.sequenceSample
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.AlgorithmFiveStableThrough
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.AlgorithmNineGoodAt
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.ArbitraryOmissions
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.BoundedDisplacement
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.ConstantNoise
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.ConstantNoiseArbitraryOmissionEnumeration
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.ConstantNoiseDenseSetCondition
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.ConstantNoiseGenerationProperty
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.DensityPrefixAccepts
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.ElementDensityGuaranteeOn
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.FiniteExpansionCode
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.FiniteNoise
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.FiniteOmissions
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.FreshElementCorrectAt
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GeneratesElementInLimitOn
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GeneratesInfiniteSetInLimitOn
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GeneratesSetDensityUnderConstantNoise
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GeneratesSetDensityUnderVanishingNoise
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GeneratesSetInLimitOn
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GeneratesSetUnderFiniteContaminationOn
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GeneratesUnderConstantNoise
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.GuaranteesSetBasedUpperDensityUnderOmissionsOn
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.IsInfiniteSetGenerator
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.NoNoise
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.OmissionsAtMost
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.PriorityBefore
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_5_1
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_5_4
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_6_1
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_6_11
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_6_14
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_6_18
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_6_4
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_6_5
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.Results.theorem_7_8
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.SetCorrectAt
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.SetGenerator
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.VanishingNoise
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.VanishingNoiseArbitraryOmissionEnumeration
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.VanishingNoiseDenseSetCondition
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmFiveActiveIndices
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmFiveCutoff
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmFiveGenerator
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmFiveIndices
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmFivePrefixCompletion
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmFivePrefixIndices
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNineDiagnostic
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNineHistoryIndices
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNineHistoryScore
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNineIndices
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNineNoiseThreshold
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNineNoiseThreshold._proof_1
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNinePriorityTrace
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNineRawCore
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmNineSetGenerator
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.algorithmSevenIndices
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.canonicalFamilyOrders
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.canonicalIndex
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.canonicalIndex._proof_1
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.canonicalRank
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.elementBasedLowerDensity
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.elementBasedUpperDensity
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.elementOutputLanguage
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.elementOutputStream
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.empiricalNoiseRate
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.finiteCommonCore
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.finiteExpansion
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.finiteExpansionCode
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.finiteExpansionLanguage
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.finiteExpansionLanguage_infinite
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.finiteExpansionOracleFamily
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.finiteExpansionOracleFamily._proof_1
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.floorIncrementLanguage
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.floorIncrementOrder
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.floorIncrementStream
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.floorIncrementStream_injective
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.generatedBefore
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.indexedLanguages
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.maximalDensePrefixSize
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.naturalOrder
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.naturalOrder._proof_1
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.noiseCount
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.prefixCompletion
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.prefixMaxCanonicalRank
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.priorityPredecessors
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.priorityRank
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.range_floorIncrementStream
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.rankedPrefix
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.setBasedLowerDensity
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.setBasedUpperDensity
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.setOutput
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theoremSixFourFamily
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theoremSixFourOrders
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_5_1_algorithmFour
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_5_4_characterization_enumerated
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_6_11_characterization_enumerated
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_6_14_characterization_enumerated
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_6_18_finiteContamination_transfer
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_6_1_algorithmFive
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_6_4_arbitrary_constant
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_6_5_lowerDensity_characterization_enumerated
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.theorem_7_8_algorithmNine
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.InfiniteContamination.thresholdPenalty
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.canonical
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.canonical._proof_1
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.canonical._proof_2
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.carrier
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.enumeration
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.lowerDensity
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.mk
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.prefixCount
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.KleinbergWei.OrderedLanguage.upperDensity
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Language
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.LanguageFamily
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.OracleFamily
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.OracleFamily.infinite'
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.OracleFamily.language
emit_audit_type "P17-all-overview-theorems-level1" GenLimit.OracleFamily.mk
emit_audit_definition "P17-all-overview-theorems-level1" GenLimit.Presents

/-!
## P19 all Overview theorems, Level 1

Peng Zhang reported Level 1 review of Theorems 2.16--2.19 and all recursively
statement-relevant definitions on 13 November 2026. Construction/proof
correspondence and other supporting results remain outside scope.
-/

emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.FiniteHistoryOperator
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.Generator
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.IsTargetwiseEventuallyCorrect
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.IsUniformEventuallyCorrect
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.Language
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.SetDifferenceAtMost
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.Stream
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.ValuesOutsideAtMost
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Generic.sample
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.AllLanguagesInfinite
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.CorrectAt
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.EnumerationWithNoiseAtMost
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.FiniteNoisyClosureDimensionAt
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.HasFiniteDimensionExhaustionAt
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.IsNonuniformGeneratorAtNoiseLevel
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.IsNonuniformNoiseDependentGenerator
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.IsUniformGeneratorAtNoiseLevel
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.IsUniformNoiseDependentGenerator
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.MissingAtMost
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.NoisyClosureWitnessAt
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.NonuniformNoiseDependentGeneratable
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.PaperColumnPoint
emit_audit_type "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.Results.theorem_2_16
emit_audit_type "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.Results.theorem_2_17
emit_audit_type "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.Results.theorem_2_18
emit_audit_type "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.Results.theorem_2_19
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.UniformNoiseDependentGeneratable
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.consistentLanguages
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.noisyClosure
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.noisyCommonCore
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.observed
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.QuantifyingNoise.outputAt
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Support.EnumerationWithNoiseAtMost
emit_audit_definition "P19-all-overview-theorems-level1" GenLimit.Support.MissingAtMost
