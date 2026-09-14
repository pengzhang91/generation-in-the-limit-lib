import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper00_LanguageIdentification
import GenLimit.Paper01_LanguageGeneration.Semantic
import GenLimit.Paper02_LearningTheory.Results.Overview
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Results.Overview
import GenLimit.Paper06_NoisyExamples.Results.Overview
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Overview
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
and 3.10.  It does not extend to the supporting Section 3 lemmas and
corollaries, prompted generation, prediction, or Appendix C.
-/

emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.Language
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.LanguageClass
emit_audit_definition "P02-named-section2-3-results" GenLimit.Generic.Stream
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

/-! ## P04 overview Theorems 1--4 -/

emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.Language
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.LanguageClass
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.LanguageFamily
emit_audit_definition "P04-overview-theorems-1-4" GenLimit.Generic.Stream
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

emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_1
emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_2
emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_3
emit_audit_type "P04-overview-theorems-1-4" GenLimit.CharikarPabbaraju.Results.theorem_4

/-! ## P06 Section 3 theorem specifications -/

emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.Language
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.LanguageClass
emit_audit_definition "P06-section3-theorems-level1" GenLimit.Generic.Stream
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

/-! ## P10 overview Theorems 3.1--3.3 -/

emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.Language
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.LanguageClass
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.Generic.Stream
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
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.InjectivePresentation
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.IsLimitGeneratorOnInjectivePresentations
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.NoAdversaryInputSchedule
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.IsUniformNoAdversaryInputScheduleAt
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.IsNonuniformNoAdversaryInputSchedule
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput
emit_audit_definition "P10-overview-theorems-3-1-3-3" GenLimit.LiRamanTewari.EventuallyUnboundedClosure

emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_1
emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_2
emit_audit_type "P10-overview-theorems-3-1-3-3" GenLimit.UnionClosedness.theorem_3_3

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
