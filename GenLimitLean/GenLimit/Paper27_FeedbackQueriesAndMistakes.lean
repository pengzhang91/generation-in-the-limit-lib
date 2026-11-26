import GenLimit.Paper27_FeedbackQueriesAndMistakes.Definitions
import GenLimit.Paper27_FeedbackQueriesAndMistakes.MistakeFeedback
import GenLimit.Paper27_FeedbackQueriesAndMistakes.QueryFeedback
import GenLimit.Paper27_FeedbackQueriesAndMistakes.QuerySeparation
import GenLimit.Paper27_FeedbackQueriesAndMistakes.Bridges
import GenLimit.Paper27_FeedbackQueriesAndMistakes.PositiveSequence
import GenLimit.Paper27_FeedbackQueriesAndMistakes.ElementMistake
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceSetMistake
import GenLimit.Paper27_FeedbackQueriesAndMistakes.AdaptiveQueryNormalization
import GenLimit.Paper27_FeedbackQueriesAndMistakes.QueryScheduling
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuery
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuerySeparation
import GenLimit.Paper27_FeedbackQueriesAndMistakes.CountableUnion
import GenLimit.Paper27_FeedbackQueriesAndMistakes.ZeroExamples
import GenLimit.Paper27_FeedbackQueriesAndMistakes.EventuallyCorrect
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackEquivalence
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackLockingGap
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackInnerCovers
import GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview

/-!
# Language generation with feedback queries and mistakes

Paper-facing umbrella for the finite-query and mistake-feedback semantic
cores of Hanneke--Karbasi--Mehrotra--Velegkas (ICML 2026).  The set-valued
characterizations include literal finite positive-sequence input wrappers.
The exact semantic/classical element-valued characterization of Theorem 3.1,
the exact first-element set-feedback equivalence of Theorem 3.2, and the exact
source-timed one-membership-query characterization of Theorem 3.4 are checked.
The older whole-set-validity, square-batch, and pre-sample one-query models are
retained as explicitly auxiliary results.  The literal three-point block
separation of Theorem 3.3 is checked in the source-timed element/set query
interfaces.  Corollaries 3.6--3.8 add countable-union closure, zero-example
generation, and robustness to eventually correct feedback.  Theorem 3.9 uses an independent finite-witness characterization for the
unrestricted conversion. All five clauses of Theorem 3.10 follow. Appendix
Lemma A.8 has a counterexample for sequence-sensitive generators.
-/
