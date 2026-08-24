import GenLimit.Paper12_NoiseLossAndFeedback.Projection
import GenLimit.Paper12_NoiseLossAndFeedback.WithoutSamples
import GenLimit.Paper12_NoiseLossAndFeedback.NoisyWithoutSamples
import GenLimit.Paper12_NoiseLossAndFeedback.NoSampleCharacterization
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteOmissionSeparation
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper12_NoiseLossAndFeedback.UnknownFiniteNoiseSeparation
import GenLimit.Paper12_NoiseLossAndFeedback.InfiniteOmissions
import GenLimit.Paper12_NoiseLossAndFeedback.Repetitions
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteFeedback
import GenLimit.Paper12_NoiseLossAndFeedback.InfiniteFeedback
import GenLimit.Paper12_NoiseLossAndFeedback.FeedbackIdentification
import GenLimit.Paper12_NoiseLossAndFeedback.Relationships
import GenLimit.Paper12_NoiseLossAndFeedback.Bridges.NoisyExamples
import GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview

/-!
# Language Generation in the Limit: Noise, Loss, and Feedback

Paper-facing umbrella for the deterministic formalization slice of
Bai--Panigrahi--Zhang, arXiv:2507.15319v2, including the complete unknown
finite-noise separation, Appendix A.1--A.6 repetition-equivalence path, and
the deterministic infinite-feedback construction of Theorem 6.3 and
Corollary 6.4, and finite-feedback elimination of Theorem 6.7.

`Results.Overview` packages the generation summary theorems from their
detailed proofs and records the exact reuse of the concurrent Paper10
witness. `FeedbackIdentification` formalizes Definitions 6.8--6.9,
Algorithm 6, and summary Theorem 1.8 by reusing the Gold complete-informant
identification theory.
-/
