import GenLimit.Core
import GenLimit.Paper01_LanguageGeneration.Semantic
import GenLimit.Paper01_LanguageGeneration.FiniteQuery
import GenLimit.Paper01_LanguageGeneration.FiniteFamily
import GenLimit.Paper01_LanguageGeneration.SetInterface
import GenLimit.Paper01_LanguageGeneration.Transport
import GenLimit.Paper01_LanguageGeneration.Prompted.Universe
import GenLimit.Paper01_LanguageGeneration.Results.Overview
import GenLimit.Paper01_LanguageGeneration.Results.Transport

/-!
# #01 Language Generation

Importing this module provides the short semantic/noncomputable proof, the
NeurIPS Proceedings finite membership-query algorithm for Theorem 2.1,
the fixed-sample finite-family membership-query algorithm for Theorem 2.2,
the robust string-prompt finite-query algorithm for Theorem 7.1,
the literal observed-set interface for arbitrary exact presentations, and the
transport from the implementation over `ℕ` to an arbitrary countable universe,
without importing the #39 Dense Generation patient-scope development.
-/
