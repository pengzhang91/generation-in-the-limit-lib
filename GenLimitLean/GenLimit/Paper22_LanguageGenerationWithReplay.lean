import GenLimit.Paper22_LanguageGenerationWithReplay.Uniform
import GenLimit.Paper22_LanguageGenerationWithReplay.NonuniformSeparation
import GenLimit.Paper22_LanguageGenerationWithReplay.ProperSeparation
import GenLimit.Paper22_LanguageGenerationWithReplay.LimitSeparation
import GenLimit.Paper22_LanguageGenerationWithReplay.ProperMembershipLowerBound
import GenLimit.Paper22_LanguageGenerationWithReplay.WitnessProtectionMachine
import GenLimit.Paper22_LanguageGenerationWithReplay.CarriedCutoff
import GenLimit.Paper22_LanguageGenerationWithReplay.FiniteQueryTrace
import GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview

/-!
# Language generation with replay

Paper-facing umbrella for the formalization of Racca--Valko--Sanyal,
arXiv:2603.11784v2.  It includes the exact fixed-threshold equivalence
(Theorem 4.1), the countable non-uniform separation (Theorem 5.1), the
Witness Protection core of Theorem 6.1 and Lemmas 6.3--6.5, the
arbitrary-countable-domain transport of its semantic theorem, the executable
literal carried-cutoff state machine and its finite answered-query trace,
literal uncountable ordinary-versus-replay limit separation (Theorem 6.6,
including Lemmas 6.7--6.8), and the four-language proper-generation
separation (Theorem 7.3).  Theorem 7.1's
exact adaptive membership-query statement and checked reduction to the
remaining Algorithm 3 construction are also pinned explicitly.  A separate
Mathlib `Computable` specialization and query-complexity bounds for Theorem
6.1 are not claimed.
-/
