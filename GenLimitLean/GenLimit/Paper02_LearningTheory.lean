import GenLimit.Paper02_LearningTheory.Results.Overview

/-!
# #02 Learning Theory

Independent umbrella for *Generation through the Lens of Learning Theory*.
The public main-results facade is
`GenLimit.Paper02_LearningTheory.Results.Overview`; its source-numbered
wrappers delegate to the canonical topic modules.

Numbered entry points:

* Proposition 2.1 and Theorems 2.4--2.5 are packaged in the results facade.
* Theorems 3.3, 3.5, and 3.10 are in `Closure`,
  `NonuniformCharacterization`, and `GenerationInLimitCharacterization`.
* Theorem 4.1's explicitly delimited VC/Littlestone combinatorial core is in
  `Prediction`.
* Theorems 5.1--5.2 are in `PromptedClosure` and `PromptedNonuniform`.
* Theorems C.2 and C.4 are in `FiniteEUCUnion` and
  `EventuallyUnboundedClosure`.

Theorem 2.2 and the corrected countable form of Theorem 2.3 reuse the Gold
and Angluin developments.  They therefore remain in `GenLimit.Bridges` and
are deliberately not imported by this independent paper umbrella.  Import
`GenLimit` for the paper modules together with all cross-paper bridges.
-/
