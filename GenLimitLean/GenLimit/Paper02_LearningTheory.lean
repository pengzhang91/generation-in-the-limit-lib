import GenLimit.Paper02_LearningTheory.FiniteUniverse
import GenLimit.Paper02_LearningTheory.Results.Overview

/-!
# #02 Learning Theory

Independent umbrella for *Generation through the Lens of Learning Theory*.
The public facade for P02's new main results is
`GenLimit.Paper02_LearningTheory.Results.Overview`; its source-numbered
wrappers delegate to the canonical topic modules.

Numbered new-result entry points:

* Proposition 2.1 packages the strict generation hierarchy.
* Theorems 3.3, 3.5, and 3.10 are in `Closure`,
  `NonuniformCharacterization`, and `GenerationInLimitCharacterization`.
* Theorem 4.1 in `PredictionLandscape` realizes all six regions in the
  distribution-free IID and causal online learning models. The dimension
  arguments and witness classes are in `Prediction`.
* Theorems 5.1--5.2 are in `PromptedClosure` and `PromptedNonuniform`.
* Theorems C.2 and C.4 are in `FiniteEUCUnion` and
  `EventuallyUnboundedClosure`.

The earlier Gold/Angluin and KM results restated as Theorems 2.2--2.5 are
collected in `GenLimit.Paper02_LearningTheory.Results.Background`. Import
that module explicitly, or import `GenLimit` for the paper modules together
with the cross-paper bridges. The background facade is outside this
independent umbrella because its identification bridges depend on Gold,
Angluin, and this umbrella. The native canonical Theorems 2.4--2.5 remain
available in `Introductory`; their `Results` wrappers live in `Background`.
-/
