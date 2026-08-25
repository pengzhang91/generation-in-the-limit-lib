import GenLimit.Core
import GenLimit.Paper39_DenseGeneration.ArxivV1
import GenLimit.Paper39_DenseGeneration.Abstract.NormalizedMain
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper39_DenseGeneration.Partial

/-!
# #39 Dense Generation

Importing this module provides the public arXiv-v1 criticality/focus layer and
its focus-refresh diagnostic.  It also preserves the earlier-manuscript
semantic patient-scope algorithm, its validity and target-relative
lower-density theorems, and its Section 3.3 extension to partial enumeration.
The arXiv-v1 layer reuses #01 Language Generation criticality; it does not
import the #01 selection or machine modules.
-/
