import Examples.TargetStability
import Examples.FiniteContamination
import Examples.FiniteTellTale
import Examples.PaperResult
import Examples.CrossPaperBridge

/-!
# Compiling examples for GenLimit

This umbrella checks small downstream uses of the public library API.  It is
compiled explicitly in CI but deliberately is not imported by `GenLimit`:
examples are clients of the library, not part of its public dependency graph.
-/
