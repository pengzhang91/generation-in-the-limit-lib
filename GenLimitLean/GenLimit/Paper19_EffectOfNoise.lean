import GenLimit.Paper19_EffectOfNoise.Definitions
import GenLimit.Paper19_EffectOfNoise.Closure
import GenLimit.Paper19_EffectOfNoise.Bridges
import GenLimit.Paper19_EffectOfNoise.FixedLevel
import GenLimit.Paper19_EffectOfNoise.SquareRoot
import GenLimit.Paper19_EffectOfNoise.Nonuniform
import GenLimit.Paper19_EffectOfNoise.Separation
import GenLimit.Paper19_EffectOfNoise.RejectedScan
import GenLimit.Paper19_EffectOfNoise.EquivTransport
import GenLimit.Paper19_EffectOfNoise.Results.Overview

/-!
# Characterizing the Effect of Noise on Language Generation

Paper-specific umbrella for the Lean formalization of
arXiv:2601.21237v2, including the exact fixed-level characterization and
the square-root descent infrastructure.  The Theorem 2.17 witness is also
transported to the paper's literal `ℕ × ℕ` universe, and Algorithm 1 is
available both as an accepted-update compression and as a semantic scan with
every rejected iteration retained.
-/
