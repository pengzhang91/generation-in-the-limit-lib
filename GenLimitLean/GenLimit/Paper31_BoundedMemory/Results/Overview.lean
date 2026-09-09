import GenLimit.Paper31_BoundedMemory.ArbitraryRepetitions
import GenLimit.Paper31_BoundedMemory.FinitelyRepeating
import GenLimit.Paper31_BoundedMemory.OutputSeparations
import GenLimit.Paper31_BoundedMemory.MinimaxClosure
import GenLimit.Paper31_BoundedMemory.WindowHardInstance
import GenLimit.Paper31_BoundedMemory.AdaptiveBuffer
import GenLimit.Paper31_BoundedMemory.IncrementalIdentification
import GenLimit.Paper31_BoundedMemory.ExactIdentificationObstruction
import GenLimit.Paper31_BoundedMemory.IncrementalIndexObstruction
import GenLimit.Paper31_BoundedMemory.IncrementalElementCoding

/-!
# Paper 31: main-results overview

This facade collects the proved headline endpoints for
Kleinberg--Mehrotra--Saberi--Velegkas, *On Language Generation in the Limit
with Bounded Memory*.  All declarations are aliases of canonical proof
modules.

The source-facing limitations are preserved: Theorems 1.1 and 3.1 have the
scope recorded in the paper map; the minimax density theorems expose their
order-robust proved forms; and Appendix Theorems A.4--A.5 are semantic coding
results over `Nat`, not machine-level bounded-memory implementations.  The
full arbitrary-universe transports and the unformalized full Sperner fact are
not claimed here.
-/

namespace GenLimit.BoundedMemory.Results

alias theorem_1_1 := GenLimit.BoundedMemory.theorem_1_1
alias theorem_3_1 := GenLimit.BoundedMemory.theorem_3_1
alias theorem_3_2 := GenLimit.BoundedMemory.theorem_3_2
alias theorem_4_1_order_robust :=
  GenLimit.BoundedMemory.theorem_4_1_memoryless_minimax_upper_density
alias theorem_4_2_order_robust :=
  GenLimit.BoundedMemory.theorem_4_2_no_uniform_positive_lower_density
alias theorem_4_10_order_robust :=
  GenLimit.BoundedMemory.theorem_4_10_window_minimax_upper_density
alias theorem_4_15_order_robust :=
  GenLimit.BoundedMemory.theorem_4_15_adaptive_buffer_lower_bound
alias proposition_5_1 := GenLimit.BoundedMemory.proposition_5_1
alias theorem_5_2 := GenLimit.BoundedMemory.theorem_5_2
alias theorem_A_1 := GenLimit.BoundedMemory.theorem_A_1
alias proposition_A_2 := GenLimit.BoundedMemory.proposition_A_2
alias theorem_A_4_semantic :=
  GenLimit.BoundedMemory.incremental_coding_compilation
alias theorem_A_5_nat_semantic :=
  GenLimit.BoundedMemory.incremental_element_generation

end GenLimit.BoundedMemory.Results
