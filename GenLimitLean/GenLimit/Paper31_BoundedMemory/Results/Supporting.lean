import GenLimit.Paper31_BoundedMemory.FixedOrderDensity
import GenLimit.Paper31_BoundedMemory.CountableCoding

/-! # Earlier interfaces for the order-robust and natural-number specializations -/

namespace GenLimit.BoundedMemory.Results

alias theorem_4_1_order_robust :=
  GenLimit.BoundedMemory.theorem_4_1_memoryless_minimax_upper_density

alias theorem_4_2_order_robust :=
  GenLimit.BoundedMemory.theorem_4_2_no_uniform_positive_lower_density

alias theorem_4_10_order_robust :=
  GenLimit.BoundedMemory.theorem_4_10_window_minimax_upper_density

alias theorem_4_15_order_robust :=
  GenLimit.BoundedMemory.theorem_4_15_adaptive_buffer_lower_bound

alias theorem_A_4_semantic :=
  GenLimit.BoundedMemory.incremental_coding_compilation

alias theorem_A_5_nat_semantic :=
  GenLimit.BoundedMemory.incremental_element_generation

end GenLimit.BoundedMemory.Results
