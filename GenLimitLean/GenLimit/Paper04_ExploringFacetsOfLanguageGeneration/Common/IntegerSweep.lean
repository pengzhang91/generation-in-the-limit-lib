import Mathlib.Logic.Equiv.Nat

/-!
# Integer sweep used by Paper04 examples

The fixed order `0, -1, 1, -2, 2, ...` is shared by the exhaustive-generation
example and the feedback example, so it lives in a small paper-local common
module rather than either result file.
-/

namespace GenLimit.CharikarPabbaraju

def integerSweep : ℕ → ℤ := Equiv.intEquivNat.symm

theorem integerSweep_bijective : Function.Bijective integerSweep :=
  Equiv.intEquivNat.symm.bijective

@[simp] theorem integerSweep_equivIndex (z : ℤ) :
    integerSweep (Equiv.intEquivNat z) = z :=
  Equiv.intEquivNat.symm_apply_apply z

end GenLimit.CharikarPabbaraju
