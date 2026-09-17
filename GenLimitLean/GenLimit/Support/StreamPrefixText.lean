import GenLimit.Core.Text
import GenLimit.Support.StreamPrefix
import Mathlib.Data.List.OfFn

/-!
# Ordered prefixes of prepended streams

This small extension keeps the legacy ordered-text dependency out of the
basic `StreamPrefix` module.  Clients that only need generic streams, ranges,
or exact presentations therefore do not acquire the fixed-`ℕ` vocabulary
from `Core.Text` and `Core.Basic`.
-/

namespace GenLimit.Support

/-- The finite prefix of a prepended stream is the original list followed by
the corresponding finite prefix of the tail. -/
theorem textPrefix_prependStream
    (xs : List α) (tail : GenLimit.Generic.Stream α) (t : ℕ) :
    GenLimit.textPrefix (prependStream xs tail) (xs.length + t) =
      xs ++ GenLimit.textPrefix tail t := by
  rw [GenLimit.textPrefix_eq_ofFn, GenLimit.textPrefix_eq_ofFn]
  calc
    List.ofFn
        (fun i : Fin (xs.length + t) => prependStream xs tail i) =
        List.ofFn (Fin.append xs.get (fun i : Fin t => tail i)) := by
      congr 1
      funext q
      refine Fin.addCases ?_ ?_ q
      · intro i
        simp [prependStream, Fin.append]
      · intro i
        simp [prependStream, Fin.append]
    _ = List.ofFn xs.get ++ List.ofFn (fun i : Fin t => tail i) :=
      List.ofFn_fin_append _ _
    _ = xs ++ List.ofFn (fun i : Fin t => tail i) := by simp

end GenLimit.Support
