import GenLimit.Core.ClassCovers
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Range

/-!
# Canonical finite-prefix covers of countable classes

A countable language class is covered by the nondecreasing sequence of its
finite enumerated prefixes.  Several non-uniform generation arguments use
this same paper-independent construction.
-/

namespace GenLimit.Support

/-- Languages of `H` appearing among the first `n + 1` values of an ambient
enumeration. -/
def finitePrefixSubclass
    (H : GenLimit.Generic.LanguageClass α)
    (enumerate : ℕ → GenLimit.Generic.Language α)
    (n : ℕ) : GenLimit.Generic.LanguageClass α :=
  {L | L ∈ H ∧ ∃ i < n + 1, enumerate i = L}

theorem finitePrefixSubclass_mono
    (H : GenLimit.Generic.LanguageClass α)
    (enumerate : ℕ → GenLimit.Generic.Language α)
    {m n : ℕ} (hmn : m ≤ n) :
    finitePrefixSubclass H enumerate m ⊆
      finitePrefixSubclass H enumerate n := by
  rintro L ⟨hLH, i, him, hiL⟩
  exact
    ⟨hLH, i, him.trans_le (Nat.add_le_add_right hmn 1), hiL⟩

theorem iUnion_finitePrefixSubclass
    (H : GenLimit.Generic.LanguageClass α)
    (enumerate : ℕ → GenLimit.Generic.Language α)
    (hEnumerates : H ⊆ Set.range enumerate) :
    ⋃ n, finitePrefixSubclass H enumerate n = H := by
  ext L
  constructor
  · intro hL
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hL
    exact hn.1
  · intro hLH
    obtain ⟨i, hiL⟩ := hEnumerates hLH
    exact Set.mem_iUnion.mpr
      ⟨i, hLH, i, Nat.lt_succ_self i, hiL⟩

theorem finitePrefixSubclass_isNondecreasingCover
    (H : GenLimit.Generic.LanguageClass α)
    (enumerate : ℕ → GenLimit.Generic.Language α)
    (hEnumerates : H ⊆ Set.range enumerate) :
    GenLimit.Generic.IsNondecreasingCover H
      (finitePrefixSubclass H enumerate) :=
  ⟨fun _m _n hmn => finitePrefixSubclass_mono H enumerate hmn,
    (iUnion_finitePrefixSubclass H enumerate hEnumerates).symm⟩

theorem finitePrefixSubclass_finite
    (H : GenLimit.Generic.LanguageClass α)
    (enumerate : ℕ → GenLimit.Generic.Language α)
    (n : ℕ) :
    (finitePrefixSubclass H enumerate n).Finite := by
  apply
    (Set.finite_range
      (fun i : Fin (n + 1) => enumerate i)).subset
  rintro L ⟨_hLH, i, hin, rfl⟩
  exact ⟨⟨i, hin⟩, rfl⟩

end GenLimit.Support
