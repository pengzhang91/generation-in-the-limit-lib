import GenLimit.Core.OracleFamily
import GenLimit.Paper01_LanguageGeneration.Critical
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

/-!
# #01 Language Generation: semantic generator

This module isolates the short mathematical idea behind KM Theorem 2.1.  At
time `t`, it classically selects the highest semantically critical index below
`t` and then selects the least element of that language outside the adversary
sample.

More precisely, this module formalizes the noncomputable construction in
Section 4 of the KM NeurIPS paper, especially (4.2)--(4.6).  Statement (4.1)
describes `f_C` as a function of the observed finite set alone, whereas the
construction in (4.5) selects among the first `t` candidate languages.  Since
the paper permits repeated observations, the set does not in general determine
`t`.  This module follows the round-dependent rule in (4.5) and makes `t`
explicit; it does not formalize the literal finite-set-only interface in (4.1).

The construction is `noncomputable`: semantic
criticality tests inclusion between whole infinite languages.  It therefore
does not implement those tests using the pointwise membership oracle.  The
finite-query Proceedings algorithm is formalized separately under
`GenLimit.Paper01_LanguageGeneration.FiniteQuery`.

The conclusion matches the current KM Lean theorem: eventual target membership
and freshness relative to the adversary sample.  It does not add a requirement
that generator outputs be distinct from one another.
-/

namespace GenLimit
namespace KM
namespace Semantic

/-- Semantically critical indices in the current finite scope. -/
noncomputable def criticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter (Critical C stream t)

@[simp] theorem mem_criticalIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ} :
    n ∈ criticalIndices C stream t ↔ n < t ∧ Critical C stream t n := by
  classical
  simp [criticalIndices]

/-- Highest semantically critical index in scope, with an arbitrary default
before the scope contains any consistent language. -/
noncomputable def focus
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ := by
  classical
  let candidates := criticalIndices C stream t
  exact if h : candidates.Nonempty then candidates.max' h else 0

/-- If a critical index is in scope, the semantic focus is critical, is also in
scope, and is no earlier than that index. -/
theorem focus_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z : ℕ}
    (hzt : z < t) (hz : Critical C stream t z) :
    focus C stream t < t ∧
      Critical C stream t (focus C stream t) ∧
      z ≤ focus C stream t := by
  classical
  let candidates := criticalIndices C stream t
  have hzmem : z ∈ candidates := by
    simpa [candidates] using (mem_criticalIndices.mpr ⟨hzt, hz⟩)
  have hne : candidates.Nonempty := ⟨z, hzmem⟩
  have hfmem : candidates.max' hne ∈ candidates :=
    Finset.max'_mem candidates hne
  have hfocus : focus C stream t = candidates.max' hne := by
    simp [focus, candidates, hne]
  rw [hfocus]
  have hparts :
      candidates.max' hne < t ∧
        Critical C stream t (candidates.max' hne) := by
    simpa [candidates] using (mem_criticalIndices.mp hfmem)
  exact ⟨hparts.1, hparts.2, Finset.le_max' candidates z hzmem⟩

/-- The least element of language `i` outside the current adversary sample. -/
noncomputable def fresh
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : ℕ := by
  classical
  exact Nat.find ((O.infinite' i).exists_notMem_finset (sample stream t))

theorem fresh_spec
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) :
    fresh O stream t i ∈ O.language i ∧
      fresh O stream t i ∉ sample stream t := by
  classical
  exact Nat.find_spec ((O.infinite' i).exists_notMem_finset (sample stream t))

/-- The direct semantic KM generator. -/
noncomputable def generator
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  fresh O stream t (focus O.language stream t)

theorem generator_spec
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    generator O stream t ∈ O.language (focus O.language stream t) ∧
      generator O stream t ∉ sample stream t :=
  fresh_spec O stream t (focus O.language stream t)

/-- The current KM Lean conclusion, specialized to the semantic generator. -/
def GeneratesInLimit
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    generator O stream t ∈ O.language z ∧
      generator O stream t ∉ sample stream t

/-- KM Theorem 2.1 at the semantic, noncomputable level. -/
theorem kleinbergMullainathan_main
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GeneratesInLimit O stream z := by
  obtain ⟨T, hcritical⟩ := target_eventually_critical hP
  refine ⟨max T (z + 1), ?_⟩
  intro t ht
  have hT : T ≤ t := le_trans (Nat.le_max_left T (z + 1)) ht
  have hzt : z < t :=
    Nat.lt_of_succ_le (le_trans (Nat.le_max_right T (z + 1)) ht)
  have hzcritical := hcritical t hT
  have hf := focus_spec hzt hzcritical
  have hout := generator_spec O stream t
  have hsub : O.language (focus O.language stream t) ⊆ O.language z :=
    critical_subset_of_le hf.2.2 hzcritical hf.2.1
  exact ⟨hsub hout.1, hout.2⟩

end Semantic
end KM
end GenLimit
