import GenLimit.KM.FiniteQuery.Machine

/-!
# Finite-query Kleinberg--Mullainathan main theorem

The generator below is fixed by the indexed oracle family. It does not receive
the target language index. For every exact presentation of any target in the
family, its outputs are eventually fresh elements of that target language.

This is the stateful, finite-membership-query Proceedings construction.  The
shorter classical construction lives in `GenLimit.KM.Semantic`.
-/

namespace GenLimit
namespace OracleFamily

variable (O : OracleFamily)

/-- The generator's output after the first `t` observations. -/
def kmGenerator (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  (O.run stream t).output

def GeneratesInLimit (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    O.kmGenerator stream t ∈ O.language z ∧
      O.kmGenerator stream t ∉ sample stream t

/-- Equation (5.7): after a presentation-dependent threshold, each output is a
fresh member of the target. -/
theorem eventual_correctness
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    O.GeneratesInLimit stream z := by
  obtain ⟨T, hcritical⟩ := target_eventually_finitelyCritical hP
  refine ⟨max T (z + 1), ?_⟩
  intro t ht
  have hT : T ≤ t := le_trans (Nat.le_max_left T (z + 1)) ht
  have hzt : z < t :=
    Nat.lt_of_succ_le (le_trans (Nat.le_max_right T (z + 1)) ht)
  have hzcon : Consistent O.language stream t z := presents_consistent hP
  have hhas : O.HasConsistent stream t := by
    refine ⟨z, O.mem_consistentCandidates.mpr ⟨hzt, ?_⟩⟩
    exact O.consistentAt_iff.mpr hzcon
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le z) hzt
  obtain ⟨n, hnlt, hncritical, hmaximal, hout, hfresh⟩ :=
    O.run_round_spec htpos hhas
  have hzcritical :
      FinitelyCritical O.language stream t (O.run stream t).counter z :=
    hcritical t hT (O.run stream t).counter
  have hzn : z ≤ n := hmaximal z hzt hzcritical
  have hnest := finitelyCritical_prefix_subset hzn hzcritical hncritical
  have hout' := O.mem_finitePrefix.mp hout
  exact ⟨hnest (O.kmGenerator stream t) hout'.1 hout'.2, hfresh⟩

/-- Theorem (2.1) of Kleinberg--Mullainathan, for the countable universe `ℕ`.

The threshold is presentation-dependent, as required by generation in the
limit. The generator itself depends only on the indexed family and its uniform
membership oracle, not on `z` or on a promised convergence time. -/
theorem kleinbergMullainathan_main
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    O.GeneratesInLimit stream z :=
  O.eventual_correctness hP

end OracleFamily
end GenLimit
