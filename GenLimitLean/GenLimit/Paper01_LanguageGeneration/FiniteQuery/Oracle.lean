import GenLimit.Core.OracleFamily
import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Critical

/-!
# #01 Language Generation: finite membership-oracle realization

The paper assumes a single algorithm that answers membership queries uniformly
in the language index.  The definitions below turn every test used by the
finite critical-language selector into an explicit finite Boolean computation.

The shared `OracleFamily` record lives in `GenLimit.Core.OracleFamily`; this
module contains the KM-specific finite tests built from its query function.
-/

namespace GenLimit

namespace OracleFamily

variable (O : OracleFamily)

/-- The part of language `i` lying in the strict prefix `{u | u < m}`. -/
def finitePrefix (i m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun u => O.query i u = true)

@[simp] theorem mem_finitePrefix {i m u : ℕ} :
    u ∈ O.finitePrefix i m ↔ u < m ∧ u ∈ O.language i := by
  simp [finitePrefix, O.query_spec]

/-- Observed counterexamples to consistency. -/
def inconsistentSamples (stream : ℕ → ℕ) (t i : ℕ) : Finset ℕ :=
  (sample stream t).filter (fun u => O.query i u = false)

/-- Executable consistency test. -/
def ConsistentAt (stream : ℕ → ℕ) (t i : ℕ) : Prop :=
  O.inconsistentSamples stream t i = ∅

instance consistentAtDecidable (stream : ℕ → ℕ) (t i : ℕ) :
    Decidable (O.ConsistentAt stream t i) := by
  unfold ConsistentAt
  infer_instance

theorem consistentAt_iff {stream : ℕ → ℕ} {t i : ℕ} :
    O.ConsistentAt stream t i ↔
      Consistent O.language stream t i := by
  rw [ConsistentAt, inconsistentSamples, Finset.filter_eq_empty_iff]
  constructor
  · intro h u hu
    apply (O.query_spec i u).mp
    have hnot := h hu
    cases hq : O.query i u with
    | false => exact False.elim (hnot hq)
    | true => rfl
  · intro h u hu hfalse
    have htrue : O.query i u = true :=
      (O.query_spec i u).mpr (h hu)
    simp [htrue] at hfalse

/-- Earlier consistent indices that witness failure of finite criticality. -/
def criticalFailures (stream : ℕ → ℕ) (t m n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun i =>
    O.ConsistentAt stream t i ∧
      ¬ O.finitePrefix n m ⊆ O.finitePrefix i m)

/-- Executable finite criticality test. -/
def FinitelyCriticalAt (stream : ℕ → ℕ) (t m n : ℕ) : Prop :=
  O.ConsistentAt stream t n ∧ O.criticalFailures stream t m n = ∅

instance finitelyCriticalAtDecidable (stream : ℕ → ℕ) (t m n : ℕ) :
    Decidable (O.FinitelyCriticalAt stream t m n) := by
  unfold FinitelyCriticalAt
  infer_instance

theorem finitelyCriticalAt_iff
    {stream : ℕ → ℕ} {t m n : ℕ} :
    O.FinitelyCriticalAt stream t m n ↔
      FinitelyCritical O.language stream t m n := by
  constructor
  · rintro ⟨hn, hfail⟩
    refine ⟨O.consistentAt_iff.mp hn, ?_⟩
    intro i hin hicon u hum hun
    have hiRange : i ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hin)
    have hiNotFailure :
        ¬ (O.ConsistentAt stream t i ∧
          ¬ O.finitePrefix n m ⊆ O.finitePrefix i m) := by
      intro hpair
      have hi : i ∈ O.criticalFailures stream t m n := by
        rw [criticalFailures, Finset.mem_filter]
        exact ⟨hiRange, hpair⟩
      rw [hfail] at hi
      exact Finset.notMem_empty i hi
    have hprefix : O.finitePrefix n m ⊆ O.finitePrefix i m := by
      by_contra hnot
      exact hiNotFailure ⟨O.consistentAt_iff.mpr hicon, hnot⟩
    exact (O.mem_finitePrefix.mp
      (hprefix (O.mem_finitePrefix.mpr ⟨hum, hun⟩))).2
  · rintro ⟨hn, hmin⟩
    refine ⟨O.consistentAt_iff.mpr hn, ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rw [criticalFailures, Finset.mem_filter] at hi
    rcases hi with ⟨hiRange, hicon, hnot⟩
    have hin : i ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hiRange)
    apply hnot
    intro u hu
    have hu' := O.mem_finitePrefix.mp hu
    exact O.mem_finitePrefix.mpr
      ⟨hu'.1, hmin i hin (O.consistentAt_iff.mp hicon) u hu'.1 hu'.2⟩

end OracleFamily

end GenLimit
