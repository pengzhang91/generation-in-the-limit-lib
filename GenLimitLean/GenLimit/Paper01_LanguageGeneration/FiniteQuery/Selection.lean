import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Oracle
import Mathlib.Data.Finset.Max

/-!
# The maximal finite-critical candidate

At fixed time `t` and cutoff `m`, the algorithm selects the largest candidate
index below `t` that is finite-critical. This file proves that the selector is
defined whenever some candidate is consistent, is non-increasing in `m`, and
therefore eventually stabilizes.
-/

namespace GenLimit
namespace OracleFamily

variable (O : OracleFamily)

def consistentCandidates (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun i => O.ConsistentAt stream t i)

def HasConsistent (stream : ℕ → ℕ) (t : ℕ) : Prop :=
  (O.consistentCandidates stream t).Nonempty

instance hasConsistentDecidable (stream : ℕ → ℕ) (t : ℕ) :
    Decidable (O.HasConsistent stream t) := by
  unfold HasConsistent
  infer_instance

@[simp] theorem mem_consistentCandidates
    {stream : ℕ → ℕ} {t i : ℕ} :
    i ∈ O.consistentCandidates stream t ↔
      i < t ∧ O.ConsistentAt stream t i := by
  simp [consistentCandidates]

def criticalCandidates (stream : ℕ → ℕ) (t m : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun n => O.FinitelyCriticalAt stream t m n)

@[simp] theorem mem_criticalCandidates
    {stream : ℕ → ℕ} {t m n : ℕ} :
    n ∈ O.criticalCandidates stream t m ↔
      n < t ∧ O.FinitelyCriticalAt stream t m n := by
  simp [criticalCandidates]

theorem criticalCandidates_nonempty
    {stream : ℕ → ℕ} {t : ℕ}
    (h : O.HasConsistent stream t) (m : ℕ) :
    (O.criticalCandidates stream t m).Nonempty := by
  let n := (O.consistentCandidates stream t).min' h
  have hnmem : n ∈ O.consistentCandidates stream t :=
    Finset.min'_mem _ h
  have hn := O.mem_consistentCandidates.mp hnmem
  have hleast :
      ∀ i, i < n → ¬ Consistent O.language stream t i := by
    intro i hin hicon
    have hiCandidate : i ∈ O.consistentCandidates stream t :=
      O.mem_consistentCandidates.mpr
        ⟨lt_trans hin hn.1, O.consistentAt_iff.mpr hicon⟩
    have hni : n ≤ i := Finset.min'_le _ i hiCandidate
    exact (Nat.not_le_of_lt hin) hni
  have hnfc : FinitelyCritical O.language stream t m n :=
    least_consistent_finitelyCritical
      (O.consistentAt_iff.mp hn.2) hleast m
  exact ⟨n, O.mem_criticalCandidates.mpr
    ⟨hn.1, O.finitelyCriticalAt_iff.mpr hnfc⟩⟩

/-- The paper's index `n_t(m)`: the largest finite-critical candidate. -/
def selected
    (stream : ℕ → ℕ) (t m : ℕ) (h : O.HasConsistent stream t) : ℕ :=
  (O.criticalCandidates stream t m).max'
    (O.criticalCandidates_nonempty h m)

theorem selected_mem
    {stream : ℕ → ℕ} {t m : ℕ} (h : O.HasConsistent stream t) :
    O.selected stream t m h ∈ O.criticalCandidates stream t m := by
  exact Finset.max'_mem _ _

theorem selected_lt
    {stream : ℕ → ℕ} {t m : ℕ} (h : O.HasConsistent stream t) :
    O.selected stream t m h < t :=
  (O.mem_criticalCandidates.mp (O.selected_mem h)).1

theorem selected_finitelyCriticalAt
    {stream : ℕ → ℕ} {t m : ℕ} (h : O.HasConsistent stream t) :
    O.FinitelyCriticalAt stream t m (O.selected stream t m h) :=
  (O.mem_criticalCandidates.mp (O.selected_mem h)).2

theorem selected_finitelyCritical
    {stream : ℕ → ℕ} {t m : ℕ} (h : O.HasConsistent stream t) :
    FinitelyCritical O.language stream t m (O.selected stream t m h) :=
  O.finitelyCriticalAt_iff.mp (O.selected_finitelyCriticalAt h)

theorem selected_max
    {stream : ℕ → ℕ} {t m n : ℕ} (h : O.HasConsistent stream t)
    (hnt : n < t) (hn : O.FinitelyCriticalAt stream t m n) :
    n ≤ O.selected stream t m h := by
  exact Finset.le_max' _ n (O.mem_criticalCandidates.mpr ⟨hnt, hn⟩)

/-- Equation (5.4) makes the selected index non-increasing with the cutoff. -/
theorem selected_antitone
    {stream : ℕ → ℕ} {t m m' : ℕ} (h : O.HasConsistent stream t)
    (hmm' : m ≤ m') :
    O.selected stream t m' h ≤ O.selected stream t m h := by
  apply O.selected_max h (O.selected_lt h)
  apply O.finitelyCriticalAt_iff.mpr
  exact finitelyCritical_cutoff_mono hmm'
    (O.selected_finitelyCritical h)

/-- A non-increasing natural-number sequence eventually becomes constant. -/
theorem antitone_nat_eventually_constant
    (f : ℕ → ℕ) (hf : Antitone f) :
    ∃ M, ∀ m, M ≤ m → f m = f M := by
  obtain ⟨v, ⟨M, rfl⟩, hmin⟩ :=
    Nat.lt_wfRel.wf.has_min (Set.range f) ⟨f 0, ⟨0, rfl⟩⟩
  refine ⟨M, ?_⟩
  intro m hm
  apply Nat.le_antisymm (hf hm)
  apply Nat.le_of_not_gt
  intro hlt
  exact hmin (f m) ⟨m, rfl⟩ hlt

theorem selected_eventually_constant
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) :
    ∃ M, ∀ m, M ≤ m →
      O.selected stream t m h = O.selected stream t M h := by
  apply antitone_nat_eventually_constant
  intro m m' hmm'
  exact O.selected_antitone h hmm'

end OracleFamily
end GenLimit
