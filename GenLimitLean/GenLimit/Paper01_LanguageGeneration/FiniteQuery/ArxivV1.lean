import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Selection
import Mathlib.Order.Interval.Finset.Nat

/-!
# #01 Language Generation: arXiv-v1 finite-query generator

This module formalizes the finite-query algorithm in arXiv:2404.06757v1,
Section "Generation in the Limit via an Algorithm".  It is deliberately
parallel to, rather than a replacement for, the endpoint-test algorithm in
the NeurIPS proceedings.

At cutoff `q`, the arXiv-v1 algorithm searches the whole queried prefix of the
currently selected finite-critical language and returns its least element not
already in the observed sample.  Thus its output may be strictly below the
new endpoint `q - 1`; the machine stores the queried cutoff separately.
-/

namespace GenLimit
namespace OracleFamily
namespace ArxivV1

variable (O : OracleFamily)

/-- Fresh elements of the selected finite-critical language visible below the
strict cutoff `q`. -/
def eligible
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (q : ℕ) : Finset ℕ :=
  (O.finitePrefix (O.selected stream t q h) q).filter
    (fun u => u ∉ sample stream t)

@[simp] theorem mem_eligible
    {stream : ℕ → ℕ} {t q u : ℕ} (h : O.HasConsistent stream t) :
    u ∈ eligible O stream t h q ↔
      u ∈ O.finitePrefix (O.selected stream t q h) q ∧
        u ∉ sample stream t := by
  simp [eligible]

/-- The arXiv-v1 stopping test: the queried prefix contains a fresh eligible
element. -/
def HasFreshEligible
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (q : ℕ) : Prop :=
  (eligible O stream t h q).Nonempty

instance hasFreshEligibleDecidable
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (q : ℕ) :
    Decidable (HasFreshEligible O stream t h q) := by
  unfold HasFreshEligible
  infer_instance

/-- The first-fresh search terminates.  Stabilization fixes the selected
language, and infinitude supplies a member beyond both the old cutoff and a
finite bound for the observed sample. -/
theorem hasFreshEligible_exists
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    ∃ q, b < q ∧ HasFreshEligible O stream t h q := by
  obtain ⟨M, hM⟩ := O.selected_eventually_constant h
  obtain ⟨B, hB⟩ := Finset.exists_nat_subset_range (sample stream t)
  let n := O.selected stream t M h
  obtain ⟨e, he, heLower⟩ :=
    (O.infinite' n).exists_gt (max (max b M) B)
  let q := e + 1
  have hbLower : b ≤ max (max b M) B :=
    le_trans (Nat.le_max_left b M) (Nat.le_max_left (max b M) B)
  have hMLower : M ≤ max (max b M) B :=
    le_trans (Nat.le_max_right b M) (Nat.le_max_left (max b M) B)
  have hBLower : B ≤ max (max b M) B :=
    Nat.le_max_right (max b M) B
  have hbq : b < q :=
    lt_trans (lt_of_le_of_lt hbLower heLower) (Nat.lt_succ_self e)
  have hMq : M ≤ q :=
    le_trans (le_trans hMLower (Nat.le_of_lt heLower))
      (Nat.le_succ e)
  have heFresh : e ∉ sample stream t := by
    intro heSample
    have heB : e < B := Finset.mem_range.mp (hB heSample)
    have hBe : B ≤ e :=
      le_trans hBLower (Nat.le_of_lt heLower)
    exact (Nat.not_lt_of_ge hBe) heB
  refine ⟨q, hbq, ?_⟩
  refine ⟨e, (mem_eligible O h).mpr ⟨?_, heFresh⟩⟩
  apply O.mem_finitePrefix.mpr
  refine ⟨?_, ?_⟩
  · exact Nat.lt_succ_self e
  · rw [hM q hMq]
    exact he

/-- The least cutoff after `b` at which the arXiv-v1 prefix contains a fresh
eligible element. -/
def roundCounter
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (b : ℕ) : ℕ :=
  Nat.find (hasFreshEligible_exists O h b)

theorem roundCounter_spec
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    b < roundCounter O stream t h b ∧
      HasFreshEligible O stream t h (roundCounter O stream t h b) := by
  exact Nat.find_spec (hasFreshEligible_exists O h b)

theorem roundCounter_gt
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    b < roundCounter O stream t h b :=
  (roundCounter_spec O h b).1

theorem roundCounter_le_of_freshEligible
    {stream : ℕ → ℕ} {t q : ℕ} (h : O.HasConsistent stream t) (b : ℕ)
    (hbq : b < q) (hq : HasFreshEligible O stream t h q) :
    roundCounter O stream t h b ≤ q := by
  exact Nat.find_min' (hasFreshEligible_exists O h b) ⟨hbq, hq⟩

/-- The literal arXiv-v1 choice: the least fresh eligible element in the
first successful queried prefix. -/
def roundOutput
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (b : ℕ) : ℕ :=
  (eligible O stream t h (roundCounter O stream t h b)).min'
    (roundCounter_spec O h b).2

theorem roundOutput_mem_eligible
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    roundOutput O stream t h b ∈
      eligible O stream t h (roundCounter O stream t h b) := by
  exact Finset.min'_mem _ _

theorem roundOutput_le_of_mem
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b u : ℕ)
    (hu : u ∈ eligible O stream t h (roundCounter O stream t h b)) :
    roundOutput O stream t h b ≤ u := by
  exact Finset.min'_le _ _ hu

theorem roundOutput_spec
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    roundOutput O stream t h b ∈
        O.finitePrefix
          (O.selected stream t (roundCounter O stream t h b) h)
          (roundCounter O stream t h b) ∧
      roundOutput O stream t h b ∉ sample stream t ∧
      ∀ u, u ∈
          O.finitePrefix
            (O.selected stream t (roundCounter O stream t h b) h)
            (roundCounter O stream t h b) →
        u ∉ sample stream t →
          roundOutput O stream t h b ≤ u := by
  have hout :=
    (mem_eligible O h).mp (roundOutput_mem_eligible O h b)
  refine ⟨hout.1, hout.2, ?_⟩
  intro u huPrefix huFresh
  exact roundOutput_le_of_mem O h b u
    ((mem_eligible O h).mpr ⟨huPrefix, huFresh⟩)

/-- The arXiv-v1 machine separates the queried cutoff from the output, since
the least eligible output can lie earlier in the prefix. -/
structure MachineState where
  counter : ℕ
  output : ℕ
deriving Repr

def processRound
    (stream : ℕ → ℕ) (t b : ℕ) : MachineState :=
  if h : O.HasConsistent stream t then
    ⟨roundCounter O stream t h b, roundOutput O stream t h b⟩
  else
    ⟨b, 0⟩

theorem processRound_counter_ge_start
    (stream : ℕ → ℕ) (t b : ℕ) :
    b ≤ (processRound O stream t b).counter := by
  unfold processRound
  split
  · exact Nat.le_of_lt (roundCounter_gt O _ b)
  · exact Nat.le_refl b

theorem processRound_of_hasConsistent
    {stream : ℕ → ℕ} {t b : ℕ} (h : O.HasConsistent stream t) :
    processRound O stream t b =
      ⟨roundCounter O stream t h b, roundOutput O stream t h b⟩ := by
  simp [processRound, h]

/-- The arXiv-v1 state after the first `t` observations and rounds. -/
def run (O : OracleFamily) (stream : ℕ → ℕ) : ℕ → MachineState
  | 0 => ⟨0, 0⟩
  | t + 1 =>
      let previous := run O stream t
      let start := max previous.counter (stream t + 1)
      processRound O stream (t + 1) start

theorem run_succ_counter_ge_start
    (stream : ℕ → ℕ) (t : ℕ) :
    max (run O stream t).counter (stream t + 1) ≤
      (run O stream (t + 1)).counter := by
  simpa [run] using processRound_counter_ge_start O stream (t + 1)
    (max (run O stream t).counter (stream t + 1))

/-- Every observation processed by time `t` lies below the queried cutoff.
This is the finite-access invariant needed even when observations repeat. -/
theorem run_counter_bounds
    {stream : ℕ → ℕ} :
    ∀ {t k}, k < t → stream k < (run O stream t).counter := by
  intro t
  induction t with
  | zero =>
      intro k hk
      exact False.elim (Nat.not_lt_zero k hk)
  | succ t ih =>
      intro k hk
      have hstart := run_succ_counter_ge_start O stream t
      have hkstart :
          stream k < max (run O stream t).counter (stream t + 1) := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkt | rfl
        · exact lt_of_lt_of_le (ih hkt) (Nat.le_max_left _ _)
        · exact lt_of_lt_of_le (Nat.lt_succ_self _)
            (Nat.le_max_right _ _)
      exact lt_of_lt_of_le hkstart hstart

theorem sample_lt_runCounter
    {stream : ℕ → ℕ} {t u : ℕ} (hu : u ∈ sample stream t) :
    u < (run O stream t).counter := by
  rw [mem_sample_iff] at hu
  obtain ⟨k, hk, rfl⟩ := hu
  exact run_counter_bounds O hk

/-- The exact successful-round invariant of the arXiv-v1 algorithm: the
output is the least fresh element of the maximal finite-critical prefix. -/
theorem run_round_spec
    {stream : ℕ → ℕ} {t : ℕ} (ht : 0 < t)
    (h : O.HasConsistent stream t) :
    ∃ n,
      n < t ∧
      FinitelyCritical O.language stream t (run O stream t).counter n ∧
      (∀ j, j < t →
        FinitelyCritical O.language stream t (run O stream t).counter j →
        j ≤ n) ∧
      (run O stream t).output ∈
        O.finitePrefix n (run O stream t).counter ∧
      (run O stream t).output ∉ sample stream t ∧
      (∀ u, u ∈ O.finitePrefix n (run O stream t).counter →
        u ∉ sample stream t →
          (run O stream t).output ≤ u) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  let b := max (run O stream s).counter (stream s + 1)
  let q := roundCounter O stream (s + 1) h b
  have hrun :
      run O stream (s + 1) =
        ⟨q, roundOutput O stream (s + 1) h b⟩ := by
    rw [run]
    exact processRound_of_hasConsistent O h
  let n := O.selected stream (s + 1) q h
  have hout := roundOutput_spec O h b
  refine ⟨n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact O.selected_lt h
  · rw [hrun]
    exact O.selected_finitelyCritical h
  · intro j hjt hjfc
    rw [hrun] at hjfc
    exact O.selected_max h hjt (O.finitelyCriticalAt_iff.mpr hjfc)
  · rw [hrun]
    exact hout.1
  · rw [hrun]
    exact hout.2.1
  · intro u huPrefix huFresh
    rw [hrun] at huPrefix ⊢
    exact hout.2.2 u huPrefix huFresh

/-- The arXiv-v1 generator's output after the first `t` observations. -/
def kmGenerator (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  (run O stream t).output

def GeneratesInLimit (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    kmGenerator O stream t ∈ O.language z ∧
      kmGenerator O stream t ∉ sample stream t

/-- The arXiv-v1 analogue of the paper's final correctness statement. -/
theorem eventual_correctness
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GeneratesInLimit O stream z := by
  obtain ⟨T, hcritical⟩ := target_eventually_finitelyCritical hP
  refine ⟨max T (z + 1), ?_⟩
  intro t ht
  have hT : T ≤ t := le_trans (Nat.le_max_left T (z + 1)) ht
  have hzt : z < t :=
    Nat.lt_of_succ_le (le_trans (Nat.le_max_right T (z + 1)) ht)
  have hzcon : Consistent O.language stream t z :=
    presents_consistent hP
  have hhas : O.HasConsistent stream t := by
    refine ⟨z, O.mem_consistentCandidates.mpr ⟨hzt, ?_⟩⟩
    exact O.consistentAt_iff.mpr hzcon
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le z) hzt
  obtain ⟨n, hnlt, hncritical, hmaximal, hout, hfresh, _hleast⟩ :=
    run_round_spec O htpos hhas
  have hzcritical :
      FinitelyCritical O.language stream t (run O stream t).counter z :=
    hcritical t hT (run O stream t).counter
  have hzn : z ≤ n := hmaximal z hzt hzcritical
  have hnest :=
    finitelyCritical_prefix_subset hzn hzcritical hncritical
  have hout' := O.mem_finitePrefix.mp hout
  exact
    ⟨hnest (kmGenerator O stream t) hout'.1 hout'.2, hfresh⟩

/-- Theorem 2.1 via the literal first-fresh-eligible finite-query algorithm
of arXiv:2404.06757v1.  The presentation may contain arbitrary repetitions. -/
theorem kleinbergMullainathan_main
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GeneratesInLimit O stream z :=
  eventual_correctness O hP

end ArxivV1
end OracleFamily
end GenLimit
