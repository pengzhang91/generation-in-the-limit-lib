import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TotalizedGCGMachine
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyRun

/-!
# Progress of the totalized GCG queue

The stable-stage theorem from `GreedyRun` forces every queued stage to cross
its threshold.  This file connects that theorem to the concrete recursive
run and proves that the stage counter is unbounded.
-/

namespace GenLimit.TimeSensitive

open Filter

theorem outputHistoryStream_totalized_outputs
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    {n k : ℕ} (hk : k < n) :
    outputHistoryStream (totalizedGCGRun F stream n).outputs k =
      totalizedGCGOutput F stream k := by
  rw [totalizedGCGRun_outputs_eq]
  simp [outputHistoryStream, hk]

theorem sequencePrefix_outputHistory_totalized
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    {n k : ℕ} (hkn : k ≤ n) :
    sequencePrefix
        (outputHistoryStream (totalizedGCGRun F stream n).outputs) k =
      sequencePrefix (totalizedGCGOutput F stream) k := by
  classical
  ext x
  simp only [mem_sequencePrefix_iff]
  constructor
  · rintro ⟨q, hqk, hqx⟩
    exact ⟨q, hqk, by
      rw [outputHistoryStream_totalized_outputs F stream
        (lt_of_lt_of_le hqk hkn)] at hqx
      exact hqx⟩
  · rintro ⟨q, hqk, hqx⟩
    exact ⟨q, hqk, by
      rw [outputHistoryStream_totalized_outputs F stream
        (lt_of_lt_of_le hqk hkn)]
      exact hqx⟩

theorem timelyDensity_outputHistory_totalized
    (F : CanonicallyOrderedFamily) (stream R : ℕ → ℕ) (n : ℕ) :
    timelyDensity
        (outputHistoryStream (totalizedGCGRun F stream n).outputs)
        R id n =
      timelyDensity (totalizedGCGOutput F stream) R id n := by
  letI : DecidableEq ℕ := Classical.decEq ℕ
  have helements :
      timelyElements
          (outputHistoryStream (totalizedGCGRun F stream n).outputs)
          R id n =
        timelyElements (totalizedGCGOutput F stream) R id n := by
    unfold timelyElements
    apply congrArg (Finset.image R)
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hjn, hj⟩
      refine ⟨hjn, ?_⟩
      rw [sequencePrefix_outputHistory_totalized F stream
        (show id j ≤ n by simpa using Nat.le_of_lt hjn)] at hj
      exact hj
    · rintro ⟨hjn, hj⟩
      refine ⟨hjn, ?_⟩
      rw [sequencePrefix_outputHistory_totalized F stream
        (show id j ≤ n by simpa using Nat.le_of_lt hjn)]
      exact hj
  rw [timelyDensity, timelyDensity, helements]

theorem totalizedGCGOutput_eq_onTimeUnused_of_stage_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    {m t : ℕ}
    (hstage : (totalizedGCGRun F stream t).stage = m) :
    totalizedGCGOutput F stream t =
      onTimeUnused (F.order (F.guess stream (m + 1)))
        (sample stream (t + 1) ∪
          sequencePrefix (totalizedGCGOutput F stream) t) t := by
  calc
    totalizedGCGOutput F stream t =
        onTimeUnused
          (F.order
            (F.guess stream
              ((totalizedGCGRun F stream t).stage + 1)))
          (sample stream (t + 1) ∪
            (totalizedGCGRun F stream t).outputs.toFinset) t := rfl
    _ = onTimeUnused (F.order (F.guess stream (m + 1)))
          (sample stream (t + 1) ∪
            (totalizedGCGRun F stream t).outputs.toFinset) t := by
      rw [hstage]
    _ = onTimeUnused (F.order (F.guess stream (m + 1)))
          (sample stream (t + 1) ∪
            sequencePrefix (totalizedGCGOutput F stream) t) t := by
      rw [totalizedGCGRun_outputs_toFinset]

theorem totalizedGCGRun_stage_succ_of_crossed
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    {m t : ℕ}
    (hstage : (totalizedGCGRun F stream t).stage = m)
    (hmt : m < t)
    (hcross : gcgThreshold (m + 1) ≤
      timelyDensity (totalizedGCGOutput F stream)
        (F.order (F.guess stream (m + 1))).enumeration id (t + 1)) :
    (totalizedGCGRun F stream (t + 1)).stage = m + 1 := by
  rw [totalizedGCGRun_succ]
  simp only [totalizedGCGStep]
  have hcross' :
      gcgThreshold ((totalizedGCGRun F stream t).stage + 1) ≤
        timelyDensity
          (outputHistoryStream
            ((totalizedGCGRun F stream t).outputs ++
              [totalizedGCGOutput F stream t]))
          (F.order
            (totalizedRoundActive F stream t
              (totalizedGCGRun F stream t))).enumeration
          id (t + 1) := by
    rw [← totalizedGCGRun_outputs_succ]
    rw [timelyDensity_outputHistory_totalized]
    simpa [totalizedRoundActive, hstage] using hcross
  rw [if_pos ⟨by simpa [hstage] using hmt, hcross'⟩, hstage]

/-- Once the concrete stage is fixed at `m`, the output sequence literally
satisfies the stable greedy contract for the queued guess `m + 1`. -/
theorem totalizedGCG_greedyFrom_of_stage_constant
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    {m T : ℕ}
    (hstage : ∀ t, T ≤ t →
      (totalizedGCGRun F stream t).stage = m) :
    GreedyFrom (F.order (F.guess stream (m + 1))) stream
      (totalizedGCGOutput F stream) T := by
  intro t ht
  exact totalizedGCGOutput_eq_onTimeUnused_of_stage_eq
    F stream (hstage t ht)

/-- Every finite queue stage is eventually reached and never left behind.
This is the concrete termination invariant omitted from the printed proof. -/
theorem totalizedGCG_stage_eventually_ge
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (m : ℕ) :
    ∃ T, ∀ t, T ≤ t →
      m ≤ (totalizedGCGRun F stream t).stage := by
  induction m with
  | zero => exact ⟨0, fun _ _ => Nat.zero_le _⟩
  | succ m ih =>
      obtain ⟨T, hT⟩ := ih
      by_cases hreach : ∃ t, T ≤ t ∧
          m + 1 ≤ (totalizedGCGRun F stream t).stage
      · obtain ⟨t, hTt, ht⟩ := hreach
        refine ⟨t, fun s hts => ?_⟩
        exact ht.trans
          (totalizedGCGRun_stage_mono F stream hts)
      · have hconstant : ∀ t, T ≤ t →
            (totalizedGCGRun F stream t).stage = m := by
          intro t ht
          have hlower := hT t ht
          have hupper : (totalizedGCGRun F stream t).stage < m + 1 := by
            by_contra hnot
            exact hreach ⟨t, ht, Nat.le_of_not_gt hnot⟩
          omega
        have hgreedy := totalizedGCG_greedyFrom_of_stage_constant
          F stream hconstant
        have hcross := stableGreedy_eventually_crosses_threshold
          (m := m + 1) (totalizedGCG_freshPlay F stream) hgreedy
        have hlarge : ∀ᶠ i in atTop, max (T + 1) (m + 2) ≤ i :=
          eventually_ge_atTop (max (T + 1) (m + 2))
        obtain ⟨i, hcrossAt, hilarge⟩ := (hcross.and hlarge).exists
        let t := i - 1
        have hiPos : 0 < i := by
          have : T + 1 ≤ i := (Nat.le_max_left _ _).trans hilarge
          omega
        have htSucc : t + 1 = i := by
          dsimp [t]
          omega
        have htT : T ≤ t := by
          have : T + 1 ≤ i := (Nat.le_max_left _ _).trans hilarge
          dsimp [t]
          omega
        have hmt : m < t := by
          have : m + 2 ≤ i := (Nat.le_max_right _ _).trans hilarge
          dsimp [t]
          omega
        have hnext :
            (totalizedGCGRun F stream (t + 1)).stage = m + 1 :=
          totalizedGCGRun_stage_succ_of_crossed F stream
            (hconstant t htT) hmt (by simpa [htSucc] using hcrossAt)
        exact False.elim (hreach ⟨t + 1, by omega, by rw [hnext]⟩)

end GenLimit.TimeSensitive
