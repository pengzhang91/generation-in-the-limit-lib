import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TotalizedGCGProgress
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TheoremFour
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TurnTakingUpperBound
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.AdaptiveUpperBound

/-!
# The repaired GCG theorem

This module assembles the concrete queue progress theorem with P07's
`Accurate` contract.  It proves the two obligations omitted from the printed
Appendix-E proof: eventual consistency of the repaired run and cofinal target
checkpoints.  The latter gives instance-level upper timely density at least
one half via `theorem_4_density_endgame`.  The concrete sparse adaptive
presentation imported below supplies the matching upper bound and hence the
unconditional repaired equality theorem.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures

theorem totalizedGCGRun_stage_step_le
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream (t + 1)).stage ≤
      (totalizedGCGRun F stream t).stage + 1 := by
  simp only [totalizedGCGRun_succ, totalizedGCGStep]
  split <;> omega

theorem totalizedGCG_crossed_of_stage_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    {m t : ℕ}
    (hstage : (totalizedGCGRun F stream t).stage = m)
    (hnext : (totalizedGCGRun F stream (t + 1)).stage = m + 1) :
    gcgThreshold (m + 1) ≤
      timelyDensity (totalizedGCGOutput F stream)
        (F.order (F.guess stream (m + 1))).enumeration id (t + 1) := by
  have hcondition :
      (totalizedGCGRun F stream t).stage < t ∧
      gcgThreshold ((totalizedGCGRun F stream t).stage + 1) ≤
        timelyDensity
          (outputHistoryStream
            ((totalizedGCGRun F stream t).outputs ++
              [totalizedRoundOutput F stream t
                (totalizedGCGRun F stream t)]))
          (F.order
            (totalizedRoundActive F stream t
              (totalizedGCGRun F stream t))).enumeration id (t + 1) := by
    by_contra hnot
    have hsame :
        (totalizedGCGRun F stream (t + 1)).stage =
          (totalizedGCGRun F stream t).stage := by
      rw [totalizedGCGRun_succ]
      simp only [totalizedGCGStep]
      rw [if_neg hnot]
    rw [hsame, hstage] at hnext
    omega
  have hcross := hcondition.2
  change
    gcgThreshold ((totalizedGCGRun F stream t).stage + 1) ≤
      timelyDensity
        (outputHistoryStream
          ((totalizedGCGRun F stream t).outputs ++
            [totalizedGCGOutput F stream t]))
        (F.order
          (totalizedRoundActive F stream t
            (totalizedGCGRun F stream t))).enumeration id (t + 1) at hcross
  rw [← totalizedGCGRun_outputs_succ,
    timelyDensity_outputHistory_totalized] at hcross
  simpa [totalizedRoundActive, hstage] using hcross

/-- Every queued stage has a concrete transition round and a certified
threshold checkpoint. -/
theorem totalizedGCG_exists_stage_transition
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (m : ℕ) :
    ∃ t,
      (totalizedGCGRun F stream t).stage = m ∧
      (totalizedGCGRun F stream (t + 1)).stage = m + 1 ∧
      gcgThreshold (m + 1) ≤
        timelyDensity (totalizedGCGOutput F stream)
          (F.order (F.guess stream (m + 1))).enumeration id (t + 1) := by
  obtain ⟨T, hT⟩ := totalizedGCG_stage_eventually_ge F stream (m + 1)
  have hexists : ∃ q,
      m + 1 ≤ (totalizedGCGRun F stream q).stage :=
    ⟨T, hT T le_rfl⟩
  let q := Nat.find hexists
  have hqReach : m + 1 ≤ (totalizedGCGRun F stream q).stage :=
    Nat.find_spec hexists
  have hqPos : 0 < q := by
    by_contra hnot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hnot
    simp [q, hq0, TotalizedGCGState.initial] at hqReach
  let t := q - 1
  have htSucc : t + 1 = q := by
    dsimp [t]
    omega
  have htNotReach :
      ¬m + 1 ≤ (totalizedGCGRun F stream t).stage := by
    intro htReach
    have hqt : q ≤ t := Nat.find_min' hexists htReach
    dsimp [t] at hqt
    omega
  have hstep := totalizedGCGRun_stage_step_le F stream t
  have hqReach' :
      m + 1 ≤ (totalizedGCGRun F stream (t + 1)).stage := by
    rw [htSucc]
    exact hqReach
  have hstage : (totalizedGCGRun F stream t).stage = m := by
    have hupper : (totalizedGCGRun F stream t).stage ≤ m := by
      omega
    omega
  have hnext : (totalizedGCGRun F stream (t + 1)).stage = m + 1 := by
    omega
  exact ⟨t, hstage, hnext,
    totalizedGCG_crossed_of_stage_succ F stream hstage hnext⟩

/-- P07's eventual index validity and unbounded queue progress imply that
all sufficiently late repaired-GCG outputs lie in the target language. -/
theorem totalizedGCG_eventually_consistent
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hvalid : IndexValidInLimit F.language stream z) :
    ∃ T, ∀ t, T ≤ t →
      totalizedGCGOutput F stream t ∈ F.language z := by
  obtain ⟨A, hA⟩ := hvalid
  obtain ⟨T, hT⟩ := totalizedGCG_stage_eventually_ge F stream A
  refine ⟨T, fun t ht => ?_⟩
  have hstageA : A ≤ (totalizedGCGRun F stream t).stage := hT t ht
  exact hA _ (by omega)
    (totalizedGCGOutput_mem_active F stream t)

/-- Infinitely-often accurate queued guesses yield cofinal density
checkpoints for the true target order. -/
theorem totalizedGCG_target_cofinal_checkpoints
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (z : ℕ)
    (haccurate : ∀ q, ∃ r, q ≤ r ∧
      AccurateAt F.language stream z r) :
    ∀ m N : ℕ, ∃ i : ℕ,
      N ≤ i ∧
      gcgThreshold m ≤
        timelyDensity (totalizedGCGOutput F stream)
          (F.order z).enumeration id i := by
  intro m N
  obtain ⟨r, hrLarge, hrAccurate⟩ :=
    haccurate (max 1 (max m N))
  have hrPos : 0 < r := by
    have : 1 ≤ r := (Nat.le_max_left 1 (max m N)).trans hrLarge
    omega
  let s := r - 1
  have hsSucc : s + 1 = r := by
    dsimp [s]
    omega
  obtain ⟨t, hstage, hnext, hcross⟩ :=
    totalizedGCG_exists_stage_transition F stream s
  have hactiveOrder :
      (F.order (F.guess stream (s + 1))).enumeration =
        (F.order z).enumeration := by
    apply F.order_eq_of_language_eq
    simpa [AccurateAt, hsSucc] using hrAccurate
  refine ⟨t + 1, ?_, ?_⟩
  · have hstageLe := totalizedGCGRun_stage_le_time F stream t
    have hrLe : r ≤ t + 1 := by
      rw [← hsSucc]
      omega
    exact ((Nat.le_max_right m N).trans
      (Nat.le_max_right 1 (max m N))).trans (hrLarge.trans hrLe)
  · have hmR : m ≤ r :=
      (Nat.le_max_left m N).trans
        ((Nat.le_max_right 1 (max m N)).trans hrLarge)
    exact (gcgThreshold_monotone hmR).trans (by
      rw [← hsSucc]
      rw [hactiveOrder] at hcross
      exact hcross)

/-- Repaired Algorithm 2: eventual consistency and the full constructive
`>= 1/2` half of Theorem 4 / Appendix Theorem 12. -/
theorem totalizedGCG_theorem_4_lower
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (F.language z))
    (hfirst : FirstOccurrence F.language z) :
    (∃ T, ∀ t, T ≤ t →
      totalizedGCGOutput F stream t ∈ F.language z) ∧
    (1 / 2 : ℝ) ≤
      upperTimelyDensity (totalizedGCGOutput F stream)
        (F.order z).enumeration id := by
  obtain ⟨hvalid, haccurate⟩ :=
    appendix_E_accurate_oracle_from_paper07 hP hfirst
  refine ⟨totalizedGCG_eventually_consistent F stream z hvalid, ?_⟩
  exact theorem_4_density_endgame_of_cofinal_checkpoints _ _
    (totalizedGCG_target_cofinal_checkpoints F stream z haccurate)

/-- Exact equality once an operational Kleinberg--Wei adversary has supplied
the finite turn-taking bounds and a vanishing catch-up budget.  Keeping these
premises visible prevents the source's omitted optimality argument from being
mistaken for a consequence of the constructive lower bound. -/
theorem totalizedGCG_theorem_4_eq_of_turnTaking
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (F.language z))
    (hfirst : FirstOccurrence F.language z)
    (exceptions : ℕ → ℕ)
    (hfinite : ∀ᶠ i in Filter.atTop,
      2 * (timelyElements (totalizedGCGOutput F stream)
        (F.order z).enumeration id i).card ≤ i + 2 * exceptions i)
    (hvanishing : Filter.Tendsto (catchupRatio exceptions)
      Filter.atTop (nhds 0)) :
    (∃ T, ∀ t, T ≤ t →
      totalizedGCGOutput F stream t ∈ F.language z) ∧
    upperTimelyDensity (totalizedGCGOutput F stream)
      (F.order z).enumeration id = (1 / 2 : ℝ) := by
  obtain ⟨hconsistent, hlower⟩ :=
    totalizedGCG_theorem_4_lower F stream z hP hfirst
  refine ⟨hconsistent, le_antisymm ?_ hlower⟩
  exact upperTimelyDensity_le_half_of_turnTaking _ _ exceptions
    hfinite hvanishing

/-- The concrete sparse adaptive presentation realizes the upper endpoint,
so the repaired GCG has exact instance-level timely upper density `1/2` on
this exact presentation. -/
theorem totalizedGCG_theorem_4_adaptive_witness
    (F : CanonicallyOrderedFamily) (z : ℕ)
    (hfirst : FirstOccurrence F.language z) :
    Presents (adaptivePresentation F (F.order z)) (F.language z) ∧
    (∃ T, ∀ t, T ≤ t →
      totalizedGCGOutput F (adaptivePresentation F (F.order z)) t ∈
        F.language z) ∧
    upperTimelyDensity
        (totalizedGCGOutput F (adaptivePresentation F (F.order z)))
        (F.order z).enumeration id = (1 / 2 : ℝ) := by
  have hPOrder := adaptivePresentation_presents F (F.order z)
  have hP : Presents (adaptivePresentation F (F.order z))
      (F.language z) := by
    simpa only [F.carrier_eq] using hPOrder
  obtain ⟨hconsistent, hlower⟩ :=
    totalizedGCG_theorem_4_lower F
      (adaptivePresentation F (F.order z)) z hP hfirst
  have hout : adaptiveGCGOutput F (F.order z) =
      totalizedGCGOutput F (adaptivePresentation F (F.order z)) := by
    funext t
    exact adaptiveGCGOutput_eq_totalized F (F.order z) t
  have hupper :
      upperTimelyDensity
          (totalizedGCGOutput F (adaptivePresentation F (F.order z)))
          (F.order z).enumeration id ≤ (1 / 2 : ℝ) := by
    rw [← hout]
    exact adaptive_upperTimelyDensity_le_half F (F.order z)
  exact ⟨hP, hconsistent, le_antisymm hupper hlower⟩

/-- Repaired, unconditional Theorem 4 / Appendix Theorem 12 at the explicit
indexed-family interface.

The first conjunct is the constructive guarantee on every exact
presentation.  The second gives a concrete adaptive exact presentation at
which equality is attained.  Together they state that the repaired GCG is
eventually consistent and has worst-case instance-level timely upper density
exactly `1/2`; no turn-taking certificate remains as a premise. -/
theorem totalizedGCG_theorem_4
    (F : CanonicallyOrderedFamily) (z : ℕ)
    (hfirst : FirstOccurrence F.language z) :
    (∀ stream, Presents stream (F.language z) →
      (∃ T, ∀ t, T ≤ t →
        totalizedGCGOutput F stream t ∈ F.language z) ∧
      (1 / 2 : ℝ) ≤
        upperTimelyDensity (totalizedGCGOutput F stream)
          (F.order z).enumeration id) ∧
    ∃ stream,
      Presents stream (F.language z) ∧
      (∃ T, ∀ t, T ≤ t →
        totalizedGCGOutput F stream t ∈ F.language z) ∧
      upperTimelyDensity (totalizedGCGOutput F stream)
        (F.order z).enumeration id = (1 / 2 : ℝ) := by
  constructor
  · intro stream hP
    exact totalizedGCG_theorem_4_lower F stream z hP hfirst
  · exact ⟨adaptivePresentation F (F.order z),
      totalizedGCG_theorem_4_adaptive_witness F z hfirst⟩

end GenLimit.TimeSensitive
