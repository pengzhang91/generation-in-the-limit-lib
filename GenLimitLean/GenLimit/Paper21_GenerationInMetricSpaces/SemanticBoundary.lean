import GenLimit.Paper21_GenerationInMetricSpaces.DiscreteReduction

/-!
# Reachable thresholds and the raw uniform-generation boundary

`IsUniformGeneratorAt` is deliberately a conditional guarantee: after a
finite sample reaches the stated covering-number threshold, every later
output must be correct.  The predicate itself does not say that the threshold
will ever be reached.

This module exposes that missing liveness condition as
`UniformThresholdReachableAt`, proves the general bridge from a reachable
uniform guarantee to limit generation, and records a small discrete
regression example where the raw condition is vacuous.
-/

namespace GenLimit.MetricSpaces

open GenLimit.Generic

/-- The uniform covering-number threshold is eventually attained on every
metric presentation in the class. -/
def UniformThresholdReachableAt
    (ρ : Distance α) (ε : ℝ)
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ L, L ∈ H →
    ∀ stream : GenLimit.Generic.Stream α,
      MetricPresentation ρ ε stream L →
        ∃ t, CoveringNumberAtLeast ρ ε
          (GenLimit.Generic.sample stream t : Set α) d

/-- A uniform correctness guarantee becomes genuine limit generation once
its threshold is known to be reachable on every metric presentation. -/
theorem isLimitGeneratorAt_of_uniform_of_thresholdReachable
    {ρ : Distance α} {ε ε' : ℝ}
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ}
    (hUniform : IsUniformGeneratorAt ρ ε ε' gen H d)
    (hReachable : UniformThresholdReachableAt ρ ε H d) :
    IsLimitGeneratorAt ρ ε ε' gen H := by
  intro L hLH stream hPresentation
  obtain ⟨t, hTrigger⟩ := hReachable L hLH stream hPresentation
  exact ⟨t, hUniform L hLH stream hPresentation.1 t hTrigger⟩

/-- A library-safe existence predicate that couples the source-facing
uniform guarantee with the liveness condition needed to trigger it. -/
def NonvacuouslyUniformlyGeneratableAt
    (ρ : Distance α) (ε ε' : ℝ)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, ∃ d : ℕ,
    IsUniformGeneratorAt ρ ε ε' gen H d ∧
      UniformThresholdReachableAt ρ ε H d

/-- Non-vacuous uniform generation implies generation in the limit. -/
theorem nonvacuouslyUniformlyGeneratableAt_implies_generatableInLimitAt
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (h : NonvacuouslyUniformlyGeneratableAt ρ ε ε' H) :
    GeneratableInLimitAt ρ ε ε' H := by
  obtain ⟨gen, d, hUniform, hReachable⟩ := h
  exact ⟨gen,
    isLimitGeneratorAt_of_uniform_of_thresholdReachable
      hUniform hReachable⟩

/-- If a proposed threshold is impossible on every in-class stream, the raw
uniform predicate holds for every generator by vacuity. -/
theorem isUniformGeneratorAt_of_threshold_unreachable
    {ρ : Distance α} {ε ε' : ℝ}
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ}
    (hUnreachable :
      ∀ L, L ∈ H →
        ∀ stream : GenLimit.Generic.Stream α,
          GenLimit.Generic.StreamIn stream L →
            ∀ t, ¬ CoveringNumberAtLeast ρ ε
              (GenLimit.Generic.sample stream t : Set α) d) :
    IsUniformGeneratorAt ρ ε ε' gen H d := by
  intro L hLH stream hStream t hTrigger
  exact False.elim (hUnreachable L hLH stream hStream t hTrigger)

namespace UniformThresholdBoundary

/-- A one-point target used to expose an unreachable threshold. -/
def singletonTarget : GenLimit.Generic.Language ℕ := {0}

/-- The class containing only the one-point target. -/
def singletonClass : GenLimit.Generic.LanguageClass ℕ := {singletonTarget}

/-- A deliberately incorrect generator for the one-point target. -/
def constantOneGenerator : GenLimit.Generic.Generator ℕ :=
  fun _t _history => 1

/-- Every finite sample from a stream in the one-point target has cardinality
at most one. -/
theorem sample_card_le_one_of_streamIn_singletonTarget
    {stream : GenLimit.Generic.Stream ℕ}
    (hStream : GenLimit.Generic.StreamIn stream singletonTarget)
    (t : ℕ) :
    (GenLimit.Generic.sample stream t).card ≤ 1 := by
  classical
  have hSubset :
      GenLimit.Generic.sample stream t ⊆ ({0} : Finset ℕ) := by
    intro x hx
    obtain ⟨s, _hst, hsx⟩ := GenLimit.Generic.mem_sample_iff.mp hx
    have hxTarget : x ∈ singletonTarget :=
      hStream ⟨s, hsx⟩
    simpa [singletonTarget] using hxTarget
  simpa using Finset.card_le_card hSubset

/-- The threshold two is unreachable for streams in the one-point target at
the discrete half-unit scale. -/
theorem threshold_two_unreachable
    {stream : GenLimit.Generic.Stream ℕ}
    (hStream : GenLimit.Generic.StreamIn stream singletonTarget)
    (t : ℕ) :
    ¬ CoveringNumberAtLeast
        (discreteDistance (α := ℕ)) (1 / 2 : ℝ)
        (GenLimit.Generic.sample stream t : Set ℕ) 2 := by
  rw [discrete_coveringNumberAtLeast_finset_iff
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)]
  have hCard :=
    sample_card_le_one_of_streamIn_singletonTarget hStream t
  omega

/-- Semantic regression: because threshold two can never be reached, even a
generator that always returns the off-target value `1` satisfies the raw
uniform predicate for the singleton class. -/
theorem constantOneGenerator_isUniformGeneratorAt_two :
    IsUniformGeneratorAt
      (discreteDistance (α := ℕ)) (1 / 2 : ℝ) (1 / 2 : ℝ)
      constantOneGenerator singletonClass 2 := by
  apply isUniformGeneratorAt_of_threshold_unreachable
  intro L hLH stream hStream t
  have hL : L = singletonTarget := by
    simpa [singletonClass] using hLH
  subst L
  exact threshold_two_unreachable hStream t

/-- The same deliberately incorrect generator is not a limit generator: on
the constant presentation of `{0}`, it always outputs the off-target value
`1`. -/
theorem constantOneGenerator_not_isLimitGeneratorAt :
    ¬ IsLimitGeneratorAt
      (discreteDistance (α := ℕ)) (1 / 2 : ℝ) (1 / 2 : ℝ)
      constantOneGenerator singletonClass := by
  intro hLimit
  let stream : GenLimit.Generic.Stream ℕ := fun _ => 0
  have hPresents : GenLimit.Generic.Presents stream singletonTarget := by
    ext x
    simp [stream, singletonTarget]
  have hMetricPresentation :
      MetricPresentation (discreteDistance (α := ℕ)) (1 / 2 : ℝ)
        stream singletonTarget :=
    (discrete_metricPresentation_iff
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).2 hPresents
  obtain ⟨T, hT⟩ :=
    hLimit singletonTarget (by simp [singletonClass])
      stream hMetricPresentation
  have hValid := (hT T le_rfl).1
  simp [constantOneGenerator, GenLimit.Generic.output,
    singletonTarget] at hValid

/-- The raw uniform predicate therefore does not imply the corresponding
limit predicate without a threshold-reachability hypothesis. -/
theorem raw_uniform_does_not_imply_limit :
    IsUniformGeneratorAt
        (discreteDistance (α := ℕ)) (1 / 2 : ℝ) (1 / 2 : ℝ)
        constantOneGenerator singletonClass 2 ∧
      ¬ IsLimitGeneratorAt
        (discreteDistance (α := ℕ)) (1 / 2 : ℝ) (1 / 2 : ℝ)
        constantOneGenerator singletonClass :=
  ⟨constantOneGenerator_isUniformGeneratorAt_two,
    constantOneGenerator_not_isLimitGeneratorAt⟩

end UniformThresholdBoundary

end GenLimit.MetricSpaces
