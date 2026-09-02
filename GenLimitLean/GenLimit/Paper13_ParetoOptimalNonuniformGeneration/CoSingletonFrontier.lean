import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.AdmissibleFrontier
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.GlobalInvariant
import GenLimit.Support.Fresh
import GenLimit.Support.Renaming
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Denumerable

/-!
# The complete co-singleton frontier

This module completes Proposition 3.3 of Charikar--Pabbaraju,
*Pareto-optimal Non-uniform Language Generation*,
arXiv:2510.02795v1, pp. 10--11, in the distinct-history semantic model used
throughout the Pareto development.

For the zero-based co-singleton family `L_i = ℕ \ {i}`, a positive time
vector is realizable exactly when every upper level set
`{i | k ≤ time i}` is infinite.  The forward direction is a finite
common-history diagonal.  The reverse direction constructs the paper's
oblivious generator directly: at history size `t`, choose a fresh index
whose requested time is larger than `t`.

Combining this exact frontier with `no_paretoOptimal_positiveAdmissible`
gives the full Pareto-impossibility conclusion.
-/

namespace GenLimit.ParetoGeneration

/-- The co-singleton family, with `ℕ` serving as both language index and
countable universe. -/
def coSingletonFamily (i : Nat) : Set Nat :=
  {x | x ≠ i}

@[simp] theorem mem_coSingletonFamily {i x : Nat} :
    x ∈ coSingletonFamily i ↔ x ≠ i :=
  Iff.rfl

/-- The infinite reservoir available to the oblivious generator at history
size `t`. -/
def coSingletonReservoir (time : TimeVector) (t : Nat) : Set Nat :=
  {i | t < time i}

theorem coSingletonReservoir_infinite
    {time : TimeVector} (htail : TailAdmissible time) (t : Nat) :
    (coSingletonReservoir time t).Infinite := by
  have h := htail (t + 1)
  simpa only [coSingletonReservoir, Set.setOf_mem_eq,
    Nat.add_one_le_iff] using h

/-- The oblivious generator from the sufficiency half of the admissibility
characterization. -/
noncomputable def coSingletonAdmissibleGenerator
    (time : TimeVector) (htail : TailAdmissible time) :
    HistoryGenerator Nat := by
  classical
  exact fun t xs =>
    GenLimit.Support.freshFromInfinite
      (coSingletonReservoir time t)
      (coSingletonReservoir_infinite htail t)
      (GenLimit.Generic.sequenceSample xs)

theorem coSingletonAdmissibleGenerator_spec
    (time : TimeVector) (htail : TailAdmissible time)
    {t : Nat} (xs : Fin t -> Nat) :
    t < time (coSingletonAdmissibleGenerator time htail t xs) ∧
      ∀ k, coSingletonAdmissibleGenerator time htail t xs ≠ xs k := by
  classical
  have hmem :=
    GenLimit.Support.freshFromInfinite_mem
      (coSingletonReservoir time t)
      (coSingletonReservoir_infinite htail t)
      (GenLimit.Generic.sequenceSample xs)
  have hfresh :=
    GenLimit.Support.freshFromInfinite_not_mem
      (coSingletonReservoir time t)
      (coSingletonReservoir_infinite htail t)
      (GenLimit.Generic.sequenceSample xs)
  constructor
  · exact hmem
  · intro k hk
    exact hfresh
      (GenLimit.Generic.mem_sequenceSample_iff.mpr
        ⟨k, hk.symm⟩)

/-- Every positive tail-admissible vector is achieved by the oblivious
co-singleton generator. -/
theorem coSingletonAdmissibleGenerator_achieves
    {time : TimeVector} (htail : TailAdmissible time) :
    AchievesTimeVector
      (coSingletonAdmissibleGenerator time htail)
      coSingletonFamily time := by
  intro i t xs htime _ _
  have hspec :=
    coSingletonAdmissibleGenerator_spec time htail xs
  constructor
  · change coSingletonAdmissibleGenerator time htail t xs ≠ i
    intro hout
    subst i
    exact (Nat.not_lt_of_ge htime) hspec.1
  · exact hspec.2

/-- Sufficiency in the paper's admissibility characterization. -/
theorem positiveAdmissible_coSingleton_realizable
    {time : TimeVector} (htime : time ∈ PositiveAdmissibleVectors) :
    time ∈ RealizableTimeVectors coSingletonFamily :=
  ⟨coSingletonAdmissibleGenerator time htime.2,
    coSingletonAdmissibleGenerator_achieves htime.2,
    htime.1⟩

/-- A finite upper level set can be embedded into one finite common history
large enough to activate every coordinate outside that level set. -/
noncomputable def coSingletonDiagonalSample
    (time : TimeVector) (k : Nat)
    (hfinite : ({i | k ≤ time i} : Set Nat).Finite) : Finset Nat :=
  hfinite.toFinset ∪ Finset.range k

theorem upperLevel_subset_coSingletonDiagonalSample
    (time : TimeVector) (k : Nat)
    (hfinite : ({i | k ≤ time i} : Set Nat).Finite) :
    ({i | k ≤ time i} : Set Nat) ⊆
      coSingletonDiagonalSample time k hfinite := by
  intro i hi
  apply Finset.mem_union_left
  exact hfinite.mem_toFinset.mpr hi

theorem range_subset_coSingletonDiagonalSample
    (time : TimeVector) (k : Nat)
    (hfinite : ({i | k ≤ time i} : Set Nat).Finite) :
    Finset.range k ⊆
      coSingletonDiagonalSample time k hfinite :=
  Finset.subset_union_right

theorem k_le_coSingletonDiagonalSample_card
    (time : TimeVector) (k : Nat)
    (hfinite : ({i | k ≤ time i} : Set Nat).Finite) :
    k ≤ (coSingletonDiagonalSample time k hfinite).card := by
  have hcard := Finset.card_le_card
    (range_subset_coSingletonDiagonalSample time k hfinite)
  simpa using hcard

/-- Necessity in the admissibility characterization.

If one upper level were finite, include that level set in a finite distinct
history.  Novelty forces the generator to output some index outside the
level set; taking that output itself as the co-singleton target then turns
the same output into an error. -/
theorem coSingleton_realizable_tailAdmissible
    {time : TimeVector}
    (htime : time ∈ RealizableTimeVectors coSingletonFamily) :
    TailAdmissible time := by
  obtain ⟨G, hAchieves, -⟩ := htime
  intro k
  by_contra hnotInfinite
  have hfinite :
      ({i | k ≤ time i} : Set Nat).Finite :=
    Set.not_infinite.mp hnotInfinite
  let sample :=
    coSingletonDiagonalSample time k hfinite
  let n := sample.card
  have hk_n : k ≤ n :=
    k_le_coSingletonDiagonalSample_card time k hfinite
  have hsampleFinite :
      (↑sample : Set Nat).Finite :=
    sample.finite_toSet
  have hsampleCard :
      (↑sample : Set Nat).ncard = n := by
    simp [n]
  let xs : Fin n -> Nat :=
    finiteSetHistory (↑sample : Set Nat)
      hsampleFinite n hsampleCard
  have hxsInjective : Function.Injective xs :=
    finiteSetHistory_injective (↑sample : Set Nat)
      hsampleFinite n hsampleCard
  have hxsRange : Set.range xs = (↑sample : Set Nat) :=
    finiteSetHistory_range (↑sample : Set Nat)
      hsampleFinite n hsampleCard
  let auxiliary :=
    GenLimit.Support.freshFromInfinite
      Set.univ Set.infinite_univ sample
  have hauxiliaryNotSample : auxiliary ∉ sample := by
    exact GenLimit.Support.freshFromInfinite_not_mem
      Set.univ Set.infinite_univ sample
  have hauxiliaryTime : time auxiliary ≤ n := by
    have hnotUpper : ¬k ≤ time auxiliary := by
      intro hUpper
      exact hauxiliaryNotSample
        (upperLevel_subset_coSingletonDiagonalSample
          time k hfinite hUpper)
    omega
  have hauxiliaryHistory :
      ∀ q, xs q ∈ coSingletonFamily auxiliary := by
    intro q
    change xs q ≠ auxiliary
    intro hEq
    apply hauxiliaryNotSample
    have hxRange : xs q ∈ Set.range xs :=
      Set.mem_range_self q
    rw [hxsRange] at hxRange
    simpa [hEq] using hxRange
  have hauxiliaryOutput :=
    hAchieves auxiliary n xs hauxiliaryTime
      hxsInjective hauxiliaryHistory
  let target := G n xs
  have htargetNotSample : target ∉ sample := by
    intro htargetSample
    have htargetRange : target ∈ Set.range xs := by
      rw [hxsRange]
      exact htargetSample
    obtain ⟨j, hj⟩ := htargetRange
    exact hauxiliaryOutput.2 j hj.symm
  have hpreTarget : time target ≤ n := by
    have hnotUpper : ¬k ≤ time target := by
      intro hUpper
      exact htargetNotSample
        (upperLevel_subset_coSingletonDiagonalSample
          time k hfinite hUpper)
    omega
  have htargetHistory :
      ∀ q, xs q ∈ coSingletonFamily target := by
    intro q
    change xs q ≠ target
    intro hEq
    apply htargetNotSample
    have hxRange : xs q ∈ Set.range xs :=
      Set.mem_range_self q
    rw [hxsRange] at hxRange
    simpa [hEq] using hxRange
  have hout :=
    hAchieves target n xs hpreTarget
      hxsInjective htargetHistory
  exact hout.1 rfl

/-- The exact feasible frontier asserted in the proof of Proposition 3.3. -/
theorem coSingleton_realizable_iff_positiveAdmissible
    (time : TimeVector) :
    time ∈ RealizableTimeVectors coSingletonFamily ↔
      time ∈ PositiveAdmissibleVectors := by
  constructor
  · intro htime
    exact ⟨htime.choose_spec.2,
      coSingleton_realizable_tailAdmissible htime⟩
  · exact positiveAdmissible_coSingleton_realizable

theorem coSingleton_realizableTimeVectors_eq :
    RealizableTimeVectors coSingletonFamily =
      PositiveAdmissibleVectors := by
  ext time
  exact coSingleton_realizable_iff_positiveAdmissible time

/-- Proposition 3.3: the co-singleton family admits no Pareto-optimal
realizable generation-time vector. -/
theorem proposition_3_3_full :
    ¬∃ time,
      time ∈ RealizableTimeVectors coSingletonFamily ∧
      ParetoOptimal
        (RealizableTimeVectors coSingletonFamily) time := by
  rintro ⟨time, htime, hPareto⟩
  have hAdmissible :
      time ∈ PositiveAdmissibleVectors :=
    (coSingleton_realizable_iff_positiveAdmissible time).mp htime
  apply no_paretoOptimal_positiveAdmissible time hAdmissible
  simpa only [coSingleton_realizableTimeVectors_eq] using hPareto

/-! ## Relabeling to the paper's literal integer universe -/

/-- The same co-singleton family after relabeling the natural-number
universe by an equivalence. -/
def coSingletonFamilyAlong
    (e : Nat ≃ β) (i : Nat) : Set β :=
  {x | x ≠ e i}

/-- Transport a generator from the natural-number co-singleton family
across a universe equivalence. -/
abbrev coSingletonForwardGenerator
    (e : Nat ≃ β) (G : HistoryGenerator Nat) :
    HistoryGenerator β :=
  GenLimit.Support.renameGenerator e G

theorem coSingletonForwardGenerator_achieves
    (e : Nat ≃ β) {G : HistoryGenerator Nat}
    {time : TimeVector}
    (hG : AchievesTimeVector G coSingletonFamily time) :
    AchievesTimeVector (coSingletonForwardGenerator e G)
      (coSingletonFamilyAlong e) time := by
  intro i t xs htime hinjective htarget
  let ys : Fin t -> Nat := fun k => e.symm (xs k)
  have hysInjective : Function.Injective ys := by
    intro j k hjk
    apply hinjective
    simpa [ys] using congrArg e hjk
  have hysTarget : ∀ k, ys k ∈ coSingletonFamily i := by
    intro k
    change e.symm (xs k) ≠ i
    intro hEq
    apply htarget k
    calc
      xs k = e (e.symm (xs k)) := (e.apply_symm_apply _).symm
      _ = e i := congrArg e hEq
  have hout := hG i t ys htime hysInjective hysTarget
  constructor
  · change e (G t ys) ≠ e i
    exact e.injective.ne hout.1
  · intro k hEq
    apply hout.2 k
    apply e.injective
    simpa [coSingletonForwardGenerator, ys] using hEq

/-- Transport in the reverse direction. -/
abbrev coSingletonBackwardGenerator
    (e : Nat ≃ β) (G : HistoryGenerator β) :
    HistoryGenerator Nat :=
  GenLimit.Support.renameGenerator e.symm G

theorem coSingletonBackwardGenerator_achieves
    (e : Nat ≃ β) {G : HistoryGenerator β}
    {time : TimeVector}
    (hG : AchievesTimeVector G (coSingletonFamilyAlong e) time) :
    AchievesTimeVector (coSingletonBackwardGenerator e G)
      coSingletonFamily time := by
  intro i t xs htime hinjective htarget
  let ys : Fin t -> β := fun k => e (xs k)
  have hysInjective : Function.Injective ys :=
    e.injective.comp hinjective
  have hysTarget :
      ∀ k, ys k ∈ coSingletonFamilyAlong e i := by
    intro k
    change e (xs k) ≠ e i
    exact e.injective.ne (htarget k)
  have hout := hG i t ys htime hysInjective hysTarget
  constructor
  · change e.symm (G t ys) ≠ i
    intro hEq
    apply hout.1
    calc
      G t ys = e (e.symm (G t ys)) :=
        (e.apply_symm_apply _).symm
      _ = e i := congrArg e hEq
  · intro k hEq
    apply hout.2 k
    apply e.symm.injective
    simpa [coSingletonBackwardGenerator, ys] using hEq

theorem coSingletonAlong_realizable_iff
    (e : Nat ≃ β) (time : TimeVector) :
    time ∈ RealizableTimeVectors (coSingletonFamilyAlong e) ↔
      time ∈ RealizableTimeVectors coSingletonFamily := by
  constructor
  · rintro ⟨G, hG, hpositive⟩
    exact ⟨coSingletonBackwardGenerator e G,
      coSingletonBackwardGenerator_achieves e hG,
      hpositive⟩
  · rintro ⟨G, hG, hpositive⟩
    exact ⟨coSingletonForwardGenerator e G,
      coSingletonForwardGenerator_achieves e hG,
      hpositive⟩

theorem coSingletonAlong_realizable_iff_positiveAdmissible
    (e : Nat ≃ β) (time : TimeVector) :
    time ∈ RealizableTimeVectors (coSingletonFamilyAlong e) ↔
      time ∈ PositiveAdmissibleVectors := by
  rw [coSingletonAlong_realizable_iff,
    coSingleton_realizable_iff_positiveAdmissible]

/-- A fixed no-repetition enumeration of every integer, used to state the
paper's literal `ℤ \ {e_i}` family. -/
def integerIndexEquiv : Nat ≃ Int :=
  Equiv.intEquivNat.symm

def integerCoSingletonFamily (i : Nat) : Set Int :=
  coSingletonFamilyAlong integerIndexEquiv i

theorem integerCoSingleton_realizable_iff_positiveAdmissible
    (time : TimeVector) :
    time ∈ RealizableTimeVectors integerCoSingletonFamily ↔
      time ∈ PositiveAdmissibleVectors := by
  exact coSingletonAlong_realizable_iff_positiveAdmissible
    integerIndexEquiv time

/-- Proposition 3.3 on the source's literal integer universe. -/
theorem proposition_3_3_integer_full :
    ¬∃ time,
      time ∈ RealizableTimeVectors integerCoSingletonFamily ∧
      ParetoOptimal
        (RealizableTimeVectors integerCoSingletonFamily) time := by
  have hsets :
      RealizableTimeVectors integerCoSingletonFamily =
        PositiveAdmissibleVectors := by
    ext time
    exact integerCoSingleton_realizable_iff_positiveAdmissible time
  rintro ⟨time, htime, hPareto⟩
  have hAdmissible : time ∈ PositiveAdmissibleVectors := by
    simpa only [hsets] using htime
  apply no_paretoOptimal_positiveAdmissible time hAdmissible
  simpa only [hsets] using hPareto

end GenLimit.ParetoGeneration
