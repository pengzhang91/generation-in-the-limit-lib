import GenLimit.Paper06_NoisyExamples.Nonuniform
import GenLimit.Paper06_NoisyExamples.Separation
import GenLimit.Paper06_NoisyExamples.AlternatePositive
import Mathlib.Data.ENat.Basic
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Numerical noisy closure dimension and optimal uniform thresholds

Raman and Raman, Definition 3.2, the discussion after Theorem 3.3, and the
proof of Lemma 3.8. Thresholds count distinct observations, while the noise
budget counts off-target occurrences. The generator does not receive the budget.
-/

namespace GenLimit.NoisyExamples

/-- Restricting a witness to any smaller cardinality preserves nonbottom
finite closure. Removing observations enlarges the version space. -/
theorem NoisyClosureWitnessAt.downward {H : GenLimit.Generic.LanguageClass α}
    {n k d : ℕ} (hw : NoisyClosureWitnessAt H n k) (hd : d ≤ k) :
    NoisyClosureWitnessAt H n d := by
  classical
  obtain ⟨T, rfl, hv, hc⟩ := hw
  obtain ⟨S, hST, hcard⟩ := Finset.exists_subset_card_eq hd
  have hsub : noisyVersionSpace H T n ⊆ noisyVersionSpace H S n := by
    intro L hL
    have hneg : negativePart S L ⊆ negativePart T L :=
      Finset.filter_subset_filter _ hST
    have hbad := (Finset.card_le_card hneg).trans (negativePart_card_le_of_mem_noisyVersionSpace hL)
    have hsplit := S.filter_card_add_filter_neg_card_eq_card (fun x ↦ x ∈ L)
    exact ⟨hL.1, by simpa only [positivePart, negativePart] using
      (hsplit ▸ Nat.add_le_add_left hbad (positivePart S L).card)⟩
  exact ⟨S, hcard, hv.mono hsub, hc.subset fun _ hx L hL ↦ hx L (hsub hL)⟩

/-- Definition 3.2. A bounded witness spectrum has a least natural upper
bound (zero if empty). An unbounded spectrum has value infinity. -/
noncomputable def noisyClosureDimension (H : GenLimit.Generic.LanguageClass α)
    (n : ℕ) : WithTop ℕ := by
  classical
  exact if h : FiniteNoisyClosureDimensionAt H n then (Nat.find h : ℕ) else ⊤

theorem noisyClosureDimension_eq_bound {H : GenLimit.Generic.LanguageClass α}
    (hdim : ∀ n, FiniteNoisyClosureDimensionAt H n) (n : ℕ) :
    noisyClosureDimension H n = (noisyClosureBound H hdim n : WithTop ℕ) := by
  classical
  simp [noisyClosureDimension, noisyClosureBound, hdim n]

theorem noisyClosureDimension_lt_top_iff {H : GenLimit.Generic.LanguageClass α} {n : ℕ} :
    noisyClosureDimension H n < ⊤ ↔ FiniteNoisyClosureDimensionAt H n := by
  classical
  by_cases h : FiniteNoisyClosureDimensionAt H n <;> simp [noisyClosureDimension, h]

theorem noisyClosureDimension_eq_top_iff {H : GenLimit.Generic.LanguageClass α} {n : ℕ} :
    noisyClosureDimension H n = ⊤ ↔ InfiniteNoisyClosureDimensionAt H n := by
  rw [← not_lt_top_iff, noisyClosureDimension_lt_top_iff]
  constructor
  · intro h d
    obtain ⟨k, hdk, hw⟩ := arbitrarily_large_witness_of_not_finiteNoisyClosureDimensionAt h d
    exact hw.downward hdk.le
  · rintro hall ⟨d, hd⟩
    exact hd (d + 1) (Nat.lt_succ_self d) (hall _)

theorem noisyClosureDimension_le_iff {H : GenLimit.Generic.LanguageClass α} {n d : ℕ} :
    noisyClosureDimension H n ≤ (d : WithTop ℕ) ↔
      ∀ k, NoisyClosureWitnessAt H n k → k ≤ d := by
  classical
  constructor
  · intro hle k hw
    have hf := noisyClosureDimension_lt_top_iff.mp
      (hle.trans_lt (WithTop.coe_lt_top d))
    have hfind : Nat.find hf ≤ d := WithTop.coe_le_coe.mp (by
      simpa [noisyClosureDimension, hf] using hle)
    exact (Nat.le_of_not_gt fun hk ↦ Nat.find_spec hf k hk hw).trans hfind
  · intro h
    have hb : ∀ k, d < k → ¬NoisyClosureWitnessAt H n k :=
      fun k hk hw ↦ hk.not_ge (h k hw)
    have hf : FiniteNoisyClosureDimensionAt H n := ⟨d, hb⟩
    simpa [noisyClosureDimension, hf] using WithTop.coe_le_coe.mpr (Nat.find_min' hf hb)

theorem noisyClosureDimension_eq_zero_iff {H : GenLimit.Generic.LanguageClass α} {n : ℕ} :
    noisyClosureDimension H n = 0 ↔ ¬ NoisyClosureWitnessAt H n 1 := by
  change noisyClosureDimension H n = (⊥ : WithTop ℕ) ↔ _
  rw [← le_bot_iff]
  change noisyClosureDimension H n ≤ ((0 : ℕ) : WithTop ℕ) ↔ _
  rw [noisyClosureDimension_le_iff]
  constructor
  · intro h hw
    exact Nat.not_succ_le_zero 0 (h 1 hw)
  · intro h k hw
    by_contra! hk
    exact h (hw.downward hk)

theorem noisyClosureDimension_eq_succ_iff {H : GenLimit.Generic.LanguageClass α}
    {n d : ℕ} :
    noisyClosureDimension H n = ((d + 1 : ℕ) : WithTop ℕ) ↔
      NoisyClosureWitnessAt H n (d + 1) ∧ ¬ NoisyClosureWitnessAt H n (d + 2) := by
  constructor
  · intro heq
    constructor
    · by_contra hn
      have hle : noisyClosureDimension H n ≤ (d : WithTop ℕ) :=
        noisyClosureDimension_le_iff.mpr fun k hw ↦
          Nat.le_of_not_gt fun hk ↦ hn (hw.downward hk)
      rw [heq] at hle
      exact (Nat.lt_succ_self d).not_ge (WithTop.coe_le_coe.mp hle)
    · intro hw
      have hle := noisyClosureDimension_le_iff.mp heq.le _ hw
      omega
  · rintro ⟨hw, hn⟩
    have hb : noisyClosureDimension H n ≤ ((d + 1 : ℕ) : WithTop ℕ) :=
      noisyClosureDimension_le_iff.mpr fun k hk ↦
        Nat.le_of_not_gt fun hlt ↦ hn (hk.downward hlt)
    have hf := noisyClosureDimension_lt_top_iff.mp
      (hb.trans_lt (WithTop.coe_lt_top _))
    classical
    have heq : noisyClosureDimension H n = (Nat.find hf : WithTop ℕ) := by
      simp [noisyClosureDimension, hf]
    exact le_antisymm hb (heq ▸ WithTop.coe_le_coe.mpr
      (noisyClosureDimension_le_iff.mp heq.le _ hw))

/-- The numerical form of the bounded-excess condition in Theorem C.3. -/
theorem boundedNoisyClosureExcess_iff_dimension_le {H : GenLimit.Generic.LanguageClass α} :
    BoundedNoisyClosureExcess H ↔
      ∃ B : ℕ, ∀ n, noisyClosureDimension H n ≤ ((n + B : ℕ) : WithTop ℕ) := by
  simp only [BoundedNoisyClosureExcess, noisyClosureDimension_le_iff]

/-- Theorem C.3 with the supremum taken in the extended naturals. -/
theorem theorem_C_3_numerical [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : GenLimit.Generic.UUS H) :
    AlternateUniformNoiseIndependentGeneratable H ↔
      (⨆ n : ℕ, noisyClosureDimension H n - (n : WithTop ℕ)) < ⊤ := by
  rw [theorem_C_3 hUUS, boundedNoisyClosureExcess_iff_dimension_le]
  constructor
  · rintro ⟨B, hB⟩
    apply lt_of_le_of_lt _ (WithTop.coe_lt_top B)
    exact iSup_le fun n ↦ tsub_le_iff_right.mpr (by simpa [add_comm] using hB n)
  · intro h
    obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.mp h.ne
    refine ⟨B, fun n ↦ ?_⟩
    have hle := le_iSup (fun m : ℕ ↦ noisyClosureDimension H m - (m : WithTop ℕ)) n
    rw [← hB] at hle
    simpa [add_comm] using tsub_le_iff_right.mp hle

/-- No threshold (including zero) at or below the size of a witness works. -/
theorem witness_lt_uniformNoisyThreshold {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) {gen : GenLimit.Generic.Generator α} {n d k : ℕ}
    (hd : UniformNoisyThreshold gen H n d) (hw : NoisyClosureWitnessAt H n k) : k < d := by
  by_contra! hdk
  obtain ⟨L, hL, stream, hnoise, t, ht, s, hts, hfail⟩ :=
    noisyClosureWitness_defeats_threshold hUUS hw hdk gen
  exact hfail (hd L hL stream hnoise t ht s hts)

/-- Both thresholds printed in the paper work simultaneously for every noise
level with one generator. The first bound implies the larger Appendix E bound. -/
theorem uniformNoisyThresholds_of_finite_dimensions [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} (hdim : ∀ n, FiniteNoisyClosureDimensionAt H n) :
    ∃ gen : GenLimit.Generic.Generator α, ∀ n d : ℕ,
      noisyClosureDimension H n = (d : WithTop ℕ) →
      UniformNoisyThreshold gen H n (d + 1) ∧ UniformNoisyThreshold gen H n (max (d + 1) n) := by
  refine ⟨noisyClosureStrategy H hdim, fun n d heq ↦ ?_⟩
  rw [noisyClosureDimension_eq_bound hdim] at heq
  have hd : noisyClosureBound H hdim n = d := WithTop.coe_inj.mp heq
  exact ⟨noisyClosureStrategy_threshold hdim (Nat.lt_succ_of_le hd.le),
    noisyClosureStrategy_threshold hdim ((Nat.lt_succ_of_le hd.le).trans_le (le_max_left _ _))⟩

/-- The optimum ranges over generators satisfying Definition 2.5 at every
budget; the threshold is evaluated at the specified budget. -/
noncomputable def optimalNoisyThreshold (H : GenLimit.Generic.LanguageClass α)
    (hg : UniformNoiseDependentGeneratable H) (n : ℕ) : ℕ := by
  classical
  have hex : ∃ d, ∃ gen, IsUniformNoiseDependentGenerator gen H ∧ UniformNoisyThreshold gen H n d := by
    obtain ⟨gen, hgen⟩ := hg
    obtain ⟨d, hd⟩ := hgen n
    exact ⟨d, gen, hgen, hd⟩
  exact Nat.find hex

theorem optimalNoisyThreshold_isLeast {H : GenLimit.Generic.LanguageClass α}
    (hg : UniformNoiseDependentGeneratable H) (n : ℕ) :
    IsLeast {d | ∃ gen, IsUniformNoiseDependentGenerator gen H ∧ UniformNoisyThreshold gen H n d}
      (optimalNoisyThreshold H hg n) := by
  classical
  unfold optimalNoisyThreshold
  exact ⟨Nat.find_spec _, fun _ hd ↦ Nat.find_min' _ hd⟩

/-- For finite dimension `d`, the optimum is at most `d+1` and at least
`d`. A positive `d` is attained by a witness, forcing the optimum to equal
`d+1`. At dimension zero the library also admits threshold zero. -/
theorem optimalNoisyThreshold_bounds [Nonempty α] {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) (hg : UniformNoiseDependentGeneratable H)
    {n d : ℕ} (hNC : noisyClosureDimension H n = (d : WithTop ℕ)) :
    d ≤ optimalNoisyThreshold H hg n ∧ optimalNoisyThreshold H hg n ≤ d + 1 ∧
      (0 < d → optimalNoisyThreshold H hg n = d + 1) := by
  have hdim := uniform_noiseDependent_implies_finite_noisyClosureDimensions hUUS hg
  obtain ⟨gen, hgen⟩ := uniformNoisyThresholds_of_finite_dimensions hdim
  have hglobal : IsUniformNoiseDependentGenerator gen H := fun k ↦
    ⟨_, (hgen k _ (noisyClosureDimension_eq_bound hdim k)).1⟩
  have hleast := optimalNoisyThreshold_isLeast hg n
  have hupper := hleast.2 ⟨gen, hglobal, (hgen n d hNC).1⟩
  obtain ⟨other, _, hgood⟩ := hleast.1
  cases d with
  | zero => exact ⟨Nat.zero_le _, hupper, by omega⟩
  | succ k =>
    have hlt := witness_lt_uniformNoisyThreshold hUUS hgood
      (noisyClosureDimension_eq_succ_iff.mp hNC).1
    exact ⟨hlt.le, hupper, fun _ ↦ le_antisymm hupper hlt⟩

/-- With the paper's positive threshold convention the exact optimum is
`d+1`, including the case of dimension zero. -/
theorem optimal_positive_noisyThreshold [Nonempty α] {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) (hg : UniformNoiseDependentGeneratable H)
    {n d : ℕ} (hNC : noisyClosureDimension H n = (d : WithTop ℕ)) :
    IsLeast {k : ℕ | 0 < k ∧ ∃ gen, IsUniformNoiseDependentGenerator gen H ∧
      UniformNoisyThreshold gen H n k} (d + 1) := by
  have hdim := uniform_noiseDependent_implies_finite_noisyClosureDimensions hUUS hg
  obtain ⟨gen, hgen⟩ := uniformNoisyThresholds_of_finite_dimensions hdim
  refine ⟨⟨Nat.zero_lt_succ _, gen, fun m ↦
    ⟨_, (hgen m _ (noisyClosureDimension_eq_bound hdim m)).1⟩, (hgen n d hNC).1⟩, ?_⟩
  rintro k ⟨hk, other, _, hother⟩
  cases d with
  | zero => exact hk
  | succ j =>
    exact witness_lt_uniformNoisyThreshold hUUS hother (noisyClosureDimension_eq_succ_iff.mp hNC).1

/-- A single observation is compatible with every target at any positive
noise allowance. If the dimension is zero, the whole nonempty class then
has infinite intersection and can also generate at round zero. -/
theorem optimalNoisyThreshold_zero_of_positive_noise [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} (hg : UniformNoiseDependentGeneratable H)
    {n : ℕ} (hn : 0 < n) (hNC : noisyClosureDimension H n = 0) :
    optimalNoisyThreshold H hg n = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply (optimalNoisyThreshold_isLeast hg n).2
  by_cases hH : H.Nonempty
  · let x : α := Classical.choice inferInstance
    have hVS : noisyVersionSpace H {x} n = H := by
      ext L
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by
        rw [Finset.card_singleton]
        omega⟩⟩
    have hcore : noisyCommonCore H {x} n = commonIntersection H := by
      simp only [noisyCommonCore, hVS, commonIntersection, GenLimit.Support.classIntersection]
    have hinf : (commonIntersection H).Infinite := by
      intro hfin
      exact noisyClosureDimension_eq_zero_iff.mp hNC
        ⟨{x}, Finset.card_singleton _, by rwa [hVS], by rwa [hcore]⟩
    have hzero (m : ℕ) : UniformNoisyThreshold (commonIntersectionGenerator H hinf) H m 0 := by
      intro L hL stream _ t _ s _
      have hout := commonIntersectionGenerator_spec hinf (fun i : Fin s ↦ stream i)
      rw [GenLimit.Generic.sequenceSample_prefix] at hout
      exact ⟨commonIntersection_subset_of_mem hL hout.1, hout.2⟩
    exact ⟨_, fun m ↦ ⟨0, hzero m⟩, hzero n⟩
  · obtain ⟨gen, hgen⟩ := hg
    exact ⟨gen, hgen, fun L hL ↦ (hH ⟨L, hL⟩).elim⟩

/-- Theorem 3.3's asymptotic assertion along families of classes and noise
budgets. Constants 1 and 2 work, including dimension zero at positive noise.
At zero noise the same statement applies on the positive-dimension range. -/
theorem optimalNoisyThreshold_isTheta {ι : Type*} [Nonempty α]
    (l : Filter ι) (H : ι → GenLimit.Generic.LanguageClass α) (n d : ι → ℕ)
    (hUUS : ∀ i, GenLimit.Generic.UUS (H i)) (hg : ∀ i, UniformNoiseDependentGeneratable (H i))
    (hd : ∀ i, noisyClosureDimension (H i) (n i) = (d i : WithTop ℕ))
    (hpos : ∀ᶠ i in l, 0 < d i ∨ 0 < n i) :
    Asymptotics.IsTheta l (fun i ↦ (optimalNoisyThreshold (H i) (hg i) (n i) : ℝ))
      (fun i ↦ (d i : ℝ)) := by
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨2, hpos.mono fun i hi ↦ ?_⟩
    simp only [Real.norm_natCast]
    have hupper := (optimalNoisyThreshold_bounds (hUUS i) (hg i) (hd i)).2.1
    by_cases hzero : d i = 0
    · have hn : 0 < n i := hi.resolve_left (by omega)
      have hNC : noisyClosureDimension (H i) (n i) = 0 := by simpa [hzero] using hd i
      simp [hzero, optimalNoisyThreshold_zero_of_positive_noise (hg i) hn hNC]
    · exact_mod_cast (show optimalNoisyThreshold (H i) (hg i) (n i) ≤ 2 * d i by omega)
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, Filter.Eventually.of_forall fun i ↦ ?_⟩
    simp only [Real.norm_natCast, one_mul]
    exact_mod_cast (optimalNoisyThreshold_bounds (hUUS i) (hg i) (hd i)).1

/-- Lemma 3.8's threshold subclasses, with their strict dimension bound at
every one-based component index. -/
theorem lemma_3_8_quantitative {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) {gen : GenLimit.Generic.Generator α}
    (hg : IsNonuniformNoiseDependentGenerator gen H) (n : ℕ) :
    GenLimit.Generic.IsNondecreasingCover H (fun j ↦ thresholdSubclass gen H n (j + 1)) ∧
      ∀ j : ℕ, noisyClosureDimension (thresholdSubclass gen H n (j + 1)) n <
        ((j + 1 : ℕ) : WithTop ℕ) := by
  refine ⟨thresholdSubclass_cover hg n, fun j ↦ ?_⟩
  apply lt_of_le_of_lt _ (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self j))
  apply noisyClosureDimension_le_iff.mpr
  intro k hw
  exact Nat.le_of_lt_succ (witness_lt_uniformNoisyThreshold (fun L hL ↦ hUUS L hL.1)
    (thresholdSubclass_uniform gen H n (j + 1)) hw)

end GenLimit.NoisyExamples
