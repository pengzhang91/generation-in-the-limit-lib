import GenLimit.Paper09_RepresentativeLanguageGeneration.FinitePartitionCorollaries
import GenLimit.Paper02_LearningTheory.Examples.Cofinite

/-!
# Representative uniform generation is strictly stronger

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Corollary 3.6
(`cor:repunignequniggen`).

The source adjoins one shared infinite half-line to a countable class that is
not uniformly generatable and partitions the enlarged universe into the
shared and original coordinates.  The common half-line makes ordinary
uniform generation trivial.  Conversely, a representative randomized
generator at any tolerance below one must put positive mass on the original
coordinate whenever the empirical sample lies there.  Consistency then lets
us choose a fresh correct original-coordinate point, yielding a deterministic
uniform generator for the original class and a contradiction.

We use the typed two-copy universe `ℕ ⊕ β` rather than integer sign
arithmetic.  This is exactly the source construction up to a countable
bijection and keeps the group boundary explicit.
-/

namespace GenLimit.RepresentativeGeneration

/-! ## Infinite common padding -/

/-- Adjoin a shared left copy of `ℕ` to a language on `β`. -/
def commonPadLanguage (L : Set β) : Set (ℕ ⊕ β) :=
  {z | match z with
    | Sum.inl _ => True
    | Sum.inr y => y ∈ L}

@[simp]
theorem inl_mem_commonPadLanguage (L : Set β) (n : ℕ) :
    Sum.inl n ∈ commonPadLanguage L :=
  trivial

@[simp]
theorem inr_mem_commonPadLanguage_iff (L : Set β) (y : β) :
    Sum.inr y ∈ commonPadLanguage L ↔ y ∈ L :=
  Iff.rfl

/-- Pointwise lift of a language class through `commonPadLanguage`. -/
def commonPadClass
    (H : GenLimit.Generic.LanguageClass β) :
    GenLimit.Generic.LanguageClass (ℕ ⊕ β) :=
  commonPadLanguage '' H

theorem commonPadClass_countable
    {H : GenLimit.Generic.LanguageClass β}
    (hH : H.Countable) :
    (commonPadClass H).Countable :=
  hH.image commonPadLanguage

theorem commonPadClass_uus
    (H : GenLimit.Generic.LanguageClass β) :
    GenLimit.Generic.UUS (commonPadClass H) := by
  intro L hL
  obtain ⟨L₀, _hL₀, rfl⟩ := hL
  apply (Set.infinite_range_of_injective
    (f := fun n : ℕ => (Sum.inl n : ℕ ⊕ β))
      Sum.inl_injective).mono
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  simp

private theorem exists_fresh_commonPad
    {t : ℕ} (xs : Fin t → ℕ ⊕ β) :
    ∃ n : ℕ,
      Sum.inl n ∉
        (↑(GenLimit.Generic.sequenceSample xs) : Set (ℕ ⊕ β)) := by
  let left : Set (ℕ ⊕ β) :=
    Set.range (fun n : ℕ => Sum.inl n)
  have hleft : left.Infinite :=
    Set.infinite_range_of_injective Sum.inl_injective
  obtain ⟨z, hzLeft, hzFresh⟩ :=
    (hleft.diff
      (GenLimit.Generic.sequenceSample xs).finite_toSet).nonempty
  obtain ⟨n, rfl⟩ := hzLeft
  exact ⟨n, hzFresh⟩

/-- Always output the least left-coordinate point absent from the finite
history. -/
noncomputable def commonPadFreshGenerator :
    GenLimit.Generic.Generator (ℕ ⊕ β) := by
  classical
  exact fun _t xs =>
    Sum.inl (Nat.find (exists_fresh_commonPad xs))

theorem commonPadFreshGenerator_fresh
    {t : ℕ} (xs : Fin t → ℕ ⊕ β) :
    commonPadFreshGenerator t xs ∉
      (↑(GenLimit.Generic.sequenceSample xs) : Set (ℕ ⊕ β)) := by
  classical
  exact Nat.find_spec (exists_fresh_commonPad xs)

theorem commonPadClass_uniformlyGeneratable
    (H : GenLimit.Generic.LanguageClass β) :
    GenLimit.Generic.UniformlyGeneratable
      (commonPadClass H) := by
  refine ⟨commonPadFreshGenerator, 0, ?_⟩
  intro L hL stream _hstream t _ht s _hts
  obtain ⟨L₀, _hL₀, rfl⟩ := hL
  constructor
  · simp [GenLimit.Generic.output, commonPadFreshGenerator]
  · have hfresh :=
      commonPadFreshGenerator_fresh
        (fun i : Fin s => stream i)
    rwa [GenLimit.Generic.sequenceSample_prefix] at hfresh

/-! ## The source's two groups -/

def commonPadLeft : Set (ℕ ⊕ β) :=
  {z | match z with
    | Sum.inl _ => True
    | Sum.inr _ => False}

def commonPadRight : Set (ℕ ⊕ β) :=
  {z | match z with
    | Sum.inl _ => False
    | Sum.inr _ => True}

@[simp] theorem inl_mem_commonPadLeft (n : ℕ) :
    Sum.inl n ∈ (commonPadLeft : Set (ℕ ⊕ β)) :=
  trivial

@[simp] theorem inr_not_mem_commonPadLeft (y : β) :
    Sum.inr y ∉ (commonPadLeft : Set (ℕ ⊕ β)) :=
  id

@[simp] theorem inl_not_mem_commonPadRight (n : ℕ) :
    Sum.inl n ∉ (commonPadRight : Set (ℕ ⊕ β)) :=
  id

@[simp] theorem inr_mem_commonPadRight (y : β) :
    Sum.inr y ∈ (commonPadRight : Set (ℕ ⊕ β)) :=
  trivial

/-- The two-coordinate finite family: shared pad first, payload second. -/
def commonPadGroups : Fin 2 → Set (ℕ ⊕ β) :=
  fun i => if i = 0 then commonPadLeft else commonPadRight

@[simp]
theorem commonPadGroups_zero :
    commonPadGroups (β := β) 0 = commonPadLeft := by
  simp [commonPadGroups]

@[simp]
theorem commonPadGroups_one :
    commonPadGroups (β := β) 1 = commonPadRight := by
  simp [commonPadGroups]

theorem commonPadGroups_isFinitePartition :
    IsFinitePartition (commonPadGroups (β := β)) := by
  apply isFinitePartition_of_pairwise_iUnion
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact Set.disjoint_left.mpr (by simp)
    · exact Set.disjoint_left.mpr (by simp)
    · exact (hij rfl).elim
  · ext z
    rcases z with n | y <;>
      simp [commonPadGroups, commonPadLeft, commonPadRight]

@[simp]
theorem extendedCommonPadGroups_one :
    extendFinitePartition (commonPadGroups (β := β)) 1 =
      commonPadRight := by
  simpa using
    extendFinitePartition_apply_fin
      (commonPadGroups (β := β)) (1 : Fin 2)

/-- Lift a payload stream into the right coordinate. -/
def commonPadStream
    (stream : GenLimit.Generic.Stream β) :
    GenLimit.Generic.Stream (ℕ ⊕ β) :=
  fun t => Sum.inr (stream t)

theorem commonPadStream_streamIn
    {stream : GenLimit.Generic.Stream β} {L : Set β}
    (hstream : GenLimit.Generic.StreamIn stream L) :
    GenLimit.Generic.StreamIn
      (commonPadStream stream) (commonPadLanguage L) := by
  rintro z ⟨t, rfl⟩
  simp [commonPadStream]
  exact hstream ⟨t, rfl⟩

theorem commonPadStream_sample_card
    (stream : GenLimit.Generic.Stream β) (t : ℕ) :
    (GenLimit.Generic.sample (commonPadStream stream) t).card =
      (GenLimit.Generic.sample stream t).card := by
  classical
  have hsample :
      GenLimit.Generic.sample (commonPadStream stream) t =
        (GenLimit.Generic.sample stream t).image Sum.inr := by
    ext z
    rcases z with n | y
    · simp only [GenLimit.Generic.mem_sample_iff,
        Finset.mem_image]
      constructor
      · rintro ⟨s, hs, h⟩
        simp [commonPadStream] at h
      · rintro ⟨y, _hy, h⟩
        simp at h
    · simp only [GenLimit.Generic.mem_sample_iff,
        Finset.mem_image]
      constructor
      · rintro ⟨s, hs, h⟩
        refine ⟨stream s, ⟨s, hs, rfl⟩, ?_⟩
        simpa [commonPadStream] using h
      · rintro ⟨y', ⟨s, hs, hy'⟩, h⟩
        have hyy : y' = y := Sum.inr_injective h
        exact ⟨s, hs, by
          simpa [commonPadStream] using hy'.trans hyy⟩
  rw [hsample, Finset.card_image_iff.mpr]
  intro x _hx y _hy hxy
  exact Sum.inr_injective hxy

@[simp]
theorem inr_mem_commonPadStream_sample_iff
    (stream : GenLimit.Generic.Stream β) (t : ℕ) (y : β) :
    Sum.inr y ∈ GenLimit.Generic.sample (commonPadStream stream) t ↔
      y ∈ GenLimit.Generic.sample stream t := by
  simp [GenLimit.Generic.mem_sample_iff, commonPadStream]

theorem commonPadStream_sample_subset_right
    (stream : GenLimit.Generic.Stream β) (t : ℕ) :
    (↑(GenLimit.Generic.sample (commonPadStream stream) t) :
        Set (ℕ ⊕ β)) ⊆ commonPadRight := by
  intro z hz
  obtain ⟨s, _hs, hsz⟩ :=
    GenLimit.Generic.mem_sample_iff.mp hz
  rw [← hsz]
  simp [commonPadStream]

theorem empirical_commonPadStream_right_eq_one
    (stream : GenLimit.Generic.Stream β)
    {t : ℕ} (ht : 0 < t) :
    empiricalGroupProbability
        (GenLimit.Generic.sample (commonPadStream stream) t)
        (extendFinitePartition (commonPadGroups (β := β))) 1 = 1 := by
  classical
  let S :=
    GenLimit.Generic.sample (commonPadStream stream) t
  have hS : S.Nonempty := by
    refine ⟨commonPadStream stream 0, ?_⟩
    exact GenLimit.Generic.value_mem_sample ht
  have hfilter :
      S.filter (fun z =>
        z ∈ extendFinitePartition
          (commonPadGroups (β := β)) 1) = S := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    rw [extendedCommonPadGroups_one]
    exact commonPadStream_sample_subset_right stream t hz
  change
    empiricalGroupProbability S
        (extendFinitePartition (commonPadGroups (β := β))) 1 = 1
  rw [empiricalGroupProbability]
  simp only [hS, if_true]
  rw [hfilter]
  exact div_self (by
    exact_mod_cast (Finset.card_pos.mpr hS).ne')

/-! ## From representative mass to a payload output -/

/-- Positive mass on a set is witnessed by a point of nonzero mass. -/
theorem exists_mass_ne_zero_of_groupMass_pos
    {μ : DiscreteDistribution α} {A : Set α}
    (hpos : 0 < groupMass μ A) :
    ∃ x, x ∈ A ∧ μ.mass x ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hzero : groupMass μ A = 0 := by
    have hrestricted : restrictedMass μ A = 0 := by
      funext x
      by_cases hx : x ∈ A
      · simp [restrictedMass, hx, hnone x hx]
      · simp [restrictedMass, hx]
    rw [groupMass, hrestricted]
    exact tsum_zero
  linarith

/-- The lower-coordinate counterpart of
`inducedGroupProbability_le_empirical_add_of_distance`. -/
theorem empiricalGroupProbability_le_induced_add_of_distance
    {μ : DiscreteDistribution α}
    {groups : ℕ → Set α} {alpha : ℝ}
    {S : Finset α}
    (halpha : 0 ≤ alpha)
    (hdistance :
      groupSupDistance μ S groups ≤ ENNReal.ofReal alpha)
    (i : ℕ) :
    empiricalGroupProbability S groups i ≤
      inducedGroupProbability μ groups i + alpha := by
  have hcoordinate :
      ENNReal.ofReal
          |inducedGroupProbability μ groups i -
            empiricalGroupProbability S groups i| ≤
        ENNReal.ofReal alpha :=
    (coordinate_le_groupSupDistance μ S groups i).trans
      hdistance
  have habs :
      |inducedGroupProbability μ groups i -
        empiricalGroupProbability S groups i| ≤ alpha :=
    (ENNReal.ofReal_le_ofReal_iff halpha).mp hcoordinate
  have hreverse :
      empiricalGroupProbability S groups i -
          inducedGroupProbability μ groups i ≤ alpha := by
    rw [abs_sub_comm] at habs
    exact (le_abs_self
      (empiricalGroupProbability S groups i -
        inducedGroupProbability μ groups i)).trans habs
  linarith

/-- A positive payload-coordinate mass contains a payload point of nonzero
mass. -/
theorem exists_payload_mass_ne_zero
    {μ : DiscreteDistribution (ℕ ⊕ β)}
    (hpos :
      0 < inducedGroupProbability μ
        (extendFinitePartition (commonPadGroups (β := β))) 1) :
    ∃ y : β, μ.mass (Sum.inr y) ≠ 0 := by
  change
    0 < groupMass μ
      (extendFinitePartition (commonPadGroups (β := β)) 1)
    at hpos
  rw [extendedCommonPadGroups_one] at hpos
  obtain ⟨z, hzRight, hzMass⟩ :=
    exists_mass_ne_zero_of_groupMass_pos hpos
  rcases z with n | y
  · simp [commonPadRight] at hzRight
  · exact ⟨y, hzMass⟩

/-- Total projection of a randomized padded generator to a deterministic
payload generator.  Histories without payload mass use an arbitrary
fallback; the representative-consistent histories used below always take
the first branch. -/
noncomputable def projectedPayloadGenerator
    [Nonempty β]
    (gen : RandomizedGenerator (ℕ ⊕ β)) :
    GenLimit.Generic.Generator β := by
  classical
  exact fun t xs =>
    let μ := gen t (fun i => Sum.inr (xs i))
    if h : ∃ y : β, μ.mass (Sum.inr y) ≠ 0 then
      Classical.choose h
    else
      Classical.choice (inferInstance : Nonempty β)

theorem projectedPayloadGenerator_mass_ne_zero
    [Nonempty β]
    (gen : RandomizedGenerator (ℕ ⊕ β))
    {t : ℕ} (xs : Fin t → β)
    (hexists :
      ∃ y : β,
        (gen t (fun i => Sum.inr (xs i))).mass
          (Sum.inr y) ≠ 0) :
    (gen t (fun i => Sum.inr (xs i))).mass
        (Sum.inr (projectedPayloadGenerator gen t xs)) ≠ 0 := by
  classical
  simp [projectedPayloadGenerator, hexists,
    Classical.choose_spec hexists]

/-! ## The representative-to-ordinary reduction -/

/-- Any representative generator for the padded class at tolerance strictly
below one projects to an ordinary uniform generator for the payload class.

The ordinary threshold is raised from `d` to `d + 1`: this guarantees a
positive history, while an earlier lifted prefix of exact size `d` supplies
the representative generator's consistency hypothesis. -/
theorem uniformlyGeneratable_of_alphaRepresentative_commonPad
    [Nonempty β]
    {H : GenLimit.Generic.LanguageClass β} {alpha : ℝ}
    (halpha : 0 ≤ alpha) (halphaOne : alpha < 1)
    (h :
      AlphaRepresentativeUniformlyGeneratable
        (commonPadClass H)
        (extendFinitePartition (commonPadGroups (β := β))) alpha) :
    GenLimit.Generic.UniformlyGeneratable H := by
  obtain ⟨gen, hrepresentative, d, hconsistent⟩ := h
  refine ⟨projectedPayloadGenerator gen, d + 1, ?_⟩
  intro L hLH stream hstream t ht s hts
  let padded := commonPadLanguage L
  let lifted := commonPadStream stream
  have hpadded : padded ∈ commonPadClass H := by
    exact ⟨L, hLH, rfl⟩
  have hlifted : GenLimit.Generic.StreamIn lifted padded := by
    exact commonPadStream_streamIn hstream
  have hdAtT :
      d ≤ (GenLimit.Generic.sample lifted t).card := by
    rw [show
      (GenLimit.Generic.sample lifted t).card =
        (GenLimit.Generic.sample stream t).card by
          exact commonPadStream_sample_card stream t]
    omega
  obtain ⟨r, hrt, hrCard⟩ :=
    GenLimit.Generic.exists_sample_card_eq_of_le hdAtT
  have hconsistentAt :
      IsConsistentAt gen padded lifted s :=
    hconsistent padded hpadded lifted hlifted r hrCard s
      (hrt.trans hts)
  have htPositive : 0 < t := by
    have hthresholdLe : d + 1 ≤ t := by
      rw [← ht]
      exact GenLimit.Generic.sample_card_le stream t
    omega
  have hsPositive : 0 < s :=
    htPositive.trans_le hts
  have hdistance :=
    hrepresentative lifted s hsPositive
  have hempirical :
      empiricalGroupProbability
          (GenLimit.Generic.sample lifted s)
          (extendFinitePartition (commonPadGroups (β := β))) 1 =
        1 := by
    exact empirical_commonPadStream_right_eq_one stream hsPositive
  have hlower :=
    empiricalGroupProbability_le_induced_add_of_distance
      halpha hdistance 1
  rw [hempirical] at hlower
  have hpayloadPositive :
      0 <
        inducedGroupProbability
          (distributionAt gen lifted s)
          (extendFinitePartition (commonPadGroups (β := β))) 1 := by
    linarith
  have hexists :
      ∃ y : β,
        (distributionAt gen lifted s).mass (Sum.inr y) ≠ 0 :=
    exists_payload_mass_ne_zero hpayloadPositive
  have houtputMass :
      (distributionAt gen lifted s).mass
          (Sum.inr
            (GenLimit.Generic.output
              (projectedPayloadGenerator gen) stream s)) ≠ 0 := by
    have hchosen :=
      projectedPayloadGenerator_mass_ne_zero gen
        (fun i : Fin s => stream i)
        (by
          simpa [distributionAt, lifted, commonPadStream] using
            hexists)
    simpa [GenLimit.Generic.output, distributionAt, lifted,
      commonPadStream] using hchosen
  have hsupported :
      SupportedOn (distributionAt gen lifted s)
        (padded \
          (↑(GenLimit.Generic.sample lifted s) : Set (ℕ ⊕ β))) :=
    isConsistentAt_iff_supportedOn.mp hconsistentAt
  have hcorrectPadded :=
    hsupported
      (Sum.inr
        (GenLimit.Generic.output
          (projectedPayloadGenerator gen) stream s))
      houtputMass
  simpa [GenLimit.Generic.CorrectAt, padded, lifted] using
    hcorrectPadded

/-- Representative uniform generation of the padded two-group construction
would imply ordinary uniform generation of its payload class. -/
theorem uniformlyGeneratable_of_representativelyUniformlyGeneratable_commonPad
    [Nonempty β]
    {H : GenLimit.Generic.LanguageClass β}
    (h :
      RepresentativelyUniformlyGeneratable
        (commonPadClass H)
        (extendFinitePartition (commonPadGroups (β := β)))) :
    GenLimit.Generic.UniformlyGeneratable H := by
  apply
    uniformlyGeneratable_of_alphaRepresentative_commonPad
      (alpha := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  exact h (1 / 2 : ℝ) (by norm_num) (by norm_num)

theorem commonPadClass_not_representativelyUniformlyGeneratable
    [Nonempty β]
    {H : GenLimit.Generic.LanguageClass β}
    (hnot : ¬ GenLimit.Generic.UniformlyGeneratable H) :
    ¬ RepresentativelyUniformlyGeneratable
        (commonPadClass H)
        (extendFinitePartition (commonPadGroups (β := β))) := by
  intro h
  exact hnot
    (uniformlyGeneratable_of_representativelyUniformlyGeneratable_commonPad
      h)

/-! ## Published Corollary 3.6 -/

/-- A typed version of the source's two integer half-lines. -/
abbrev UniformSeparationUniverse := ℕ ⊕ ℕ

/-- The source witness obtained by padding the countable cofinite class. -/
def uniformSeparationClass :
    GenLimit.Generic.LanguageClass UniformSeparationUniverse :=
  commonPadClass (GenLimit.LiRamanTewari.cofiniteLanguageClass ℕ)

/-- The source witness's shared/payload partition. -/
def uniformSeparationGroups :
    Fin 2 → Set UniformSeparationUniverse :=
  commonPadGroups

theorem uniformSeparationClass_countable :
    uniformSeparationClass.Countable :=
  commonPadClass_countable
    GenLimit.LiRamanTewari.cofiniteLanguageClass_countable

theorem uniformSeparationClass_uus :
    GenLimit.Generic.UUS uniformSeparationClass :=
  commonPadClass_uus
    (GenLimit.LiRamanTewari.cofiniteLanguageClass ℕ)

theorem uniformSeparationClass_uniformlyGeneratable :
    GenLimit.Generic.UniformlyGeneratable
      uniformSeparationClass :=
  commonPadClass_uniformlyGeneratable
    (GenLimit.LiRamanTewari.cofiniteLanguageClass ℕ)

theorem uniformSeparationGroups_isFinitePartition :
    IsFinitePartition uniformSeparationGroups :=
  commonPadGroups_isFinitePartition

theorem uniformSeparationClass_not_representativelyUniformlyGeneratable :
    ¬ RepresentativelyUniformlyGeneratable
        uniformSeparationClass
        (extendFinitePartition uniformSeparationGroups) :=
  commonPadClass_not_representativelyUniformlyGeneratable
    GenLimit.LiRamanTewari.cofiniteLanguageClass_not_uniform

/-- Source-facing published Corollary 3.6: on an explicit countably infinite universe,
ordinary uniform generation is strictly weaker than representative uniform
generation, even for a two-group finite partition.

The paper prints the claim for a generic countable universe but proves it on
`ℤ`; the generic reading is false for finite universes.  `ℕ ⊕ ℕ` is
countably bijective with the proof's two integer half-lines. -/
theorem uniformGeneration_not_representativeUniformGeneration :
    ∃ H : GenLimit.Generic.LanguageClass UniformSeparationUniverse,
      ∃ groups : Fin 2 → Set UniformSeparationUniverse,
        H.Countable ∧
        GenLimit.Generic.UUS H ∧
        IsFinitePartition groups ∧
        GenLimit.Generic.UniformlyGeneratable H ∧
        ¬ RepresentativelyUniformlyGeneratable H
            (extendFinitePartition groups) := by
  exact
    ⟨uniformSeparationClass, uniformSeparationGroups,
      uniformSeparationClass_countable,
      uniformSeparationClass_uus,
      uniformSeparationGroups_isFinitePartition,
      uniformSeparationClass_uniformlyGeneratable,
      uniformSeparationClass_not_representativelyUniformlyGeneratable⟩

end GenLimit.RepresentativeGeneration
