import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import Mathlib.Data.Nat.Find

/-!
# Uniform generation from finite metric scale-closure dimension

This module formalizes `lem:clossuff`, the sufficiency direction of
Theorem 3.1 in Li--Raman--Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1.

The proof constructs the source's common-core choice generator.  Once the
observed sample has covering number above a finite scale-closure bound, its
common core cannot have a finite novelty-scale cover.  Hence some common-core
point lies outside the observed closed neighbourhood.

The source assumes a genuine metric, positive scales, and `r`-UUS.  This
direction only uses metric reflexivity and nonnegativity of the adversary
scale; the `r`-UUS assumption is unnecessary once finite scale-closure
dimension is supplied.
-/

namespace GenLimit.MetricSpaces

/-- A finite set covers itself at every nonnegative radius for a reflexive
distance kernel. -/
theorem finset_hasFiniteCover
    {ρ : Distance α} {ε : ℝ}
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε)
    (S : Finset α) :
    HasFiniteCover ρ ε (S : Set α) := by
  classical
  refine ⟨S, ?_⟩
  intro y hy η hεη
  exact ⟨y, hy, by rw [hrefl]; linarith⟩

/-- Every finite set has an exact finite covering number at a nonnegative
radius for a reflexive distance kernel. -/
theorem finset_exists_coveringNumberEq
    {ρ : Distance α} {ε : ℝ}
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε)
    (S : Finset α) :
    ∃ d, CoveringNumberEq ρ ε (S : Set α) d := by
  classical
  let P : ℕ → Prop := fun d =>
    ∃ centers : Finset α,
      centers.card = d ∧
        (S : Set α) ⊆
          closedNeighborhood ρ (centers : Set α) ε
  have hex : ∃ d, P d := by
    obtain ⟨centers, hcover⟩ :=
      finset_hasFiniteCover (ρ := ρ) hrefl hε S
    exact ⟨centers.card, centers, rfl, hcover⟩
  let d := Nat.find hex
  refine ⟨d, ?_, ?_⟩
  · intro centers hcover
    exact Nat.find_min' hex ⟨centers, rfl, hcover⟩
  · exact Nat.find_spec hex

/-- Above a finite scale-closure bound, a consistent sample's common core
cannot have a finite novelty-scale cover. -/
theorem commonCore_not_hasFiniteCover_of_dimension_bound
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    {D : ℕ}
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε)
    (hD : ∀ d, D < d →
      ¬ ∃ S : Finset α,
        IsScaleClosureWitness ρ ε ε' H S d)
    (S : Finset α)
    (hversion : (versionSpace H S).Nonempty)
    (hlarge :
      CoveringNumberAtLeast ρ ε (S : Set α) (D + 1)) :
    ¬ HasFiniteCover ρ ε' (commonCore H S) := by
  obtain ⟨d, hd⟩ :=
    finset_exists_coveringNumberEq
      (ρ := ρ) hrefl hε S
  have hDd : D < d := by
    obtain ⟨centers, hcard, hcover⟩ := hd.2
    have hle : D + 1 ≤ centers.card :=
      hlarge centers hcover
    rw [hcard] at hle
    exact Nat.lt_of_succ_le hle
  intro hcore
  exact hD d hDd ⟨S, hversion, hd, hcore⟩

/-- A common core with no finite cover contains a point outside the
neighbourhood of any specified finite sample. -/
theorem exists_commonCore_point_outside_sample_neighborhood
    {ρ : Distance α} {ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (S : Finset α)
    (hcore :
      ¬ HasFiniteCover ρ ε' (commonCore H S)) :
    ∃ x,
      x ∈ commonCore H S ∧
        x ∉ closedNeighborhood ρ (S : Set α) ε' := by
  classical
  by_contra hfresh
  apply hcore
  refine ⟨S, ?_⟩
  intro x hx
  by_contra hfar
  exact hfresh ⟨x, hx, hfar⟩

/-- The choice generator used by the metric scale-closure proof. -/
noncomputable def scaleClosureGenerator
    [Nonempty α]
    (ρ : Distance α) (ε' : ℝ)
    (H : GenLimit.Generic.LanguageClass α) :
    GenLimit.Generic.Generator α :=
  fun _ xs => by
    classical
    let S := GenLimit.Generic.sequenceSample xs
    exact if h :
        ∃ x,
          x ∈ commonCore H S ∧
            x ∉ closedNeighborhood ρ (S : Set α) ε' then
      Classical.choose h
    else
      Classical.choice inferInstance

theorem scaleClosureGenerator_spec
    [Nonempty α]
    {ρ : Distance α} {ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    {t : ℕ} {xs : Fin t → α}
    (hfresh :
      ∃ x,
        x ∈ commonCore H
            (GenLimit.Generic.sequenceSample xs) ∧
          x ∉ closedNeighborhood ρ
            (GenLimit.Generic.sequenceSample xs : Set α) ε') :
    scaleClosureGenerator ρ ε' H t xs ∈
          commonCore H
            (GenLimit.Generic.sequenceSample xs) ∧
      scaleClosureGenerator ρ ε' H t xs ∉
          closedNeighborhood ρ
            (GenLimit.Generic.sequenceSample xs : Set α) ε' := by
  classical
  simpa only [scaleClosureGenerator, dif_pos hfresh] using
    Classical.choose_spec hfresh

/-- Sufficiency in Theorem 3.1 ("Characterization of Uniform
Generatability") of Li--Raman--Tewari, corresponding to source lemma
`lem:clossuff`.

The source assumes `ρ` is a metric and `ε > 0`; the proof only uses the
displayed reflexivity and nonnegativity consequences.  Its `r`-UUS
assumption is not needed in this constructive direction once finite
scale-closure dimension is supplied.
-/
theorem finite_scaleClosureDimension_implies_uniform
    [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε)
    (hdim :
      HasFiniteScaleClosureDimension ρ ε ε' H) :
    UniformlyGeneratableAt ρ ε ε' H := by
  classical
  obtain ⟨D, hD⟩ := hdim
  refine ⟨scaleClosureGenerator ρ ε' H, D + 1, ?_⟩
  intro L hLH stream hstream t ht s hts
  have hsample :
      (GenLimit.Generic.sample stream s : Set α) ⊆ L := by
    intro x hx
    obtain ⟨i, _his, rfl⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hx
    exact hstream ⟨i, rfl⟩
  have htarget :
      L ∈ versionSpace H
        (GenLimit.Generic.sample stream s) :=
    ⟨hLH, hsample⟩
  have hversion :
      (versionSpace H
        (GenLimit.Generic.sample stream s)).Nonempty :=
    ⟨L, htarget⟩
  have hsampleMono :
      (GenLimit.Generic.sample stream t : Set α) ⊆
        (GenLimit.Generic.sample stream s : Set α) := by
    exact GenLimit.Generic.sample_mono hts
  have hlarge :
      CoveringNumberAtLeast ρ ε
        (GenLimit.Generic.sample stream s : Set α) (D + 1) :=
    coveringNumberAtLeast_mono_set hsampleMono ht
  have hnoCover :
      ¬ HasFiniteCover ρ ε'
        (commonCore H
          (GenLimit.Generic.sample stream s)) :=
    commonCore_not_hasFiniteCover_of_dimension_bound
      hrefl hε hD (GenLimit.Generic.sample stream s)
        hversion hlarge
  have hfresh :
      ∃ x,
        x ∈ commonCore H
            (GenLimit.Generic.sample stream s) ∧
          x ∉ closedNeighborhood ρ
            (GenLimit.Generic.sample stream s : Set α) ε' :=
    exists_commonCore_point_outside_sample_neighborhood
      (GenLimit.Generic.sample stream s) hnoCover
  have hspec :=
    scaleClosureGenerator_spec
      (ρ := ρ) (ε' := ε') (H := H)
      (xs := fun i : Fin s => stream i)
      (by simpa [GenLimit.Generic.sequenceSample_prefix]
        using hfresh)
  rw [GenLimit.Generic.sequenceSample_prefix] at hspec
  change
    scaleClosureGenerator ρ ε' H s
          (fun i : Fin s => stream i) ∈ L ∧
      scaleClosureGenerator ρ ε' H s
          (fun i : Fin s => stream i) ∉
        closedNeighborhood ρ
          (GenLimit.Generic.sample stream s : Set α) ε'
  exact ⟨hspec.1 L htarget, hspec.2⟩

end GenLimit.MetricSpaces
