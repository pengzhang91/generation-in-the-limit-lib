import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Countable

/-!
# Finite covers, separated samples, and the v2 UUS condition

These metric arguments support the source's prefix-covering formulation of
UUS. A finite collection of centers attains its nearest distance. A separated
finite sample therefore gives a covering-number lower bound, and failure of
a finite cover produces arbitrarily large separated samples.
-/

namespace GenLimit.MetricSpaces

theorem mem_closedNeighborhood_finset_iff
    {ρ : Distance α} {r : ℝ} {S : Finset α} {y : α} :
    y ∈ closedNeighborhood ρ (S : Set α) r ↔ ∃ x ∈ S, ρ x y ≤ r := by
  classical
  constructor
  · intro h
    obtain ⟨z, hz, _⟩ := h (r + 1) (by linarith)
    obtain ⟨x, hx, hmin⟩ := S.exists_min_image (fun x => ρ x y) ⟨z, hz⟩
    refine ⟨x, hx, ?_⟩
    by_contra hnot
    obtain ⟨w, hw, hwy⟩ := h (ρ x y) (lt_of_not_ge hnot)
    exact (not_lt_of_ge (hmin w hw)) hwy
  · rintro ⟨x, hx, hxy⟩ η hrη
    exact ⟨x, hx, hxy.trans_lt hrη⟩

theorem HasFiniteCover.mono_set
    {ρ : Distance α} {r : ℝ} {A B : Set α}
    (h : HasFiniteCover ρ r B) (hAB : A ⊆ B) : HasFiniteCover ρ r A := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, hAB.trans hS⟩

/-- Covering a closed neighborhood adds its radius to that of the finite
cover, including when the neighborhood's infimum is not attained. -/
theorem HasFiniteCover.closedNeighborhood
    {ρ : Distance α} {r s : ℝ} {A : Set α}
    (htriangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (h : HasFiniteCover ρ s A) :
    HasFiniteCover ρ (r + s) (closedNeighborhood ρ A r) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  intro y hy η hη
  obtain ⟨x, hx, hxy⟩ := hy (η - s) (by linarith)
  obtain ⟨z, hz, hzx⟩ := mem_closedNeighborhood_finset_iff.mp (hS hx)
  refine ⟨z, hz, ?_⟩
  have := htriangle z x y
  linarith

/-- A radius-`r` ball contains at most one point of a `2r`-separated set. -/
theorem coveringNumberAtLeast_of_separated
    {ρ : Distance α} {r : ℝ} {S : Finset α}
    (hsymm : ∀ x y, ρ x y = ρ y x)
    (htriangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (hsep : (S : Set α).Pairwise (fun x y => 2 * r < ρ x y)) :
    CoveringNumberAtLeast ρ r (S : Set α) S.card := by
  classical
  intro centers hcover
  have hex : ∀ x : S, ∃ c : centers, ρ c x ≤ r := by
    intro x
    obtain ⟨c, hc, hcx⟩ := mem_closedNeighborhood_finset_iff.mp (hcover x.property)
    exact ⟨⟨c, hc⟩, hcx⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hfar := hsep x.property y.property hne
    have hx := hf x
    have hy := hf y
    rw [← hxy] at hy
    have ht := htriangle (x : α) (f x : α) (y : α)
    rw [hsymm (x : α) (f x : α)] at ht
    linarith
  simpa using Fintype.card_le_of_injective f hinj

theorem exists_outside_finite_cover
    {ρ : Distance α} {r : ℝ} {A : Set α}
    (h : ¬ HasFiniteCover ρ r A) (S : Finset α) :
    ∃ x ∈ A, x ∉ closedNeighborhood ρ (S : Set α) r := by
  classical
  by_contra hnone
  apply h
  refine ⟨S, ?_⟩
  intro x hx
  by_contra hfar
  exact hnone ⟨x, hx, hfar⟩

/-- The finite greedy-packing argument, restricted to the set being covered. -/
theorem exists_separated_finset_of_not_finiteCover
    {ρ : Distance α} {R : ℝ} {A : Set α}
    (hrefl : ∀ x, ρ x x = 0) (hsymm : ∀ x y, ρ x y = ρ y x)
    (hR : 0 ≤ R) (h : ¬ HasFiniteCover ρ R A) (d : ℕ) :
    ∃ S : Finset α, (S : Set α) ⊆ A ∧ S.card = d ∧
      (S : Set α).Pairwise (fun x y => R < ρ x y) := by
  classical
  induction d with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ d ih =>
    obtain ⟨S, hSA, hcard, hsep⟩ := ih
    obtain ⟨x, hxA, hfar⟩ := exists_outside_finite_cover h S
    have hdist : ∀ y ∈ S, R < ρ y x := by
      intro y hy
      by_contra hnot
      apply hfar
      exact mem_closedNeighborhood_finset_iff.mpr ⟨y, hy, le_of_not_gt hnot⟩
    have hxS : x ∉ S := by
      intro hx
      have := hdist x hx
      rw [hrefl] at this
      linarith
    refine ⟨insert x S, ?_, by simp [hxS, hcard], ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxA
      · exact hSA hy
    · intro u hu v hv hne
      rcases Finset.mem_insert.mp hu with hux | huS
      · subst u
        rcases Finset.mem_insert.mp hv with hvx | hvS
        · exact (hne hvx.symm).elim
        · rw [hsymm]
          exact hdist v hvS
      · rcases Finset.mem_insert.mp hv with hvx | hvS
        · subst v
          exact hdist u huS
        · exact hsep huS hvS hne

/-- An infinite stream with no finite `2r`-cover reaches every prefix
covering-number threshold at radius `r`. -/
theorem prefix_coveringNumber_unbounded_of_not_finiteCover
    {ρ : Distance α} {r : ℝ} {stream : GenLimit.Generic.Stream α}
    (hrefl : ∀ x, ρ x x = 0) (hsymm : ∀ x y, ρ x y = ρ y x)
    (htriangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (hr : 0 ≤ r) (h : ¬ HasFiniteCover ρ (2 * r) (Set.range stream))
    (d : ℕ) :
    ∃ t, CoveringNumberAtLeast ρ r (GenLimit.Generic.sample stream t : Set α) d := by
  obtain ⟨S, hS, hcard, hsep⟩ :=
    exists_separated_finset_of_not_finiteCover hrefl hsymm (by linarith) h d
  obtain ⟨t, ht⟩ := GenLimit.Generic.finset_eventually_subset_sample rfl S hS
  refine ⟨t, ?_⟩
  rw [← hcard]
  exact coveringNumberAtLeast_mono_set ht
    (coveringNumberAtLeast_of_separated hsymm htriangle hsep)

/-- A useful sufficient condition for v2 UUS. The factor three comes from
the presentation radius plus a `2r` packing cover of its range. -/
theorem uus_of_no_finite_cover_triple
    {ρ : Distance α} {r : ℝ} {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0) (hsymm : ∀ x y, ρ x y = ρ y x)
    (htriangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (hr : 0 ≤ r) (h : InfiniteCoveringSupportAt ρ (3 * r) H) :
    UniformlyUnboundedSupportAt ρ r H := by
  intro L hL
  obtain ⟨x, hx, _⟩ := exists_outside_finite_cover (h L hL) ∅
  refine ⟨⟨x, hx⟩, ?_⟩
  intro stream hp d
  apply prefix_coveringNumber_unbounded_of_not_finiteCover hrefl hsymm htriangle hr
  intro hcover
  apply h L hL
  have hlarge := (HasFiniteCover.closedNeighborhood (r := r) htriangle hcover).mono_set hp.2
  convert hlarge using 1
  linarith

/-- A finite internal cover would give a positive covering sequence with
uniformly bounded prefix covering numbers, contrary to Definition 2.3. -/
theorem UniformlyUnboundedSupportAt.not_finiteInternalCover
    {ρ : Distance α} {r : ℝ} {H : GenLimit.Generic.LanguageClass α}
    (h : UniformlyUnboundedSupportAt ρ r H)
    {L : GenLimit.Generic.Language α} (hL : L ∈ H) :
    ¬ HasFiniteInternalCover ρ r L := by
  classical
  rintro ⟨centers, hcL, hcover⟩
  obtain ⟨y, hy⟩ := (h L hL).1
  obtain ⟨c, hc, _⟩ := hcover hy (r + 1) (by linarith)
  obtain ⟨stream, hstream⟩ := centers.finite_toSet.countable.exists_eq_range ⟨c, hc⟩
  have hp : MetricPresentation ρ r stream L := by
    constructor
    · rw [GenLimit.Generic.StreamIn, ← hstream]
      exact hcL
    · rw [← hstream]
      exact hcover
  obtain ⟨t, ht⟩ := (h L hL).2 stream hp (centers.card + 1)
  have hbad := ht centers
    ((GenLimit.Generic.sample_subset_of_streamIn hp.1 t).trans hcover)
  omega

end GenLimit.MetricSpaces
