import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardDiagonal
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.IntervalOptimality

/-! The unrestricted filtered generation problem has the same truth value for
all finite-rank classes and for known singleton languages across all dimensions.
The reverse implication also allows repetitions and removes monotonicity of the
filter once the finite game has been solved. -/
namespace GenLimit.KleinbergWei.Banach
open Set Filter
open scoped Classical ENNReal
noncomputable section

/-- Generation on arbitrary known singleton lattice languages at a fixed
dimension and tolerance, restricted to injective presentations. -/
def SingletonFilteredGuarantee (d : ℕ) (ε : ℝ) := ∀ K : Set (Lattice d), K.Infinite →
  ∀ f : ℕ → ℝ, Monotone f → (∀ v, 0 < f v) → Tendsto f atTop atTop →
  ∃ A : List (Lattice d) → Lattice d, ∀ s, range s = K → Function.Injective s →
    cubeValid A s K ∧ ENNReal.ofReal (1/2-ε) ≤ filteredRectangularDensity f (range (cubePlay A s)) K

/-- The finite-rank conclusion of 5.5 at a fixed dimension and tolerance. -/
def FiniteRankFilteredGuarantee (d : ℕ) (ε : ℝ) := ∀ (e : ℕ → Lattice d), Function.Injective e →
  ∀ (C : LanguageFamily), (∀ z, (C z).Infinite) → ∀ R,
  TowerTopology.FiniteRankAtMost (range C) R → ∀ f : ℕ → ℝ, Tendsto f atTop atTop →
  ∃ A : List (Lattice d) → Lattice d, ∀ z s, range s = e '' C z →
    cubeValid A s (e '' C z) ∧ ENNReal.ofReal (1/2-ε) ≤
      filteredRectangularDensity f (range (cubePlay A s)) (e '' C z)

/-- Reduction with dimension and tolerance explicit. -/
theorem finite_rank_of_singletons (d : ℕ) {q : ℝ} (positive : 0 < q) (small : q < 1/2)
    (single : SingletonFilteredGuarantee (d+1) (q/2)) : FiniteRankFilteredGuarantee d q := by
  intro e he C inf R rank f grows
  exact filtered_generation_of_finite_response e he positive
    (BoardDiagonal.finite_response_of_singletons e he positive small single) f grows C inf rank

theorem singleton_of_finite_rank (d : ℕ) (q : ℝ) (all : FiniteRankFilteredGuarantee d q) :
    SingletonFilteredGuarantee d q := by
  intro K inf f _ _ grows
  letI : Infinite K := inf.to_subtype
  let key : ℕ ≃ K := Classical.choice (inferInstance : Nonempty (ℕ ≃ K))
  let e (x : ℕ) : Lattice d := (key x).val
  have he : Function.Injective e := Subtype.val_injective.comp key.injective
  have image : e '' (Set.univ : Set ℕ) = K := by
    ext x; constructor
    · rintro ⟨y,_,rfl⟩; exact (key y).property
    · intro hx; exact ⟨key.symm ⟨x,hx⟩,Set.mem_univ _,by simp [e]⟩
  obtain ⟨A,works⟩ := all e he (fun _ => Set.univ) (fun _ => Set.infinite_univ) 1
    singleton_rank_one f grows
  refine ⟨A,fun s pres _ => ?_⟩
  simpa only [image] using works 0 s (image ▸ pres)

/-- Across all dimensions and tolerances, the known-target and finite-rank
versions of the higher-dimensional filtered theorem are equivalent. -/
theorem filtered_generation_iff_singletons :
    (∀ d q, 0 < q → FiniteRankFilteredGuarantee d q) ↔
    (∀ d q, 0 < q → SingletonFilteredGuarantee d q) := by
  refine ⟨fun all d q hq => singleton_of_finite_rank d q (all d q hq),?_⟩
  intro all d ε he
  let q := min ε (1/4)
  have hp : 0 < q := lt_min he (by norm_num)
  have small : q < 1/2 := (min_le_right ..).trans_lt (by norm_num)
  intro e inj C inf R rank f grows
  obtain ⟨A,works⟩ := finite_rank_of_singletons d hp small (all _ _ (half_pos hp)) e inj C inf R rank f grows
  refine ⟨A,fun z s pres => ?_⟩
  obtain ⟨valid,half⟩ := works z s pres
  exact ⟨valid,(ENNReal.ofReal_le_ofReal (sub_le_sub_left (min_le_left ..) _)).trans half⟩

end
end GenLimit.KleinbergWei.Banach
