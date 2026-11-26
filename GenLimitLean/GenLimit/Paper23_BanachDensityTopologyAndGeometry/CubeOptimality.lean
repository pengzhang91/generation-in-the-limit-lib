import GenLimit.Paper23_BanachDensityTopologyAndGeometry.CenteredCubes
import GenLimit.Paper15_PartialEnumeration.SharpDensity

/-! The singleton speed-one benchmark in Theorem 5.8. On a single lattice
ray, centered cubes cut out exactly the ordinary one-dimensional prefixes. -/

namespace GenLimit.KleinbergWei.Banach

open Filter Set
open PartialEnumeration.Sharpness
open scoped Classical

private def ray (d n : ℕ) : Lattice (d+1) := fun _ => n
private def rank {d} (x : Lattice (d+1)) := (x 0).toNat

private theorem rank_ray (d n) : rank (ray d n) = n := by simp [rank,ray]

private theorem ray_cube (d n r) : ray d n ∈ centeredCube (d+1) r ↔ n ≤ r := by
  simp [centeredCube, ray, Pi.le_def]

private theorem cubeCount_ray (d) (S : Set (Lattice (d+1))) (r) :
    cubeCount (S ∩ range (ray d)) r =
      natural.prefixCount ((ray d) ⁻¹' S) (r+1) := by
  classical
  symm
  unfold OrderedLanguage.prefixCount
  apply Finset.card_bij (fun n _ => ray d n)
  · intro n hn
    obtain ⟨hn,h⟩ := Finset.mem_filter.mp hn
    simp only [Finset.mem_filter]
    exact ⟨(ray_cube ..).2 (Nat.le_of_lt_succ (Finset.mem_range.mp hn)), h, n,rfl⟩
  · intro i _ j _ e
    simpa only [rank_ray] using congrArg rank e
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨hc,hs,⟨n,rfl⟩⟩ := hx
    exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((ray_cube ..).1 hc)), hs⟩,rfl⟩

private theorem ray_density (d) (S : Set (Lattice (d+1))) :
    centeredLowerDensity S (range (ray d)) = natural.lowerDensity ((ray d) ⁻¹' S) := by
  have denom (r) : cubeCount (range (ray d)) r = r+1 := by
    simpa [natural, OrderedLanguage.prefixCount] using cubeCount_ray d Set.univ r
  unfold centeredLowerDensity OrderedLanguage.lowerDensity
  rw [← liminf_nat_add (fun n => natural.prefixRatio ((ray d) ⁻¹' S) n) 1]
  simp only [cubeCount_ray, denom, OrderedLanguage.prefixRatio, Nat.add_one_ne_zero, if_false]

/-- In every positive dimension the same singleton class witnesses optimality. -/
theorem centered_singleton_upper (d : ℕ) :
    ∃ K : Set (Lattice (d+1)), K.Infinite ∧ ∀ A : List (Lattice (d+1)) → Lattice (d+1),
      (∀ s, Set.range s = K → cubeValid A s K) →
      ∃ s, Function.Injective s ∧ Set.range s = K ∧
        centeredLowerDensity (Set.range (cubePlay A s)) K ≤ 1/2 := by
  let f := ray d
  have hinj : Function.Injective f := Function.LeftInverse.injective (rank_ray d)
  refine ⟨range f, Set.infinite_range_of_injective hinj, fun A valid => ?_⟩
  let G := fun h : List ℕ => rank (A (h.map f))
  let s := f ∘ stream G
  have hpres : range s = range f := by
    change range (f ∘ stream G) = range f
    rw [range_comp,PartialEnumeration.Sharpness.presents,image_univ]
  obtain ⟨T,hgood⟩ := valid s hpres
  have obs (t) : output G t = rank (cubePlay A s t) := by
    simp [output, history_eq, cubePlay, textPrefix, s, G, List.map_map]
  have bound : FreshAfter G T := by
    intro t ht i hi h
    obtain ⟨⟨n,hn⟩,fresh,_⟩ := hgood t ht
    apply fresh i hi
    rw [obs,← hn] at h
    exact (congrArg f (h.trans (rank_ray d n))).trans hn
  refine ⟨s,hinj.comp (stream_injective G),hpres,?_⟩
  rw [ray_density]
  have sub : f ⁻¹' range (cubePlay A s) ⊆ range (output G) := by
    rintro x ⟨t,ht⟩
    exact ⟨t,(obs t).trans ((congrArg rank ht).trans (rank_ray d x))⟩
  have hlim : natural.lowerDensity (range (output G)) ≤ natural.upperDensity (range (output G)) :=
    liminf_le_limsup (isBoundedUnder_of ⟨1,natural.prefixRatio_le_one _⟩)
      (isBoundedUnder_of ⟨0,natural.prefixRatio_nonneg _⟩)
  have thin_one : thin 1 = id := by funext j; simp [thin]
  exact ((natural.lowerDensity_mono sub).trans hlim).trans
    (by simpa [thin_one] using diluted_upper (α := 1) (by norm_num) le_rfl G T bound)

end GenLimit.KleinbergWei.Banach
