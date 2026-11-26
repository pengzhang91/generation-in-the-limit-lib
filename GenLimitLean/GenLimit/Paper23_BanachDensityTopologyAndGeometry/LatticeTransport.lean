import GenLimit.Paper23_BanachDensityTopologyAndGeometry.CenteredCubes

/-! Transport a finite-history generator from word codes to lattice points.
All inputs and past outputs are transported together. -/
namespace GenLimit.KleinbergWei.Banach.LatticeTransport
open Set DensityMeasures
open scoped Classical
noncomputable section
variable {d} (e : ℕ → Lattice d) (inj : Function.Injective e)

def lift (G : List ℕ → ℕ) (p : List (Lattice d)) := e (G (p.map (Function.invFun e)))

include inj in
theorem run {S : Set ℕ} {s : ℕ → Lattice d} (pres : range s = e '' S) (G : List ℕ → ℕ) :
    let t := Function.invFun e ∘ s
    Presents t S ∧ range (cubePlay (lift e G) s) = e '' range (OrderedFocus.play G t) ∧
      (OrderedFocus.ElementValid t (OrderedFocus.play G t) S → cubeValid (lift e G) s (e '' S)) := by
  let g := Function.invFun e
  let t := g ∘ s
  have left : Function.LeftInverse g e := Function.leftInverse_invFun inj
  have orig (i : ℕ) : e (t i) = s i := by
    obtain ⟨x,_,hx⟩ := (show s i ∈ e '' S from pres ▸ mem_range_self i)
    simp [t,←hx,left x]
  have full : Presents t S := by
    change range (g ∘ s) = S
    rw [range_comp,pres,image_image,show (fun x => g (e x)) = (fun x => x) from funext left,Set.image_id']
  have eq (i) : cubePlay (lift e G) s i = e (OrderedFocus.play G t i) := by
    simp [cubePlay,lift,OrderedFocus.play,t,g,textPrefix,List.map_map]
  refine ⟨full,?_,?_⟩
  · rw [←range_comp]; exact congrArg range (funext eq)
  · rintro ⟨T,ok⟩
    refine ⟨T,fun i hi => ?_⟩
    obtain ⟨hit,fresh,recent⟩ := ok i hi
    rw [eq]
    exact ⟨⟨_,hit,rfl⟩,fun k hk h => fresh k hk (inj ((orig k).trans h)),
      fun k hk h => recent k hk (inj ((eq k).symm.trans h))⟩

end
end GenLimit.KleinbergWei.Banach.LatticeTransport
