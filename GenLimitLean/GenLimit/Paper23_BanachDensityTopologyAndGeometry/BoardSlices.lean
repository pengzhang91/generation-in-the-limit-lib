import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardPermutations

/-! Place arbitrary finite boards in distinct lattice slices. A rectangle
in a board lifts to a positive-width rectangle of exactly the same volume.
This allows a single known language to test an unbounded series of games. -/
namespace GenLimit.KleinbergWei.Banach.BoardSlices
open Set Finset BoardPermutations
open scoped Classical
noncomputable section
variable {d : ℕ} (e : ℕ → Lattice d) (D : ℕ → Finset ℕ)

def place (j x : ℕ) : Lattice (d+1) := Fin.cons (2*(j:ℤ)) (e x)
def language := {v : Lattice (d+1) | ∃ j x, x ∈ D j ∧ place e j x = v}

theorem inj (he : Function.Injective e) (j : ℕ) : Function.Injective (place e j) := by
  intro x y eq
  exact he (funext fun i => congrFun eq i.succ)

theorem member {j x} (hx : x ∈ D j) : place e j x ∈ language e D := ⟨j,x,hx,rfl⟩

theorem infinite (nonempty : ∀ j, (D j).Nonempty) : (language e D).Infinite := by
  let one j := place e j (nonempty j).choose
  have oneIn (j : ℕ) : one j ∈ language e D := member e D (nonempty j).choose_spec
  have unique : Function.Injective one := by
    intro i j eq
    have h : 2*(i:ℤ) = 2*(j:ℤ) := congrFun eq 0
    omega
  exact (Set.infinite_range_of_injective unique).mono (Set.range_subset_iff.mpr oneIn)

theorem unused (p : Finset (Lattice (d+1))) (n : ℕ) :
    ∃ j ≥ n, ∀ x, place e j x ∉ p := by
  let cap := p.sup (fun v => (v 0).natAbs)
  refine ⟨n+cap+1,by omega,fun x hx => ?_⟩
  have le : ((place e (n+cap+1) x) 0).natAbs ≤ cap := Finset.le_sup (f:=fun v => (v 0).natAbs) hx
  change (2*((n+cap+1:ℕ):ℤ)).natAbs ≤ cap at le
  omega

def lower (j : ℕ) (l : Lattice d) : Lattice (d+1) := Fin.cons (2*(j:ℤ)) l
def upper (j : ℕ) (u : Lattice d) : Lattice (d+1) := Fin.cons (2*(j:ℤ)+1) u

theorem widths {l u : Lattice d} (pos : ∀ i, l i < u i) (j : ℕ) :
    ∀ i, lower j l i < upper j u i := Fin.cases (by change 2*(j:ℤ) < 2*j+1; omega) pos

theorem volume (l u : Lattice d) (j : ℕ) :
    geometricVolume (lower j l) (upper j u) = geometricVolume l u := by
  simp [geometricVolume,Fin.prod_univ_succ,lower,upper]

def sample (j : ℕ) (l u : Lattice d) := (D j).filter (fun x => e x ∈ Finset.Icc l u)

theorem isolate (j : ℕ) (l u : Lattice d) :
    Rectangles.box (language e D) (lower j l) (upper j u) =
      (sample e D j l u).image (place e j) := by
  ext v
  constructor
  · intro hv
    obtain ⟨⟨lo,hi⟩,k,x,inD,rfl⟩ := Rectangles.mem_box.mp hv
    have a : 2*(j:ℤ) ≤ 2*(k:ℤ) := lo 0
    have b : 2*(k:ℤ) ≤ 2*(j:ℤ)+1 := hi 0
    have eq : k=j := by omega
    subst k
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨inD,Finset.mem_Icc.mpr
      ⟨fun i => lo i.succ,fun i => hi i.succ⟩⟩,rfl⟩
  · rintro hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨inD,rect⟩ := Finset.mem_filter.mp hx
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp rect
    exact Rectangles.mem_box.mpr ⟨⟨Fin.cases (by rfl) lo,
      Fin.cases (by change 2*(j:ℤ) ≤ 2*j+1; omega) hi⟩,member e D inD⟩

theorem count (he : Function.Injective e) (j : ℕ) (l u : Lattice d) :
    (Rectangles.box (language e D) (lower j l) (upper j u)).card = (sample e D j l u).card := by
  rw [isolate,Finset.card_image_of_injective _ (inj e he j)]

end
end GenLimit.KleinbergWei.Banach.BoardSlices
