import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredBoxes

/-! The partition of Lemma 5.10. After stage j the gap to the next radial
boundary exceeds every volume at which f is still smaller than j. -/
namespace GenLimit.KleinbergWei.Banach.FilterShells
open Filter Finset
open scoped Classical
noncomputable section

variable (f : ℕ → ℝ) (grows : Tendsto f atTop atTop)

private def cutoff (j : ℕ) := (eventually_atTop.mp ((tendsto_atTop.mp grows) (j:ℝ))).choose

private theorem cutoff_spec (j V : ℕ) (h : cutoff f grows j ≤ V) : (j:ℝ) ≤ f V :=
  (eventually_atTop.mp ((tendsto_atTop.mp grows) (j:ℝ))).choose_spec V h

def edge : ℕ → ℕ
  | 0 => 0
  | j+1 => edge j + cutoff f grows j + 1

private theorem strict : StrictMono (edge f grows) :=
  strictMono_nat_of_lt_succ fun j => by change _ < _+_+1; omega

def radius {d} (x : Lattice d) := Finset.univ.sup (fun i => (x i).natAbs)

private theorem above (r : ℕ) : ∃ j, r < edge f grows (j+1) :=
  ⟨r,Nat.lt_succ_self r |>.trans_le ((strict f grows).id_le _)⟩

def index (r : ℕ) := Nat.find (above f grows r)

theorem bounds (r : ℕ) : edge f grows (index f grows r) ≤ r ∧ r < edge f grows (index f grows r+1) := by
  refine ⟨?_,Nat.find_spec (above f grows r)⟩
  cases eq : index f grows r with
  | zero => exact Nat.zero_le _
  | succ j => exact le_of_not_gt (Nat.find_min (above f grows r) (show j < index f grows r by omega))

private theorem monotone : Monotone (index f grows) := by
  intro a b le
  apply Nat.find_min' (above f grows a)
  exact le.trans_lt (bounds f grows b).2

/-- The finite shell containing a given radius. -/
def region (d j : ℕ) := (centeredCube d (edge f grows (j+1))).filter
    (fun x => index f grows (radius x)=j)

theorem mem_region {d j} {x : Lattice d} :
    x ∈ region f grows d j ↔ index f grows (radius x)=j := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro eq
    refine Finset.mem_filter.mpr ⟨?_,eq⟩
    have lt := (bounds f grows (radius x)).2
    rw [eq] at lt
    have h (i) := (Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)).trans lt.le
    apply Finset.mem_Icc.mpr
    exact ⟨fun i => by have := h i; dsimp; omega,fun i => by have := h i; dsimp; omega⟩

/-- An interval of radii of length at most V meets at most f(V)+2
shells whenever f(V) is nonnegative. -/
theorem count_bands {a b V : ℕ} (dist : b ≤ a+V) (pos : 0 ≤ f V) :
    ((Finset.Icc (index f grows a) (index f grows b)).card:ℝ) ≤ f V+2 := by
  let A := index f grows a; let B := index f grows b
  rw [Nat.card_Icc]
  change ((B+1-A:ℕ):ℝ) ≤ f V+2
  by_cases two : A+2 ≤ B
  · let j := B-1
    have eq : B=j+1 := by dsimp [j]; omega
    have alow : a < edge f grows j := (bounds f grows a).2.trans_le
      ((strict f grows).monotone (show A+1 ≤ j by dsimp [j]; omega))
    have high : edge f grows (j+1) ≤ b := by rw [←eq]; exact (bounds f grows b).1
    change edge f grows j+cutoff f grows j+1 ≤ b at high
    have fj := cutoff_spec f grows j V (by omega)
    have small : ((B+1-A:ℕ):ℝ) ≤ (j:ℝ)+2 := by exact_mod_cast (show B+1-A ≤ j+2 by omega)
    linarith
  · have small : ((B+1-A:ℕ):ℝ) ≤ 2 := by exact_mod_cast (show B+1-A ≤ 2 by omega)
    linarith

private theorem radius_gap {d} {l u x y : Lattice d} (widths : ∀ i, l i < u i)
    (hx : x ∈ Finset.Icc l u) (hy : y ∈ Finset.Icc l u) :
    radius x ≤ radius y + geometricVolume l u := by
  apply Finset.sup_le
  intro j _
  have lx := (Finset.mem_Icc.mp hx).1 j
  have ux := (Finset.mem_Icc.mp hx).2 j
  have ly := (Finset.mem_Icc.mp hy).1 j
  have uy := (Finset.mem_Icc.mp hy).2 j
  have w : (u j-l j).toNat ≤ geometricVolume l u := Finset.single_le_prod'
    (f := fun i => (u i-l i).toNat)
    (fun i _ => by change 1 ≤ (u i-l i).toNat; have h := widths i; omega) (Finset.mem_univ j)
  have r : (y j).natAbs ≤ radius y := Finset.le_sup (f:=fun i => (y i).natAbs) (Finset.mem_univ j)
  change l j ≤ x j at lx; change x j ≤ u j at ux
  change l j ≤ y j at ly; change y j ≤ u j at uy
  omega

/-- Cover all points of every translated rectangular test using the
same finite-shell partition. The bound involves only the tested volume. -/
theorem rectangle_cover {d} (l u : Lattice d) (widths : ∀ i, l i < u i)
    (pos : 0 ≤ f (geometricVolume l u)) :
    ∃ J : Finset ℕ, (J.card:ℝ) ≤ f (geometricVolume l u)+2 ∧
      ∀ x ∈ Finset.Icc l u, index f grows (radius x) ∈ J := by
  let S := (Finset.Icc l u).image radius
  have ne : S.Nonempty := ⟨_,Finset.mem_image.mpr ⟨l,Finset.mem_Icc.mpr ⟨le_rfl,fun i => (widths i).le⟩,rfl⟩⟩
  obtain ⟨x,hx,xeq⟩ := Finset.mem_image.mp (S.max'_mem ne)
  obtain ⟨y,hy,yeq⟩ := Finset.mem_image.mp (S.min'_mem ne)
  refine ⟨Finset.Icc (index f grows (S.min' ne)) (index f grows (S.max' ne)),
    count_bands f grows (by rw [←xeq,←yeq]; exact radius_gap widths hx hy) pos,?_⟩
  intro z hz
  have mem : radius z ∈ S := Finset.mem_image.mpr ⟨z,hz,rfl⟩
  exact Finset.mem_Icc.mpr ⟨monotone f grows (S.min'_le _ mem),monotone f grows (S.le_max' _ mem)⟩

end
end GenLimit.KleinbergWei.Banach.FilterShells
