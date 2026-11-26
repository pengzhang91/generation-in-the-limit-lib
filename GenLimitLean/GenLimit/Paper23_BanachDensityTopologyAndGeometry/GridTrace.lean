import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleLanguage
import Mathlib.Data.Finset.Preimage

/-! A physical rectangle pulls back to one (possibly thin) integer rectangle
under arbitrary strictly increasing recodings of the separate coordinates. -/
namespace GenLimit.KleinbergWei.Banach.GridTrace
open Finset Set
open scoped Classical
noncomputable section

def encode {d} (φ : Fin d → ℤ → ℤ) (x : Lattice d) : Lattice d := fun j => φ j (x j)

theorem injective {d} {φ : Fin d → ℤ → ℤ} (inc : ∀ j, StrictMono (φ j)) :
    Function.Injective (encode φ) := by
  intro x y eq
  exact funext fun j => (inc j).injective (congrFun eq j)

/-- All subsets on a common grid share the same pullback rectangle.
Its number of lattice sites equals the number of physical grid points. -/
theorem rectangle {d} (φ : Fin d → ℤ → ℤ) (inc : ∀ j, StrictMono (φ j))
    {l u : Lattice d} {z : Lattice d} (witness : encode φ z ∈ Finset.Icc l u) :
    ∃ a b : Lattice d, a ≤ b ∧
      (∀ S : Set (Lattice d), (Rectangles.box (encode φ '' S) l u).card = (Rectangles.box S a b).card) ∧
      (Rectangles.box (Set.range (encode φ)) l u).card = (Finset.Icc a b).card := by
  let W (j : Fin d) := (Finset.Icc (l j) (u j)).preimage (φ j) (inc j).injective.injOn
  have mem (j) (n : ℤ) : n ∈ W j ↔ l j ≤ φ j n ∧ φ j n ≤ u j := by simp [W]
  have ne (j) : (W j).Nonempty := ⟨z j,(mem j _).2 ⟨(Finset.mem_Icc.mp witness).1 j,(Finset.mem_Icc.mp witness).2 j⟩⟩
  let a : Lattice d := fun j => (W j).min' (ne j)
  let b : Lattice d := fun j => (W j).max' (ne j)
  have iffBox (x : Lattice d) : encode φ x ∈ Finset.Icc l u ↔ x ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc,Finset.mem_Icc]
    constructor
    · rintro ⟨lo,hi⟩
      have hit (j) := (mem j _).mpr ⟨lo j,hi j⟩
      exact ⟨fun j => (W j).min'_le _ (hit j),fun j => (W j).le_max' _ (hit j)⟩
    · rintro ⟨lo,hi⟩
      have first (j) := (mem j _).mp ((W j).min'_mem (ne j))
      have last (j) := (mem j _).mp ((W j).max'_mem (ne j))
      exact ⟨fun j => (first j).1.trans ((inc j).monotone (lo j)),
        fun j => ((inc j).monotone (hi j)).trans (last j).2⟩
  have count (S : Set (Lattice d)) :
      (Rectangles.box (encode φ '' S) l u).card = (Rectangles.box S a b).card := by
    symm; apply Finset.card_bij (fun x _ => encode φ x)
    · intro x hx; obtain ⟨rect,h⟩ := Rectangles.mem_box.mp hx
      exact Rectangles.mem_box.mpr ⟨Finset.mem_Icc.mp ((iffBox x).2 (Finset.mem_Icc.mpr rect)),x,h,rfl⟩
    · exact fun _ _ _ _ eq => injective inc eq
    · intro y hy; obtain ⟨rect,x,h,rfl⟩ := Rectangles.mem_box.mp hy
      exact ⟨x,Rectangles.mem_box.mpr ⟨Finset.mem_Icc.mp ((iffBox x).1 (Finset.mem_Icc.mpr rect)),h⟩,rfl⟩
  refine ⟨a,b,fun j => (W j).min'_le _ ((W j).max'_mem (ne j)),count,?_⟩
  simpa [Rectangles.box] using count Set.univ

end
end GenLimit.KleinbergWei.Banach.GridTrace
