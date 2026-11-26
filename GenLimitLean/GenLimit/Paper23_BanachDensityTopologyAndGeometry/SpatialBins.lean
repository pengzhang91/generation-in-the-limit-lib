import GenLimit.Core.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! A fixed partition adapted to a countable family of infinite languages.
Bin j has at least j+1 words of each of the first j+1 languages. A fixed
additive error per bin consequently disappears in relative Banach density,
including for sparse targets. -/
namespace GenLimit.KleinbergWei.Banach
open Set
open scoped Classical
noncomputable section

structure SpatialBins (C : LanguageFamily) where
  edge : ℕ → ℕ
  zero : edge 0 = 0
  strict : StrictMono edge
  thick : ∀ j z, z ≤ j → j+1 ≤ ((Finset.Ico (edge j) (edge (j+1))).filter (· ∈ C z)).card

namespace SpatialBins

private theorem next_exists (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) (j a : ℕ) :
    ∃ b, a < b ∧ ∀ z ≤ j, j+1 ≤ ((Finset.Ico a b).filter (· ∈ C z)).card := by
  have enough (z : ℕ) := ((inf z).diff (Finset.range a).finite_toSet).exists_subset_card_eq (j+1)
  let F (z : ℕ) := (enough z).choose
  let b := max a ((Finset.range (j+1)).sup fun z => (F z).sup id)+1
  refine ⟨b,Nat.lt_succ_of_le (le_max_left ..),?_⟩
  intro z hz
  obtain ⟨subset,card⟩ := (enough z).choose_spec
  rw [←card]; apply Finset.card_le_card
  intro x hx
  obtain ⟨inK,low⟩ := subset hx
  have l : a ≤ x := by simpa using low
  have u : x ≤ (F z).sup id := Finset.le_sup (f:=id) hx
  have sup := Finset.le_sup (f:=fun z => (F z).sup id) (Finset.mem_range.mpr (Nat.lt_succ_of_le hz))
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨l,Nat.lt_succ_of_le ((u.trans sup).trans (le_max_right ..))⟩,inK⟩

def build (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) : SpatialBins C :=
  let edge := Nat.rec 0 fun j a => (next_exists C inf j a).choose
  { edge := edge, zero := rfl
    strict := strictMono_nat_of_lt_succ fun j => (next_exists C inf j (edge j)).choose_spec.1
    thick := fun j => (next_exists C inf j (edge j)).choose_spec.2 }

variable {C : LanguageFamily} (B : SpatialBins C)

def cell (j : ℕ) := Finset.Ico (B.edge j) (B.edge (j+1))

private theorem exists_edge (x : ℕ) : ∃ j, x < B.edge (j+1) :=
  ⟨x,(Nat.lt_succ_self x).trans_le (B.strict.id_le _)⟩

def number (x : ℕ) := Nat.find (B.exists_edge x)

theorem in_cell (x : ℕ) : x ∈ B.cell (B.number x) := by
  refine Finset.mem_Ico.mpr ⟨?_,Nat.find_spec (B.exists_edge x)⟩
  cases eq : B.number x with
  | zero => simp [B.zero]
  | succ j =>
    exact le_of_not_gt (Nat.find_min (B.exists_edge x) (show j < B.number x by omega))

theorem cell_iff {x j : ℕ} : x ∈ B.cell j ↔ B.number x = j := by
  constructor
  · intro hx; obtain ⟨l,u⟩ := Finset.mem_Ico.mp hx
    obtain ⟨lb,ub⟩ := Finset.mem_Ico.mp (B.in_cell x)
    rcases lt_trichotomy (B.number x) j with h | e | h
    · exact ((B.strict.monotone (show B.number x+1 ≤ j from h)).not_gt (l.trans_lt ub)).elim
    · exact e
    · exact ((B.strict.monotone (show j+1 ≤ B.number x from h)).not_gt (lb.trans_lt u)).elim
  · rintro rfl; exact B.in_cell x

theorem number_mono : Monotone B.number := by
  intro x y le
  obtain ⟨a,_⟩ := Finset.mem_Ico.mp (B.in_cell x)
  obtain ⟨_,b⟩ := Finset.mem_Ico.mp (B.in_cell y)
  by_contra! h
  exact ((B.strict.monotone (show B.number y+1 ≤ B.number x from h)).not_gt ((a.trans le).trans_lt b))

end SpatialBins
end
end GenLimit.KleinbergWei.Banach
