import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! An ordered stage with at least k·m vertices either has m red
vertices or has k consecutive blue vertices. Keeping the order is
essential when the blue block is cut out by a horizontal rectangle. -/
namespace GenLimit.KleinbergWei.Banach.Stages
open scoped Classical
noncomputable section

theorem row_alternative {α : Type*} [LinearOrder α] (S : Finset α) (color : α → Bool)
    {k m : ℕ} (hk : 0 < k) (cap : m*k ≤ S.card) :
    m ≤ (S.filter fun x => color x = true).card ∨
      ∃ a b : α, k ≤ (S.filter fun x => a ≤ x ∧ x ≤ b).card ∧
        ∀ x ∈ S, a ≤ x → x ≤ b → color x = false := by
  let e := S.orderEmbOfFin rfl
  let rank (j : Fin m) (i : Fin k) : Fin S.card :=
    ⟨j.val*k+i.val,by have := Nat.mul_le_mul_right k j.isLt; rw [Nat.succ_mul] at this; omega⟩
  let val (j : Fin m) (i : Fin k) := e (rank j i)
  have inj : ∀ {j j' : Fin m} {i i' : Fin k}, val j i = val j' i' → j = j' ∧ i = i' := by
    intro j j' i i' h
    have eq := congrArg Fin.val (e.injective h)
    change j.val*k+i.val=j'.val*k+i'.val at eq
    have first : j.val = j'.val := by
      by_contra ne; rcases lt_or_gt_of_ne ne with h | h
      · have := Nat.mul_le_mul_right k h; rw [Nat.succ_mul] at this; omega
      · have := Nat.mul_le_mul_right k h; rw [Nat.succ_mul] at this; omega
    exact ⟨Fin.ext first,Fin.ext (by rw [first] at eq; omega)⟩
  have mem (j : Fin m) (i : Fin k) : val j i ∈ S := Finset.orderEmbOfFin_mem ..
  by_cases all : ∀ j, ∃ i, color (val j i) = true
  · left
    let red := S.filter fun x => color x = true
    let pick (j : Fin m) : red := ⟨val j (all j).choose,Finset.mem_filter.mpr ⟨mem ..,(all j).choose_spec⟩⟩
    have inject : Function.Injective pick := by
      intro j l h
      exact (@inj j l (all j).choose (all l).choose (congrArg (fun x : red => x.val) h)).1
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective pick inject
  · right
    push_neg at all
    obtain ⟨j,blue⟩ := all
    let first : Fin k := ⟨0,hk⟩
    let last : Fin k := ⟨k-1,by omega⟩
    let a := val j first
    let b := val j last
    let block := S.filter fun x => a ≤ x ∧ x ≤ b
    have bounds (i : Fin k) : a ≤ val j i ∧ val j i ≤ b := by
      refine ⟨e.monotone ?_,e.monotone ?_⟩
      · change j.val*k+0 ≤ j.val*k+i.val; omega
      · change j.val*k+i.val ≤ j.val*k+(k-1); omega
    let place (i : Fin k) : block := ⟨val j i,Finset.mem_filter.mpr ⟨mem ..,bounds i⟩⟩
    have inject : Function.Injective place := by
      intro i l h
      exact (@inj j j i l (congrArg (fun x : block => x.val) h)).2
    refine ⟨a,b,by simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective place inject,?_⟩
    intro x hx lower upper
    obtain ⟨n,rfl⟩ : x ∈ Set.range e := by simpa [e] using hx
    have lo : j.val*k ≤ n.val := by simpa [a,val,rank,first] using (e.le_iff_le.mp lower)
    have hi : n.val ≤ j.val*k+(k-1) := e.le_iff_le.mp upper
    let i : Fin k := ⟨n.val-j.val*k,by omega⟩
    have same : rank j i = n := Fin.ext (by dsimp [rank,i]; omega)
    simpa [val,same] using blue i

end
end GenLimit.KleinbergWei.Banach.Stages
