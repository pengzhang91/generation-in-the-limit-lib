import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardPermutations

/-! Simulate a global generator during an uninterrupted permutation of a
fresh board. Every generated word in that board is charged to a local move. -/
namespace GenLimit.KleinbergWei.Banach.BoardSimulation
open Set Finset BoardPermutations
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V]

def released (A : List V → V) (p : List V) :=
  (Finset.range (p.length+1)).image fun j => A (p.take j)

theorem mem_released {A : List V → V} {p : List V} {v : V} :
    v ∈ released A p ↔ ∃ j ≤ p.length, A (p.take j) = v := by simp [released,Nat.lt_succ_iff]

private theorem released_push (A : List V → V) (p : List V) (v : V) :
    released A (p++[v]) = insert (A (p++[v])) (released A p) := by
  ext y
  rw [mem_released,Finset.mem_insert,mem_released]
  constructor
  · rintro ⟨j,le,hit⟩
    by_cases early : j ≤ p.length
    · exact Or.inr ⟨j,early,by rwa [List.take_append_of_le_length early] at hit⟩
    · have last : j=(p++[v]).length := by simp at le ⊢; omega
      exact Or.inl (by rw [last,List.take_length] at hit; exact hit.symm)
  · rintro (rfl | ⟨j,le,hit⟩)
    · exact ⟨_,le_rfl,by rw [List.take_length]⟩
    · exact ⟨j,by simp; omega,by rwa [List.take_append_of_le_length le]⟩

def simulate (D : Finset ℕ) (embed : ℕ → V) (A : List V → V) (p : List V) : Move :=
  fun h x => if w : ∃ y, x ∈ D ∧ y ∈ D ∧ y ∉ h++[x] ∧
      embed y = A (p++(h++[x]).map embed) then some w.choose else none

omit [DecidableEq V] in
theorem safe (D : Finset ℕ) (embed : ℕ → V) (A : List V → V) (p : List V) :
    BoardPermutations.Legal D (simulate D embed A p) := by
  intro h x y hit
  unfold simulate at hit
  split at hit
  next ex => obtain rfl := Option.some.inj hit; exact ⟨ex.choose_spec.1,ex.choose_spec.2.1,ex.choose_spec.2.2.1⟩
  next => contradiction

theorem recorded (D : Finset ℕ) (embed : ℕ → V) (inject : Function.Injective embed)
    (A : List V → V) (p : List V) (unused : ∀ y ∈ D, embed y ∉ released A p)
    (h : List ℕ) (inside : ∀ x ∈ h, x ∈ D)
    (fresh : ∀ k, k <+: h → A (p++k.map embed) ∉ p++k.map embed)
    {y : ℕ} (inD : y ∈ D) (seen : embed y ∈ released A (p++h.map embed)) :
    y ∈ earned (simulate D embed A p) h := by
  induction h using List.reverseRecOn with
  | nil => exact (unused y inD (by simpa using seen)).elim
  | append_singleton h x ih =>
    have shorter : h <+: h++[x] := List.prefix_append ..
    rw [List.map_append,List.map_singleton,←List.append_assoc,released_push] at seen
    rcases Finset.mem_insert.mp seen with latest | old
    · have eq : embed y = A (p++(h++[x]).map embed) := by simpa [List.append_assoc] using latest
      have notSeen := fresh _ (List.prefix_refl _)
      have clear : y ∉ h++[x] := fun hy => notSeen (eq ▸ List.mem_append_right _ (List.mem_map_of_mem hy))
      have ex : ∃ z, x ∈ D ∧ z ∈ D ∧ z ∉ h++[x] ∧ embed z = A (p++(h++[x]).map embed) :=
        ⟨y,inside x (by simp),inD,clear,eq⟩
      apply earned_push.mpr
      right
      rw [simulate,dif_pos ex]
      exact congrArg some (inject (ex.choose_spec.2.2.2.trans eq.symm))
    · exact earned_mono _ shorter (ih (fun x hx => inside x (shorter.subset hx))
        (fun k hk => fresh k (hk.trans shorter)) old)

end
end GenLimit.KleinbergWei.Banach.BoardSimulation
