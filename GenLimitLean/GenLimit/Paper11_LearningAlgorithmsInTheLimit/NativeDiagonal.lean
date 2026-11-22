import GenLimit.Paper11_LearningAlgorithmsInTheLimit.RepresentationBudget

/-! # Characteristic examples for actual single-tape programs -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape

variable {Γ α : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] [Encodable Γ]

/-- Partial word semantics with exactly the paper's initial tape, halting
condition and contiguous-word output convention. -/
noncomputable def wordSem (ι : α ↪ Γ) (P : TuringProgram Γ) (x : List α) : Option (List α) := by
  classical
  exact if h : ∃ t y, P.runWithin t (wordIO ι) x = some y then some h.choose_spec.choose else none

theorem wordSem_of_run (ι : α ↪ Γ) {P : TuringProgram Γ} {x y : List α} {t : ℕ}
    (h : P.runWithin t (wordIO ι) x = some y) : wordSem ι P x = some y := by
  classical
  have ex : ∃ t y, P.runWithin t (wordIO ι) x = some y := ⟨t,y,h⟩
  unfold wordSem
  rw [dif_pos ex]
  have h₁ := P.runWithin_mono _ (Nat.le_max_left ex.choose t) ex.choose_spec.choose_spec
  have h₂ := P.runWithin_mono _ (Nat.le_max_right ex.choose t) h
  exact h₁.symm.trans h₂

theorem run_of_wordSem (ι : α ↪ Γ) {P : TuringProgram Γ} {x y : List α}
    (h : wordSem ι P x = some y) : ∃ t, P.runWithin t (wordIO ι) x = some y := by
  classical
  unfold wordSem at h
  split at h
  · rename_i ex
    exact ⟨_,ex.choose_spec.choose_spec.trans h⟩
  · contradiction

def wordDomain (ι : α ↪ Γ) (P : TuringProgram Γ) : Set (List α) := {x | ∃ y, wordSem ι P x = some y}

def linearTotal (ι : α ↪ Γ) (P : TuringProgram Γ) : Prop :=
  ∃ t, ∀ x : List α, ∃ y, P.runWithin (x.length+t) (wordIO ι) x = some y

/-- The budget for even one selected output is impossible. This form also
applies when an effective selector is converted to a bound on its outputs. -/
theorem no_output_bound (ι : α ↪ Γ) (noBlank : ∀ a, ι a ≠ default) (a : α)
    (A : Set (List α × O) → R) (rep : R → List α → Option (List α))
    (obs : TuringProgram Γ → List α → O) (β : TuringProgram Γ → ℕ)
    (g : Nat.Partrec.Code → ℕ) (hg : Computable g)
    (hbound : ∀ c, β (constantTeacher (ι a) c) ≤ g c) :
    ¬ (∀ P, linearTotal ι P → ∃ S : Finset (List α),
      IsCharacteristicSet A obs (wordSem ι) rep (wordDomain ι P) P (↑S : Set _) ∧
      ∀ x ∈ S, ∀ y, wordSem ι P x = some y → y.length ≤ β P) := by
  classical
  intro all
  let guess := rep (A ∅) []
  let pad := (guess.map List.length).getD 0
  obtain ⟨c,hc⟩ := MassDiagonal.constant_fixed_point g hg pad
  let P := constantTeacher (ι a) c
  have he : g c + pad + 1 ∈ c.eval 0 := by rw [hc]; exact Part.mem_some _
  obtain ⟨k,t,hk,hr⟩ := constant_runs ι noBlank a he
  let y := List.replicate k a
  have val (x : List α) : wordSem ι P x = some y := wordSem_of_run _ (hr x)
  have dom (x : List α) : x ∈ wordDomain ι P := ⟨_,val x⟩
  obtain ⟨S,hS,hβ⟩ := all P ⟨t,fun x ↦ ⟨_,hr x⟩⟩
  by_cases hn : S.Nonempty
  · obtain ⟨x,hx⟩ := hn
    have ub := (hβ x hx y (val x)).trans (hbound c)
    simp [y] at ub
    omega
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hn
    have h := hS.2 ∅ (by simp) (Set.empty_subset _) [] (dom [])
    have hg' : guess = some y := by simpa [guess,exampleSet,val] using h
    have : pad = k := by simp [pad,hg',y]
    omega

theorem no_mass_bound (ι : α ↪ Γ) (noBlank : ∀ a, ι a ≠ default) (a : α)
    (A : Set (List α × O) → R) (rep : R → List α → Option (List α))
    (obs : TuringProgram Γ → List α → O) (β : TuringProgram Γ → ℕ)
    (hb : Computable (fun n ↦ β (decodeTuringProgram n))) (cost : TuringProgram Γ → List α → ℕ)
    (pays : ∀ P x y, wordSem ι P x = some y → y.length ≤ cost P x) :
    ¬ (∀ P, linearTotal ι P → ∃ S : Finset (List α),
      IsCharacteristicSet A obs (wordSem ι) rep (wordDomain ι P) P (↑S : Set _) ∧
      ∑ x ∈ S, cost P x ≤ β P) := by
  obtain ⟨g,hg,hb'⟩ := majorant β hb (ι a)
  apply fun h ↦ no_output_bound ι noBlank a A rep obs β g hg hb' ?_
  intro P hp
  obtain ⟨S,hS,hm⟩ := h P hp
  exact ⟨S,hS,fun x hx y hy ↦ (pays P x y hy).trans
    ((Finset.single_le_sum (fun i _ ↦ Nat.zero_le (cost P i)) hx).trans hm)⟩

end GenLimit.LearningAlgorithmsLimit.NativeTape
