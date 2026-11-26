import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.RowFamily

/-! # Paths that either advance along one row or start the next row -/
namespace GenLimit.AgnosticLanguage.RowFamily
open Filter
open scoped Classical
noncomputable section

def move (switch : Bool) (u : ℕ × ℕ) : ℕ × ℕ :=
  if switch then (u.1+1,0) else (u.1,u.2+1)

structure Walk where
  pos : ℕ → ℕ × ℕ
  switch : ℕ → Bool
  first : pos 0 = (0,0)
  step : ∀ k, pos (k+1) = move (switch k) (pos k)

def Walk.word (w : Walk) (k : ℕ) := cell (w.pos k).1 (w.pos k).2
def Walk.past (w : Walk) (k : ℕ) : Set ℕ := {x | ∃ t ≤ k, w.word t = x}

private theorem Walk.rowsMono (w : Walk) : Monotone (fun k ↦ (w.pos k).1) :=
  monotone_nat_of_le_succ fun k ↦ by rw [w.step]; cases w.switch k <;> simp [move]

private theorem Walk.columns (w : Walk) {t k : ℕ} (ht : t ≤ k) (he : (w.pos t).1 = (w.pos k).1) :
    (w.pos t).2 ≤ (w.pos k).2 := by
  induction k,ht using Nat.le_induction with
  | base => exact le_rfl
  | succ k ht ih =>
    have hr := w.rowsMono ht
    rw [w.step] at he ⊢
    cases h : w.switch k <;> simp [move,h] at he ⊢
    · exact (ih he).trans (Nat.le_succ _)
    · change (w.pos t).1 ≤ (w.pos k).1 at hr; omega

theorem Walk.no_return (w : Walk) {k} (hs : w.switch k = true) :
    Disjoint (Set.range w.word) (beyond (w.pos k).1 (w.pos k).2) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨t,rfl⟩ ⟨l,hl,he⟩
  obtain ⟨hr,hc⟩ := cell_inj he
  by_cases ht : t ≤ k
  · exact (Nat.not_lt_of_ge (w.columns ht hr.symm)) (hc ▸ hl)
  · have h := w.rowsMono (Nat.succ_le_of_lt (Nat.lt_of_not_ge ht))
    change (w.pos (k+1)).1 ≤ (w.pos t).1 at h
    rw [w.step] at h
    simp [move,hs] at h
    omega

theorem Walk.stay_pos (w : Walk) {k} (hs : ∀ m ≥ k, w.switch m = false) (l : ℕ) :
    w.pos (k+l) = ((w.pos k).1,(w.pos k).2+l) := by
  induction l with
  | zero => simp
  | succ l ih => rw [Nat.add_succ,w.step,hs _ (Nat.le_add_right ..),move]; simp [ih,Nat.add_assoc]

theorem Walk.stay_support (w : Walk) {k} (hs : ∀ m ≥ k, w.switch m = false) :
    Set.range w.word ⊆ w.past k ∪ beyond (w.pos k).1 (w.pos k).2 := by
  rintro _ ⟨t,rfl⟩
  by_cases ht : t ≤ k
  · exact Or.inl ⟨t,ht,rfl⟩
  · obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge ht)
    exact Or.inr ⟨(w.pos k).2+l,by omega,by simp [Walk.word,w.stay_pos hs]⟩

private theorem Walk.earlier_in_row (w : Walk) (k) :
    ∀ j ≤ (w.pos k).2, cell (w.pos k).1 j ∈ Set.range w.word := by
  induction k with
  | zero =>
    intro j hj; rw [w.first] at hj ⊢; refine ⟨0,?_⟩; simp_all [Walk.word,w.first]
  | succ k ih =>
    intro j hj
    by_cases he : j = (w.pos (k+1)).2
    · exact ⟨k+1,by rw [he]; rfl⟩
    rw [w.step] at he hj ⊢
    cases h : w.switch k <;> simp [move,h] at he hj ⊢
    · exact ih j (by omega)
    · omega

private theorem Walk.earlier_starts (w : Walk) (k) :
    ∀ i ≤ (w.pos k).1, cell i 0 ∈ Set.range w.word := by
  induction k with
  | zero =>
    intro i hi; rw [w.first] at hi; obtain rfl : i = 0 := by exact Nat.eq_zero_of_le_zero hi
    exact ⟨0,by simp [Walk.word,w.first]⟩
  | succ k ih =>
    intro i hi
    by_cases he : i ≤ (w.pos k).1
    · exact ih i he
    refine ⟨k+1,?_⟩
    rw [Walk.word,w.step]; rw [w.step] at hi
    cases h : w.switch k <;> simp [move,h] at hi ⊢
    · exact False.elim (he hi)
    · congr 1; omega

theorem Walk.contains_language (w : Walk) : ∃ i, family i ⊆ Set.range w.word := by
  by_cases hf : ∃ᶠ k : ℕ in atTop, w.switch k = true
  · refine ⟨0,?_⟩
    rintro _ ⟨i,rfl⟩
    have unbounded (i) : ∃ k, i ≤ (w.pos k).1 := by
      induction i with
      | zero => exact ⟨0,Nat.zero_le _⟩
      | succ i ih =>
        obtain ⟨k,hk⟩ := ih
        obtain ⟨t,ht,hb⟩ := frequently_atTop.mp hf k
        have hm := w.rowsMono ht
        refine ⟨t+1,?_⟩
        rw [w.step]; simpa [move,hb] using Nat.succ_le_succ (hk.trans hm)
    obtain ⟨k,hk⟩ := unbounded i
    exact w.earlier_starts k i hk
  · rw [Filter.not_frequently] at hf
    obtain ⟨k,hk⟩ := eventually_atTop.mp hf
    have stay (t) (ht : k ≤ t) : w.switch t = false := by simpa using hk t ht
    refine ⟨2*(w.pos k).1+1,?_⟩
    rw [includes_row]
    rintro _ ⟨j,rfl⟩
    rcases le_total j (w.pos k).2 with h | h
    · exact w.earlier_in_row k j h
    · obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le h
      exact ⟨k+l,by simp [Walk.word,w.stay_pos stay]⟩

end
end GenLimit.AgnosticLanguage.RowFamily
