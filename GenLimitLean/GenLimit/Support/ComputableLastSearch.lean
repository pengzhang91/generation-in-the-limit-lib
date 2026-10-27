import GenLimit.Support.ComputableSearch

/-! # Computable last-success search over a finite initial segment -/

namespace GenLimit.Support

def lastTrue {α : Type*} (p : α → ℕ → Bool) (a : α) (n : ℕ) : Option ℕ :=
  Nat.rec none (fun k previous => if p a k then some k else previous) n

@[simp] theorem lastTrue_zero {α : Type*} (p : α → ℕ → Bool) (a : α) : lastTrue p a 0 = none := rfl

theorem lastTrue_succ {α : Type*} (p : α → ℕ → Bool) (a : α) (n : ℕ) :
    lastTrue p a (n + 1) = if p a n then some n else lastTrue p a n := rfl

theorem lastTrue_computable {α : Type*} [Primcodable α] {p : α → ℕ → Bool}
    (hp : Computable₂ p) : Computable₂ (lastTrue p) := by
  let Input := (α × ℕ) × (ℕ × Option ℕ)
  have hc : Computable (fun z : Input => p z.1.1 z.2.1) :=
    hp.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hy : Computable (fun z : Input => some z.2.1) :=
    Computable.option_some.comp (Computable.fst.comp Computable.snd)
  have hn : Computable (fun z : Input => z.2.2) := Computable.snd.comp Computable.snd
  have hs : Computable (fun z : Input => if p z.1.1 z.2.1 then some z.2.1 else z.2.2) :=
    (Computable.cond hc hy hn).of_eq (fun z => by cases p z.1.1 z.2.1 <;> rfl)
  exact (Computable.nat_rec Computable.snd (Computable.const none) hs.to₂).to₂

theorem lastTrue_spec {α : Type*} {p : α → ℕ → Bool} {a : α} {n i : ℕ}
    (h : lastTrue p a n = some i) : i < n ∧ p a i = true := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    rw [lastTrue_succ] at h
    by_cases hp : p a n = true
    · simp only [hp, if_true, Option.some.injEq] at h
      subst i
      exact ⟨Nat.lt_succ_self n, hp⟩
    · rw [if_neg hp] at h
      exact ⟨(ih h).1.trans (Nat.lt_succ_self n), (ih h).2⟩

theorem lastTrue_eq_none_iff {α : Type*} (p : α → ℕ → Bool) (a : α) (n : ℕ) :
    lastTrue p a n = none ↔ ∀ i < n, p a i = false := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lastTrue_succ]
    by_cases hp : p a n = true
    · simp only [hp, if_true, reduceCtorEq, false_iff]
      intro h
      have hn := h n (Nat.lt_succ_self n)
      simp [hp] at hn
    · rw [if_neg hp, ih]
      constructor
      · intro h i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h i hi
        · exact Bool.eq_false_of_not_eq_true hp
      · intro h i hi
        exact h i (Nat.lt.step hi)

theorem lastTrue_ge_of_true {α : Type*} {p : α → ℕ → Bool} {a : α} {n i k : ℕ}
    (h : lastTrue p a n = some i) (hk : k < n) (hpk : p a k = true) : k ≤ i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [lastTrue_succ] at h
    by_cases hp : p a n = true
    · simp only [hp, if_true, Option.some.injEq] at h
      omega
    · rw [if_neg hp] at h
      have hkn : k < n := by
        by_contra hn
        have he : k = n := by omega
        exact hp (he ▸ hpk)
      exact ih h hkn

end GenLimit.Support
