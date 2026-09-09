import Mathlib.Computability.Partrec

/-!
# Computable bounded search

Small paper-independent Boolean search combinators used by effective
formalizations.
-/

namespace GenLimit.Support

/-- Boolean universal quantification over `0, ..., n - 1`. -/
def boundedAll {alpha : Type*} (p : alpha → ℕ → Bool)
    (a : alpha) (n : ℕ) : Bool :=
  Nat.rec true (fun k previous => previous && p a k) n

theorem boundedAll_computable {alpha : Type*} [Primcodable alpha]
    {p : alpha → ℕ → Bool} (hp : Computable₂ p) :
    Computable₂ (boundedAll p) := by
  simpa only [boundedAll] using Computable.to₂
    (Computable.nat_rec Computable.snd (Computable.const true)
      (Computable.to₂ <|
        Primrec.and.to_comp.comp
          (Computable.snd.comp Computable.snd)
          (hp.comp
            (Computable.fst.comp Computable.fst)
            (Computable.fst.comp Computable.snd))))

theorem boundedAll_eq_true_iff {alpha : Type*}
    (p : alpha → ℕ → Bool) (a : alpha) (n : ℕ) :
    boundedAll p a n = true ↔ ∀ k < n, p a k = true := by
  induction n with
  | zero => simp [boundedAll]
  | succ n ih =>
      simp only [boundedAll] at ih ⊢
      simp only [Bool.and_eq_true]
      rw [ih]
      constructor
      · rintro ⟨hprev, hn⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | rfl
        · exact hprev k hkn
        · exact hn
      · intro h
        exact ⟨fun k hk => h k (Nat.lt.step hk),
          h n (Nat.lt_succ_self n)⟩

/-- Executable membership for lists of natural numbers. -/
def listContains (xs : List ℕ) (x : ℕ) : Bool :=
  decide (x ∈ xs)

theorem listContains_computable : Computable₂ listContains := by
  have hidx : Primrec₂ (fun xs : List ℕ => fun x : ℕ => List.idxOf x xs) :=
    Primrec.list_idxOf.comp₂ Primrec₂.right Primrec₂.left
  have hlen : Primrec₂ (fun xs : List ℕ => fun _x : ℕ => xs.length) :=
    Primrec.list_length.comp₂ Primrec₂.left
  have hlt : PrimrecRel (fun xs : List ℕ => fun x : ℕ =>
      List.idxOf x xs < xs.length) :=
    Primrec.nat_lt.comp₂ hidx hlen
  exact (hlt.decide.of_eq fun xs x => by
    simp only [List.idxOf_lt_length_iff, listContains]).to_comp

@[simp] theorem listContains_eq_true_iff (xs : List ℕ) (x : ℕ) :
    listContains xs x = true ↔ x ∈ xs := by
  simp [listContains]

/-- First index below `n` where `p` is true, if one exists. -/
def firstTrue {alpha : Type*} (p : alpha → ℕ → Bool)
    (a : alpha) (n : ℕ) : Option ℕ :=
  Nat.rec none (fun k previous =>
    match previous with
    | some i => some i
    | none => if p a k then some k else none) n

@[simp] theorem firstTrue_zero {alpha : Type*}
    (p : alpha → ℕ → Bool) (a : alpha) :
    firstTrue p a 0 = none := rfl

theorem firstTrue_succ {alpha : Type*}
    (p : alpha → ℕ → Bool) (a : alpha) (n : ℕ) :
    firstTrue p a (n + 1) =
      match firstTrue p a n with
      | some i => some i
      | none => if p a n then some n else none := by
  simp only [firstTrue]

set_option maxHeartbeats 800000 in
theorem firstTrue_computable {alpha : Type*} [Primcodable alpha]
    {p : alpha → ℕ → Bool} (hp : Computable₂ p) :
    Computable₂ (firstTrue p) := by
  have hstep : Computable₂ (fun r : alpha × ℕ => fun q : ℕ × Option ℕ =>
      match q.2 with
      | some i => some i
      | none => if p r.1 q.1 then some q.1 else none) := by
    let Input := ((alpha × ℕ) × (ℕ × Option ℕ))
    have hprevious : Computable (fun z : Input => z.2.2) :=
      Computable.snd.comp Computable.snd
    have hnone : Computable (fun z : Input =>
        if p z.1.1 z.2.1 then some z.2.1 else none) :=
      (Computable.cond
        (hp.comp
          (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd))
        (Computable.option_some.comp
          (Computable.fst.comp Computable.snd))
        (Computable.const (none : Option ℕ))).of_eq fun z => by
          cases p z.1.1 z.2.1 <;> rfl
    have hsome : Computable₂ (fun (_z : Input) (i : ℕ) => some i) :=
      Computable.to₂ (Computable.option_some.comp Computable.snd)
    exact (Computable.to₂
      (Computable.option_casesOn hprevious hnone hsome)).of_eq
        fun z => by
          rcases z with ⟨r, q⟩
          dsimp only
          cases q.2 <;> rfl
  simpa only [firstTrue] using Computable.to₂
    (Computable.nat_rec Computable.snd (Computable.const none) hstep)

theorem firstTrue_eq_none_iff {alpha : Type*}
    (p : alpha → ℕ → Bool) (a : alpha) (n : ℕ) :
    firstTrue p a n = none ↔ ∀ i < n, p a i = false := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [firstTrue_succ]
      by_cases hprev : firstTrue p a n = none
      · rw [hprev]
        have hall : ∀ i < n, p a i = false := ih.mp hprev
        constructor
        · intro hnone i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hin | rfl
          · exact hall i hin
          · by_cases hpn : p a i = true
            · simp [hpn] at hnone
            · exact Bool.eq_false_of_not_eq_true hpn
        · intro h
          have hpfalse := h n (Nat.lt_succ_self n)
          simp [hpfalse]
      · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hprev
        rw [hj]
        constructor
        · intro h
          contradiction
        · intro h
          exact False.elim
            (hprev (ih.mpr fun i hi => h i (Nat.lt.step hi)))

theorem firstTrue_spec {alpha : Type*}
    {p : alpha → ℕ → Bool} {a : alpha} {n i : ℕ}
    (h : firstTrue p a n = some i) :
    i < n ∧ p a i = true ∧ ∀ j < i, p a j = false := by
  induction n with
  | zero => simp at h
  | succ n ih =>
      rw [firstTrue_succ] at h
      by_cases hprev : firstTrue p a n = none
      · rw [hprev] at h
        by_cases hn : p a n = true
        · simp [hn] at h
          subst i
          exact ⟨Nat.lt_succ_self n, hn,
            (firstTrue_eq_none_iff p a n).mp hprev⟩
        · have hnfalse : p a n = false := Bool.eq_false_of_not_eq_true hn
          simp [hnfalse] at h
      · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hprev
        rw [hk] at h
        simp only [Option.some.injEq] at h
        subst i
        obtain ⟨hkn, hpk, hleast⟩ := ih hk
        exact ⟨Nat.lt.step hkn, hpk, hleast⟩

theorem firstTrue_le_of_true {alpha : Type*}
    {p : alpha → ℕ → Bool} {a : alpha} {n i j : ℕ}
    (hfirst : firstTrue p a n = some j)
    (_hi : i < n) (hpi : p a i = true) : j ≤ i := by
  obtain ⟨_, _, hleast⟩ := firstTrue_spec hfirst
  by_contra hnot
  have hij : i < j := Nat.lt_of_not_ge hnot
  simpa [hpi] using hleast i hij

end GenLimit.Support
