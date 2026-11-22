import Mathlib.Computability.Primrec

/-! # Primitive recursive word numbering for Appendix I

Number the letters of a nonempty finite alphabet from zero through `k`.
In bijective base `k+1` the empty word is zero. The unary alphabet is
included. Both directions of Gold's word/number convention preserve
primitive recursiveness.
-/

namespace GenLimit.Gold.Effective.Words

def number (k : ℕ) : List (Fin (k+1)) → ℕ :=
  List.foldr (fun a r => (a.val + (k+1)*r) + 1) 0

def word (k : ℕ) : ℕ → List (Fin (k+1))
  | 0 => []
  | n+1 => ⟨n % (k+1), Nat.mod_lt _ (by omega)⟩ :: word k (n / (k+1))
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self ..)

theorem number_word (k n : ℕ) : number k (word k n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [word, number]
    | succ n =>
      rw [word]
      change n % (k+1) + (k+1) * number k (word k (n/(k+1))) + 1 = n+1
      rw [ih _ (Nat.lt_succ_of_le (Nat.div_le_self ..)), Nat.mod_add_div]

theorem word_number (k : ℕ) (s : List (Fin (k+1))) : word k (number k s) = s := by
  induction s with
  | nil => simp [number, word]
  | cons a s ih =>
    change word k ((a.val + (k+1) * number k s) + 1) = _
    rw [word]
    simp [Nat.add_mul_div_left, Nat.mod_eq_of_lt a.isLt, Nat.div_eq_of_lt a.isLt, ih]

theorem number_prim (k : ℕ) : Primrec (number k) :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    ((Primrec.succ.comp (Primrec.nat_add.comp (Primrec.fin_val.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.const (k+1)) (Primrec.snd.comp Primrec.snd)))).to₂)

theorem word_prim (k : ℕ) : Primrec (word k) := by
  let W := List (Fin (k+1))
  let digit (n : ℕ) : Fin (k+1) := ⟨n % (k+1), Nat.mod_lt _ (by omega)⟩
  have hd : Primrec digit := Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const _))
  let extend (xs : List W) := let n := xs.length.pred
    bif xs.length == 0 then some ([] : W) else
      (xs[n / (k+1)]?).map (List.cons (digit n))
  have n := Primrec.pred.comp (Primrec.list_length (α := W))
  have he : Primrec extend := (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond
    (Primrec.const (some [])) (Primrec.option_map
      (Primrec.list_getElem?.comp Primrec.id (Primrec.nat_div.comp n (Primrec.const (k+1))))
      ((Primrec.list_cons.comp ((hd.comp n).comp Primrec.fst) Primrec.snd).to₂))
  have total := Primrec.nat_strong_rec (fun (_ : Unit) => word k)
    (g := fun _ xs => extend xs) (he.comp Primrec.snd).to₂ (by
      intro _ n
      cases n with
      | zero => simp [extend, word]
      | succ n =>
        have hlt : n / (k+1) < n+1 := Nat.lt_succ_of_le (Nat.div_le_self ..)
        simp [extend, digit, word, hlt])
  exact total.comp (Primrec.const ()) Primrec.id

end GenLimit.Gold.Effective.Words
