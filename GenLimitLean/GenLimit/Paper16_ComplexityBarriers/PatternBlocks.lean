import GenLimit.Paper16_ComplexityBarriers.Threshold
import Mathlib.Data.List.OfFn

/-! # The binary word equation used in Theorem 6.1

The two templates have four variable occurrences each. If their values
agree, the value of the variable has length below nine. A longer value
would conjugate two nine-letter constants with different letter counts. -/
namespace GenLimit.ComplexityBarriers.Patterns
open List
abbrev Pattern := List (Bool ⊕ ℕ)

def eval (v : ℕ → List Bool) (p : Pattern) : List Bool :=
  p.flatMap (Sum.elim (fun a ↦ [a]) v)

def language (p : Pattern) : Set (List Bool) :=
  {w | ∃ v : ℕ → List Bool, (∀ i, v i ≠ []) ∧ eval v p = w}

private def pre : List Bool := [false,true,false,false,true,true,false,true,false]
private def suf : List Bool := [true,false,true,false,false,true,true,false,true]
private def midQ : List Bool := [false,false,true,true,false,true,false]
private def midR : List Bool := [true,false,true,false,false,true,true]

def qword (x : List Bool) := x ++ [false] ++ x ++ [true] ++ x ++ midQ ++ x ++ suf
def rword (x : List Bool) := pre ++ x ++ midR ++ x ++ [false] ++ x ++ [true] ++ x

def qpat (i : ℕ) : Pattern :=
  [.inr i,.inl false,.inr i,.inl true,.inr i] ++ midQ.map Sum.inl ++ [.inr i] ++ suf.map Sum.inl

def rpat (i : ℕ) : Pattern :=
  pre.map Sum.inl ++ [.inr i] ++ midR.map Sum.inl ++ [.inr i,.inl false,.inr i,.inl true,.inr i]

theorem qpat_length (i : ℕ) : (qpat i).length = 22 := rfl
theorem rpat_length (i : ℕ) : (rpat i).length = 22 := rfl

@[simp] theorem eval_qpat (v : ℕ → List Bool) (i : ℕ) : eval v (qpat i) = qword (v i) := by
  simp [eval,qpat,qword,suf,midQ,List.append_assoc]
@[simp] theorem eval_rpat (v : ℕ → List Bool) (i : ℕ) : eval v (rpat i) = rword (v i) := by
  simp [eval,rpat,rword,pre,midR,List.append_assoc]

theorem qword_length (x : List Bool) : (qword x).length = 4*x.length+18 := by
  simp [qword,midQ,suf]; omega
theorem rword_length (x : List Bool) : (rword x).length = 4*x.length+18 := by
  simp [rword,midR,pre]; omega

theorem bounded_solution (x : List Bool) (h : qword x = rword x) : x.length < 9 := by
  by_contra! hn
  have hxp : x <+: qword x := by simp [qword,append_assoc]
  have hrp : pre ++ x <+: rword x := by
    refine ⟨midR ++ x ++ [false] ++ x ++ [true] ++ x,?_⟩
    simp [rword,List.append_assoc]
  have hxs : x <:+ rword x := suffix_append ..
  have hqs : suf <:+ qword x := suffix_append ..
  have hp := prefix_of_prefix_length_le (h ▸ hxp) hrp (by simp)
  have hs := suffix_of_suffix_length_le (h ▸ hqs) hxs (show suf.length ≤ x.length from hn)
  obtain ⟨u,hu⟩ := hp
  have hlen := congrArg List.length hu
  simp only [List.length_append] at hlen
  have hul : u.length = suf.length := by change u.length = 9; change x.length + u.length = 9 + x.length at hlen; omega
  have hup : u <:+ pre ++ x := ⟨x,hu⟩
  have hsp : suf <:+ pre ++ x := hs.trans (suffix_append ..)
  have he := (suffix_of_suffix_length_le hup hsp hul.le).eq_of_length hul
  have counts := congrArg (List.count false) hu
  rw [he] at counts
  simp [List.count_append,pre,suf] at counts

def choice : Bool → List Bool
  | false => [false,true]
  | true => [false,true,false,false,true,true,false,true]

theorem choice_nonempty (b) : choice b ≠ [] := by cases b <;> decide
theorem choice_solution (b) : qword (choice b) = rword (choice b) := by cases b <;> decide

def encode (bits : List Bool) := bits.flatMap (fun b ↦ qword (choice b))

private theorem distinguish {b c : Bool} {u v : List Bool}
    (h : qword (choice b) ++ u = qword (choice c) ++ v) : b = c := by
  have hh := congrArg (List.take 12) h
  have hlen (j) : 12 ≤ (qword (choice j)).length := by cases j <;> decide
  rw [take_append_of_le_length (hlen b),take_append_of_le_length (hlen c)] at hh
  cases b <;> cases c <;> first | rfl | contradiction

theorem encode_injective : Function.Injective encode := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v => cases b <;> simp [encode,qword,choice] at h
  | cons b u ih =>
    intro v h
    cases v with
    | nil => cases b <;> simp [encode,qword,choice] at h
    | cons c v =>
      change qword (choice b) ++ encode u = qword (choice c) ++ encode v at h
      obtain rfl := distinguish h
      exact congrArg (List.cons b) (ih (List.append_cancel_left h))

theorem split_eq {a b c d : List α} (h : a ++ b = c ++ d) (hl : a.length = c.length) :
    a = c ∧ b = d := by
  constructor
  · simpa only [List.take_left,List.take_left' hl.symm] using congrArg (List.take a.length) h
  · simpa only [List.drop_left,List.drop_left' hl.symm] using congrArg (List.drop a.length) h

theorem same_block_lengths (is : List ℕ) (v : ℕ → List Bool) :
    (is.flatMap (fun i ↦ qword (v i))).length = (is.flatMap (fun i ↦ rword (v i))).length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [qword_length,rword_length,ih]

theorem small_half (is : List ℕ) (v : ℕ → List Bool)
    (h : is.flatMap (fun i ↦ qword (v i)) = is.flatMap (fun i ↦ rword (v i))) :
    (is.flatMap (fun i ↦ qword (v i))).length ≤ 50*is.length := by
  induction is with
  | nil => simp
  | cons i is ih =>
    obtain ⟨he,hs⟩ := split_eq h ((qword_length _).trans (rword_length _).symm)
    have hb := bounded_solution _ he
    simp only [flatMap_cons,length_append,length_cons,qword_length]
    have := ih hs
    omega

end GenLimit.ComplexityBarriers.Patterns
