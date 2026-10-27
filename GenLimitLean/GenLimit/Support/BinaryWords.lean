import Mathlib.Computability.Primrec

/-! # Effective enumeration of the finite Boolean words of a given length -/

namespace GenLimit.Support

def binaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (binaryWords n).flatMap (fun xs => [false :: xs, true :: xs])

theorem mem_binaryWords (xs : List Bool) (n : ℕ) : xs ∈ binaryWords n ↔ xs.length = n := by
  induction n generalizing xs with
  | zero => simp [binaryWords]
  | succ n ih =>
    cases xs with
    | nil => simp [binaryWords]
    | cons b xs =>
      cases b <;> simp [binaryWords, ih]

theorem binaryWords_primrec : Primrec binaryWords := by
  have hs : Primrec (fun xs : List Bool => [false :: xs, true :: xs]) :=
    Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.id)
      (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.id) (Primrec.const []))
  have hstep : Primrec₂ (fun (_u : Unit) (r : ℕ × List (List Bool)) =>
      r.2.flatMap (fun ys => [false :: ys, true :: ys])) :=
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) (hs.comp Primrec.snd).to₂).to₂
  have hrec : Primrec₂ (fun (_u : Unit) n => binaryWords n) := by
    apply (Primrec.nat_rec (Primrec.const ([[]] : List (List Bool))) hstep).of_eq
    intro u n
    induction n with
    | zero => rfl
    | succ n ih => simp only [binaryWords, ih]
  exact hrec.comp (Primrec.const ()) Primrec.id

end GenLimit.Support
