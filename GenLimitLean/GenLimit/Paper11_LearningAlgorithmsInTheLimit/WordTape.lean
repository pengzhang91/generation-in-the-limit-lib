import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TapeController

/-! # Reading the single contiguous output word on a two-sided tape -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open Turing

variable {Γ α : Type} [Inhabited Γ] [DecidableEq Γ]

private def trimEnd : List Γ → List Γ
  | [] => []
  | a::l => let t := trimEnd l; if t.isEmpty && decide (a = default) then [] else a::t

private theorem trim_blanks (l : List Γ) (n : ℕ) :
    trimEnd (l ++ List.replicate n default) = trimEnd l := by
  induction l with
  | nil =>
    simp only [List.nil_append]
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ,trimEnd,ih]
  | cons a l ih => simp only [List.cons_append,trimEnd,ih]

private theorem trim_rep (a : Γ) (ha : a ≠ default) (n : ℕ) :
    trimEnd (List.replicate n a) = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ,trimEnd,ha,ih]

private def side (l : ListBlank Γ) : List Γ :=
  l.liftOn trimEnd (by rintro a _ ⟨n,rfl⟩; exact (trim_blanks a n).symm)

private noncomputable def letter (ι : α ↪ Γ) (v : Γ) : Option α := by
  classical
  exact if h : ∃ a, ι a = v then some h.choose else none

private theorem letter_on (ι : α ↪ Γ) (a : α) : letter ι (ι a) = some a := by
  classical
  have h : ∃ b, ι b = ι a := ⟨a,rfl⟩
  exact (dif_pos h).trans (congrArg some (ι.injective h.choose_spec))

/-- Discard external blank space, then check each remaining cell against
the input/output alphabet. An internal blank or work symbol invalidates the output. -/
noncomputable def readWord (ι : α ↪ Γ) (t : Tape Γ) : Option (List α) :=
  let cells := (side t.left).reverse ++ t.head :: side t.right
  ((trimEnd (trimEnd cells).reverse).reverse).mapM (letter ι)

def initialWord (ι : α ↪ Γ) (x : List α) : TuringTape Γ :=
  ⟨[],(x.map ι).headI,(x.map ι).tail⟩

theorem initial_view (ι : α ↪ Γ) (x : List α) : view (initialWord ι x) = Tape.mk₁ (x.map ι) := rfl

noncomputable def wordIO (ι : α ↪ Γ) : TuringIO Γ (List α) (List α) :=
  ⟨default,initialWord ι,fun t ↦ readWord ι (view t)⟩

theorem read_unary (ι : α ↪ Γ) (a : α) (ha : ι a ≠ default) (n : ℕ) :
    readWord ι (Tape.mk₂ (List.replicate n (ι a)) []) = some (List.replicate n a) := by
  change ((trimEnd (trimEnd ((trimEnd (List.replicate n (ι a))).reverse ++ [default])).reverse).reverse).mapM _ = _
  rw [trim_rep _ ha,List.reverse_replicate]
  have tail := trim_blanks (List.replicate n (ι a)) 1
  change trimEnd (List.replicate n (ι a) ++ [default]) = _ at tail
  rw [tail,trim_rep _ ha,List.reverse_replicate,trim_rep _ ha,List.reverse_replicate]
  clear tail
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,List.mapM_cons,letter_on,ih]

private theorem trim_length (l : List Γ) : (trimEnd l).length ≤ l.length := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih =>
    simp only [trimEnd,List.length_cons]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ ih

private theorem decoded_length (ι : α ↪ Γ) (l : List Γ) {y : List α}
    (h : l.mapM (letter ι) = some y) : y.length = l.length := by
  induction l generalizing y with
  | nil => obtain rfl : [] = y := Option.some.inj h; rfl
  | cons a l ih =>
    simp only [List.mapM_cons] at h
    cases ha : letter ι a with
    | none => simp [ha] at h
    | some b =>
      cases ht : l.mapM (letter ι) with
      | none => simp [ha,ht] at h
      | some v =>
        obtain rfl : b::v = y := by simpa [ha,ht] using h
        simp [ih ht]

theorem output_capacity (ι : α ↪ Γ) (t : TuringTape Γ) {y} (h : readWord ι (view t) = some y) :
    y.length ≤ t.left.length + 1 + t.right.length := by
  let cells := (trimEnd t.left).reverse ++ t.scanned :: trimEnd t.right
  have len := decoded_length ι ((trimEnd (trimEnd cells).reverse).reverse) h
  rw [len,List.length_reverse]
  have ht := trim_length (trimEnd cells).reverse
  rw [List.length_reverse] at ht
  refine (ht.trans (trim_length cells)).trans ?_
  simp only [cells,List.length_append,List.length_reverse,List.length_cons]
  have hl := trim_length t.left
  have hr := trim_length t.right
  omega

end GenLimit.LearningAlgorithmsLimit.NativeTape
