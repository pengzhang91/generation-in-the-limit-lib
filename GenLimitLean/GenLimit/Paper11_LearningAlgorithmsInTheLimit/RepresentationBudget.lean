import GenLimit.Paper11_LearningAlgorithmsInTheLimit.ConstantTape

/-! # An effective bound on all finite transition-table representations
of the constant teachers, independent of their running times. -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open Nat.Partrec (Code)
variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] [Encodable Γ]

private def tower (b : ℕ) : ℕ → ℕ := Nat.rec 0 (fun _ k ↦ (Nat.pair b k).succ)

private theorem tower_prim : Primrec₂ tower :=
  Primrec.nat_rec (Primrec.const 0) ((Primrec.succ.comp
    (Primrec₂.natPair.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂)

private theorem list_bound [Encodable A] (b : ℕ) (l : List A) (h : ∀ a ∈ l, Encodable.encode a ≤ b) :
    Encodable.encode l ≤ tower b l.length := by
  induction l with
  | nil => exact le_rfl
  | cons a t ih =>
    exact Nat.succ_le_succ (pair_mono (h a List.mem_cons_self) (ih (fun v hv ↦ h v (List.mem_cons_of_mem _ hv))))

private theorem tower_mono (b : ℕ) : Monotone (tower b) :=
  monotone_nat_of_le_succ (fun n ↦ (Nat.right_le_pair b (tower b n)).trans (Nat.le_succ _))

private def maxMove := max (Encodable.encode TuringHeadMove.left)
    (max (Encodable.encode TuringHeadMove.right) (Encodable.encode TuringHeadMove.stay))

private theorem move_le (m : TuringHeadMove) : Encodable.encode m ≤ maxMove := by
  cases m <;> simp [maxMove]

private noncomputable def stateBudget (n : ℕ) :=
  evaluator.states.card + (tapeWidth+1)*(n+1) + tapeWidth + 4

private noncomputable def syntaxBudget (Γ : Type) [Fintype Γ] [Encodable Γ] (n : ℕ) :=
  tower (Nat.pair (stateBudget n+1) (Nat.pair (maxSymbol Γ) maxMove)) (tableSize Γ (stateBudget n))

private theorem state_prim : Primrec stateBudget := by
  exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const _)
    (Primrec.nat_mul.comp (Primrec.const _) Primrec.succ)) (Primrec.const _)) (Primrec.const _)

private theorem syntax_prim : Primrec (syntaxBudget Γ) := by
  have s := Primrec.succ.comp state_prim
  exact tower_prim.comp (Primrec₂.natPair.comp s (Primrec.const _))
    (Primrec.succ.comp (Primrec₂.natPair.comp s (Primrec.const _)))

theorem teacher_code_le (o : Γ) (c : Code) :
    Encodable.encode (constantTeacher o c) ≤ syntaxBudget Γ (Encodable.encode c) := by
  let card := Fintype.card (Control evaluator (encodedInput c) tapeWidth)
  let bound := stateBudget (Encodable.encode c)
  have hcard : card ≤ bound := by
    dsimp only [card,bound,stateBudget]
    rw [control_card,encodedInput,flat_length]
    have h := Nat.mul_le_mul_left (tapeWidth+1) (logical_length_le (Encodable.encode c))
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left h _) _) _
  let m := Nat.pair (bound+1) (Nat.pair (maxSymbol Γ) maxMove)
  have row {v : TuringInstruction Γ} (h : v ∈ constantTeacher o c) : Encodable.encode v ≤ m := by
    have hs : v.1 ≤ card+1 := program_state_bound _ _ h
    obtain ⟨q,a,dir⟩ := v
    simp only [Encodable.encode_prod_val]
    exact pair_mono (hs.trans (Nat.succ_le_succ hcard))
      (pair_mono (Finset.le_sup (f := @Encodable.encode Γ _) (Finset.mem_univ a)) (move_le dir))
  refine (list_bound m _ (fun _ ↦ row)).trans (tower_mono m ?_)
  rw [constantTeacher,program_length]
  exact Nat.succ_le_succ (pair_mono (Nat.succ_le_succ hcard) le_rfl)

private def envelope (f : ℕ → ℕ) (n : ℕ) : ℕ := n.rec (f 0) (fun j k ↦ max k (f (j+1)))

private theorem envelope_comp {f : ℕ → ℕ} (hf : Computable f) : Computable (envelope f) :=
  Computable.nat_rec Computable.id (Computable.const _) ((Primrec.nat_max.to_comp.comp
    (Computable.snd.comp Computable.snd) (hf.comp (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)))).to₂)

private theorem envelope_le (f : ℕ → ℕ) {i n} (hi : i ≤ n) : f i ≤ envelope f n := by
  induction n with
  | zero => obtain rfl := Nat.le_zero.mp hi; exact le_rfl
  | succ n ih =>
    rcases Nat.le_succ_iff.mp hi with h | h
    · exact (ih h).trans (le_max_left _ _)
    · subst i; exact le_max_right _ _

theorem bounded_indices (o : Γ) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ g : Code → ℕ, Computable g ∧ ∀ c j, j ≤ Encodable.encode (constantTeacher o c) → f j ≤ g c := by
  refine ⟨fun c ↦ envelope f (syntaxBudget Γ (Encodable.encode c)),
    (envelope_comp hf).comp (syntax_prim.to_comp.comp Computable.encode),fun c j hj ↦ ?_⟩
  exact envelope_le f (hj.trans (teacher_code_le o c))

/-- A computable majorant on code indices suffices, even when the finite
state labelling used by the compiler was selected nonconstructively. -/
theorem majorant (β : TuringProgram Γ → ℕ)
    (hb : Computable (fun n ↦ β (decodeTuringProgram n))) (o : Γ) :
    ∃ g : Code → ℕ, Computable g ∧ ∀ c, β (constantTeacher o c) ≤ g c := by
  refine ⟨fun c ↦ envelope (fun n ↦ β (decodeTuringProgram n)) (syntaxBudget Γ (Encodable.encode c)),
    (envelope_comp hb).comp (syntax_prim.to_comp.comp Computable.encode),fun c ↦ ?_⟩
  simpa using envelope_le (fun n ↦ β (decodeTuringProgram n)) (teacher_code_le o c)

end GenLimit.LearningAlgorithmsLimit.NativeTape
