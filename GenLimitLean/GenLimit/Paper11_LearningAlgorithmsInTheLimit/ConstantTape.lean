import GenLimit.Paper11_LearningAlgorithmsInTheLimit.ControllerRun
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.WordTape
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.MassDiagonal
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.QuantitativeSimulation

/-! # Linear-time constant teachers on the fixed paper tape alphabet -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open Turing
open Nat.Partrec (Code)

noncomputable def universalValue (x : ℕ) : Part ℕ :=
  ((Denumerable.ofNat Code x).eval 0).map (fun n ↦ 2^n)

private theorem value_part : Partrec universalValue := by
  have hp : Primrec₂ (fun a b : ℕ ↦ a^b) := Primrec₂.unpaired.mpr (Primrec.nat_iff.mpr Nat.Primrec.pow)
  exact (Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)).map
    ((hp.to_comp.comp (Computable.const 2) Computable.snd).to₂)

noncomputable def evaluator := (binary_realization universalValue value_part).choose

theorem flat_length (x : ℕ) : (chunks x).flatten.length = (Fintype.card Cell+1)*(logical x).length := by
  unfold chunks
  induction logical x with
  | nil => simp
  | cons a l ih => simp [ih,Nat.mul_succ]; omega

abbrev tapeWidth := Fintype.card Cell
noncomputable def encodedInput (c : Code) := (chunks (Encodable.encode c)).flatten

variable {Γ α : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] [Encodable Γ]

noncomputable def constantTeacher (o : Γ) (c : Code) : TuringProgram Γ :=
  program (rule o evaluator (encodedInput c) tapeWidth) .erase

/-- A single additive time constant works on every input word. The native
program initializes, executes and halts with a clean word on its actual tape. -/
theorem constant_runs (ι : α ↪ Γ) (noBlank : ∀ a, ι a ≠ default) (a : α) {c : Code} {n : ℕ}
    (hn : n ∈ c.eval 0) : ∃ k t, n ≤ k ∧ ∀ x : List α,
      (constantTeacher (ι a) c).runWithin (x.length + t) (wordIO ι) x = some (List.replicate k a) := by
  have hv : 2^n ∈ universalValue (Encodable.encode c) := by
    unfold universalValue
    rw [Denumerable.ofNat_encode]
    exact (Part.mem_map_iff _).mpr ⟨n,hn,rfl⟩
  obtain ⟨q,hq⟩ := (binary_realization universalValue value_part).choose_spec _ _ hv
  let w := encodedInput c
  let δ := rule (ι a) evaluator w tapeWidth
  have pre : Moves δ _ _ := preload (ι a) evaluator w tapeWidth
  have sim := simulate_halt (ι a) evaluator w tapeWidth (noBlank a) (q := q) hq
  have post := print_run (ι a) evaluator w tapeWidth (noBlank a) (chunks (2^n)) [] (fun _ ↦ chunks_spec)
  let k := (chunks (2^n)).flatten.length
  have hpost : Moves δ (some .inspect,Tape.mk₁ ((chunks (2^n)).flatten.map (bitSymbol (ι a))))
      (none,Tape.mk₂ (List.replicate k (ι a)) []) := by simpa [δ,k,Tape.mk₁] using post
  obtain ⟨s,hs⟩ := pre.trans (sim.trans hpost)
  refine ⟨k,1+s,?_,fun x ↦ ?_⟩
  · exact (logical_length_pow n).trans (by dsimp [k]; rw [flat_length,Nat.succ_mul]; omega)
  · have hi : ∀ v ∈ x.map ι, v ≠ default := by
      rintro _ h; obtain ⟨b,_,rfl⟩ := List.mem_map.mp h; exact noBlank b
    have er := erase_run (ι a) evaluator w tapeWidth _ hi
    have init : represents (Phase.erase : Control evaluator w tapeWidth)
        ⟨1,initialWord ι x⟩ (some .erase,Tape.mk₁ (x.map ι)) := by
      constructor
      · simp [tag]
      · exact initial_view _ _
    have h := run_represents δ .erase (x.length+(1+s)) init
    have he : (tick δ)^[x.length+(1+s)] (some .erase,Tape.mk₁ (x.map ι)) =
        (none,Tape.mk₂ (List.replicate k (ι a)) []) := by
      rw [show x.length+(1+s) = s+((x.map ι).length+1) by simp; omega,Function.iterate_add_apply]
      exact (congrArg ((tick δ)^[s]) er).trans hs
    rw [he] at h
    obtain ⟨state,tape⟩ := h
    change ((program δ .erase).runConfiguration default (x.length+(1+s)) ⟨1,initialWord ι x⟩).state = 0 at state
    change view ((program δ .erase).runConfiguration default (x.length+(1+s)) ⟨1,initialWord ι x⟩).tape = _ at tape
    unfold TuringProgram.runWithin
    change (if ((program δ .erase).runConfiguration default _ _).state = 0 then
      readWord ι (view ((program δ .erase).runConfiguration default _ _).tape) else none) = _
    simp only [wordIO]
    rw [if_pos state,tape,read_unary ι a (noBlank a)]

end GenLimit.LearningAlgorithmsLimit.NativeTape
