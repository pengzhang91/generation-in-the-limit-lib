import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TapeBlocks
import Mathlib.Computability.Halting

/-! # A fixed two-symbol, single-tape evaluator for recursive codes

Mathlib's stack-machine realization of partial recursion is translated
first to a one-tape program and then to binary tape cells. The final
configuration has its head at the beginning of the encoded result, with
blank tape on both sides of that finite word. -/
namespace GenLimit.LearningAlgorithmsLimit.NativeTape
open Turing PartrecToTM2

structure BinaryMachine where
  State : Type
  initial : Inhabited State
  program : @TM0.Machine Bool State initial
  states : Finset State
  supports : @TM0.Supports Bool State initial program (↑states : Set State)

attribute [instance] BinaryMachine.initial

private theorem single_stack (L : List Γ') :
    Function.update (fun _ : K' ↦ ([] : List Γ')) K'.main L = K'.elim L [] [] [] := by
  funext k
  cases k <;> simp

private theorem related_unique {k : TM2.Cfg (fun _ : K' ↦ Γ') Λ' (Option Γ')}
    {u v} (hu : TM2to1.TrCfg k u) (hv : TM2to1.TrCfg k v) : u = v := by
  cases hu with
  | mk L hl =>
    cases hv with
    | mk R hr =>
      have h : L = R := by
        apply ListBlank.ext
        intro i
        funext j
        rw [← proj_map_nth,← proj_map_nth,hl,hr]
      subst R
      rfl

private theorem start_rel (c : ToPartrec.Code) (x : ℕ) :
    TM2to1.TrCfg (PartrecToTM2.init c [x])
      ⟨some (.normal (trNormal c .halt)),none,Tape.mk₁ (logical x)⟩ := by
  letI : Inhabited Λ' := ⟨trNormal c .halt⟩
  have h := TM2to1.trCfg_init (Γ := fun _ : K' ↦ Γ') (Λ := Λ') (σ := Option Γ') K'.main (trList [x])
  simpa only [TM2.init,single_stack] using h

private theorem halt_rel (y : ℕ) : TM2to1.TrCfg (PartrecToTM2.halt [y])
    ⟨none,none,Tape.mk₁ (logical y)⟩ := by
  have h := start_rel ToPartrec.Code.succ y
  generalize he : Tape.mk₁ (logical y) = T at h ⊢
  cases h with
  | mk L hl => exact .mk _ hl

private theorem binary_tape (x : ℕ) :
    TM1to1.trTape (blank_block (A := Cell)) (Tape.mk₁ (logical x)) =
      Tape.mk₁ (chunks x).flatten := by
  change TM1to1.trTape _ (Tape.mk' (ListBlank.mk []) (ListBlank.mk (logical x))) = _
  rw [TM1to1.trTape_mk']
  simp only [TM1to1.trTape',ListBlank.flatMap_mk,List.flatMap_nil]
  rfl

/-- One finite control for each partial recursive function, independent of
the data written on its input tape. -/
theorem binary_realization (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ U : BinaryMachine, ∀ x y, y ∈ f x → ∃ q : U.State,
      (⟨q,Tape.mk₁ (chunks y).flatten⟩ : TM0.Cfg Bool U.State) ∈
        Turing.eval (TM0.step U.program) ⟨U.initial.default,Tape.mk₁ (chunks x).flatten⟩ := by
  obtain ⟨c,hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  letI : Inhabited Λ' := ⟨trNormal c .halt⟩
  let M := TM2to1.tr PartrecToTM2.tr
  let B := TM1to1.tr (block (A := Cell)) unblock M
  let prog := TM1to0.tr B
  have ss := TM1to0.tr_supports B (TM1to1.tr_supports block unblock M
    (TM2to1.tr_supports PartrecToTM2.tr (PartrecToTM2.tr_supports c .halt)))
  let U : BinaryMachine := ⟨_,inferInstance,prog,_,ss⟩
  refine ⟨U,fun x y hy ↦ ?_⟩
  have he : [y] ∈ c.eval [x] := by
    have h := hc (List.Vector.ofFn (fun _ : Fin 1 ↦ x))
    change c.eval [x] = _ at h
    rw [h]
    exact Part.mem_map_iff _ |>.mpr ⟨y,by simpa using hy,rfl⟩
  have h2 : PartrecToTM2.halt [y] ∈ Turing.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c [x]) := by
    rw [PartrecToTM2.tr_eval]
    exact (Part.mem_map_iff _).mpr ⟨_,he,rfl⟩
  obtain ⟨v,hv,hm⟩ := Turing.tr_eval (TM2to1.tr_respects _) (start_rel c x) h2
  rw [related_unique hv (halt_rel y)] at hm
  have hb := Turing.tr_eval (TM1to1.tr_respects (enc0 := blank_block) unblock M unblock_block)
    (show TM1to1.trCfg block blank_block _ = _ from rfl) hm
  obtain ⟨_,rfl,hb⟩ := hb
  obtain ⟨_,rfl,h0⟩ := Turing.tr_eval (TM1to0.tr_respects B) rfl hb
  simp only [TM1to0.trCfg,TM1to1.trCfg,binary_tape] at h0
  exact ⟨_,h0⟩

end GenLimit.LearningAlgorithmsLimit.NativeTape
