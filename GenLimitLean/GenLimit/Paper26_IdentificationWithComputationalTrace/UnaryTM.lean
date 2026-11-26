import GenLimit.Paper26_IdentificationWithComputationalTrace.Turing
import GenLimit.Paper26_IdentificationWithComputationalTrace.ControlLower

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace GenLimit.ComputationalTrace.TM
open Control

def unary (n : ℕ) := List.replicate n true

private def bound (i : Option ℕ) : ℕ := i.elim 0 (·+1)

private def count (i : Option ℕ) (n : ℕ) := min n (bound i)

private def admissible (i : Option ℕ) (j : ℕ) : Bool := i.all (j ≤ ·)

/-- States 0, 1, 2, 3 and 4 mark the origin, control the outer loop, scan
left, scan right and accept. Higher states count the initial unary segment.
A bounded machine saturates the count one past its acceptance threshold. -/
def paddedMachine (i : Option ℕ) : Machine ℕ Observation Action where
  initial := 0
  final q := decide (q = 4)
  table q o := match q with
    | 0 => some (5,.stay,.stay,some true)
    | 1 => if o.2 then some (4,.stay,.stay,none) else some (2,.left,.left,none)
    | 2 => if o.1.isSome then some (2,.left,.stay,none) else some (3,.right,.stay,none)
    | 3 => if o.1.isSome then some (3,.right,.stay,none) else some (1,.stay,.stay,none)
    | 4 => none
    | j+5 => match o.1 with
      | none => if admissible i j then some (1,.stay,.stay,none) else none
      | some true => some (count i (j+1)+5,.right,.right,none)
      | some false => none

private theorem count_succ (i : Option ℕ) (n : ℕ) :
    count i (count i n + 1) = count i (n+1) := by unfold count; omega

private theorem admissible_count (i : Option ℕ) (n : ℕ) :
    admissible i (count i n) = true ↔ n ∈ extent i := by
  cases i with
  | none => simp [admissible,extent]
  | some j => simp [admissible,count,bound,extent]

def marked (w : List Bool) (x y : ℤ) : Memory :=
  ⟨w,x,y,Function.update (fun _ => false) 0 true⟩

private def scanning (i : Option ℕ) (w : List Bool) (n : ℕ) : Frame ℕ Memory :=
  (count i n + 5,marked w n n)

private theorem read_unary (n k : ℕ) (hk : k < n) :
    readInput (unary n) k = some true := by
  simp [readInput,unary,hk]

private theorem read_end (w : List Bool) : readInput w w.length = none := by simp [readInput]

private theorem prefix_path (i : Option ℕ) (w : List Bool) (n : ℕ)
    (hn : ∀ j < n, readInput w j = some true) :
    ∃ cs, cs.length = n+1 ∧ Path device (paddedMachine i) (0,device.load w) cs (scanning i w n) := by
  induction n with
  | zero =>
    refine ⟨[(_,_)],rfl,Path.single rfl ?_⟩
    simp [move,device,paddedMachine,marked,scanning,count,Motion.offset]
  | succ n ih =>
    obtain ⟨cs,hc,hp⟩ := ih fun j hj => hn _ (by omega)
    have step : move device (paddedMachine i) (scanning i w n) = some (scanning i w (n+1)) := by
      simp [move,device,paddedMachine,scanning,marked,hn n (by omega),count_succ,Motion.offset]
    exact ⟨cs ++ [scanning i w n],by simp [hc],hp.append (.single (by simp [paddedMachine,scanning]) step)⟩

/-- Scanning right from position zero to the right blank costs at least n
steps. Scanning left detects the blank at position -1. The work tape keeps
its single origin mark throughout both scans. -/
private theorem right_path (n y j : ℕ) (hj : j ≤ n) :
    ∃ cs, n - j ≤ cs.length ∧ ∀ i, Path device (paddedMachine i)
      (3,marked (unary n) j y) cs (1,marked (unary n) n y) := by
  induction hj using Nat.decreasingInduction with
  | self =>
    refine ⟨[(3,_)],by simp, fun i => .single rfl ?_⟩
    simp [move,device,paddedMachine,marked,unary,readInput,Motion.offset]
  | of_succ j hj ih =>
    obtain ⟨cs,hl,hp⟩ := ih
    refine ⟨(3,marked (unary n) j y) :: cs,by simp; omega,fun i => .cons rfl ?_ (hp i)⟩
    simp [move,device,paddedMachine,marked,read_unary _ _ hj,Motion.offset]

private theorem left_path (n y j : ℕ) (hj : j ≤ n) :
    ∃ cs, ∀ i, Path device (paddedMachine i)
      (2,marked (unary n) ((j : ℤ)-1) y) cs (3,marked (unary n) 0 y) := by
  induction j with
  | zero =>
    refine ⟨[(2,_)],fun i => .single rfl ?_⟩
    simp [move,device,paddedMachine,marked,readInput,Motion.offset]
  | succ j ih =>
    obtain ⟨cs,hp⟩ := ih (by omega)
    have hj' : j < n := by omega
    refine ⟨(2,marked (unary n) (((j+1 : ℕ) : ℤ)-1) y) :: cs,
      fun i => .cons rfl ?_ (hp i)⟩
    simp [move,device,paddedMachine,marked,read_unary _ _ hj',Motion.offset,sub_eq_add_neg]

theorem padding (n y : ℕ) : ∃ ds, n*y ≤ ds.length ∧ ∀ i,
    Finish device (paddedMachine i) (1,marked (unary n) n y) ds := by
  induction y with
  | zero =>
    refine ⟨[(4,marked (unary n) n 0)],by simp,fun i => .next rfl ?_ (.halt rfl)⟩
    simp [move,device,paddedMachine,marked,Motion.offset]
  | succ y ih =>
    obtain ⟨ds,hl,hf⟩ := ih
    obtain ⟨ls,hlp⟩ := left_path n y n le_rfl
    obtain ⟨rs,hr,hrp⟩ := right_path n y 0 (Nat.zero_le _)
    let start : Frame ℕ Memory := (1,marked (unary n) n (y+1))
    let after : Frame ℕ Memory := (2,marked (unary n) ((n : ℤ)-1) y)
    have step (i) : move device (paddedMachine i) start = some after := by
      simp [start,after,move,device,paddedMachine,marked,Motion.offset,
        Function.update_of_ne (show (y : ℤ)+1 ≠ 0 by omega),sub_eq_add_neg]
    refine ⟨ls ++ rs ++ (1,marked (unary n) n y) :: ds,?_, fun i => ?_⟩
    · simp [Nat.mul_succ] at hr ⊢
      omega
    · have hp : Path device (paddedMachine i) after (ls ++ rs) (1,marked (unary n) n y) :=
        (hlp i).append (hrp i)
      obtain ⟨cs,hcs,hs⟩ := hp.finish (hf i)
      rw [← hcs]
      exact .next rfl (step i) hs

private noncomputable def commonTail (n : ℕ) := (padding n n).choose
private def outer (n : ℕ) : Frame ℕ Memory := (1,marked (unary n) n n)
private noncomputable def noise (n : ℕ) := outer n :: commonTail n

private theorem run_data (i : Option ℕ) (n : ℕ) (hi : n ∈ extent i) :
    ∃ pre ds, pre.length = n+2 ∧ (0,device.load (unary n)) :: ds = pre ++ noise n ∧
      Finish device (paddedMachine i) (0,device.load (unary n)) ds := by
  obtain ⟨cs,hc,hp⟩ := prefix_path i (unary n) n (read_unary n)
  have had := (admissible_count i n).mpr hi
  have hs : move device (paddedMachine i) (scanning i (unary n) n) = some (outer n) := by
    simp [move,device,paddedMachine,scanning,outer,marked,readInput,unary,had,Motion.offset]
  have path := hp.append (Path.single (by simp [paddedMachine,scanning]) hs)
  obtain ⟨ds,hds,hf⟩ := path.finish ((padding n n).choose_spec.2 i)
  exact ⟨_,ds,by simp [hc],hds,hf⟩

private theorem split_unary (w : List Bool) :
    ∃ n tail, w = unary n ++ tail ∧ (tail = [] ∨ ∃ ys, tail = false :: ys) := by
  induction w with
  | nil => exact ⟨0,[],rfl,Or.inl rfl⟩
  | cons a w ih =>
    cases a with
    | false => exact ⟨0,false :: w,rfl,Or.inr ⟨w,rfl⟩⟩
    | true =>
      obtain ⟨n,t,h,ht⟩ := ih
      exact ⟨n+1,t,by simp [unary,List.replicate_succ,h],ht⟩

theorem padded_language (i : Option ℕ) :
    language device (paddedMachine i) = unary '' extent i := by
  ext w
  constructor
  · rintro ⟨ds,hf⟩
    obtain ⟨n,t,rfl,ht⟩ := split_unary w
    have hp' (j) (hj : j < n) : readInput (unary n ++ t) j = some true := by
      simp [readInput,unary,List.getElem?_append_left (by simpa using hj : j < (List.replicate n true).length),hj]
    obtain ⟨cs,_,hp⟩ := prefix_path i _ n hp'
    obtain ⟨_,hy⟩ := hp.finish_at_end hf
    have next : ∃ d, move device (paddedMachine i) (scanning i (unary n ++ t) n) = some d := by
      cases hy with
      | halt h => simp [paddedMachine,scanning] at h
      | next _ h _ => exact ⟨_,h⟩
    have hr : readInput (unary n ++ t) n = t.head? := by
      simp [readInput,unary,List.head?_eq_getElem?,List.getElem?_append_right (show (List.replicate n true).length ≤ n by simp)]
    rcases ht with rfl | ⟨ys,rfl⟩
    · have had : admissible i (count i n) = true := by
        by_contra hh
        have hn : readInput (unary n) n = none := by simp [readInput,unary]
        simp [move,device,paddedMachine,scanning,marked,hn,hh] at next
      exact ⟨n,(admissible_count i n).mp had,by simp⟩
    · simp [move,device,paddedMachine,scanning,marked,hr] at next
  · rintro ⟨n,hi,rfl⟩
    obtain ⟨_,ds,_,_,hf⟩ := run_data i n hi
    exact ⟨ds,hf⟩

private theorem finite_padded (i : Option ℕ) : ∃ Q, FiniteStates (paddedMachine i) Q := by
  refine ⟨Finset.range (bound i + 6),by simp [paddedMachine],fun q _ o r a h => ?_⟩
  change (paddedMachine i).table q o = some (r,a) at h
  simp only [paddedMachine] at h
  simp only [Finset.mem_range]
  split at h <;> repeat' split at h
  all_goals simp_all [count] <;> omega

/-- A single modulus works for every member of the chain. The numerator is
exactly the number of dropped configurations. The common suffix has at least
n squared transitions before the machine halts. -/
theorem impossible_diminishing {H : Type} (denote : H → Set (List Bool))
    (learn : List (Sample Memory) → H) :
    ¬ (∀ M s, Presentation device M (DiminishingBound (fun d => 2*(d+2))) s →
      IdentifiesInLimit denote learn s (language device M)) := by
  intro hlearn
  apply no_learner_of_chain device _ paddedMachine unary (fun a b h => by
    simpa [unary] using congrArg List.length h) noise finite_padded padded_language _ denote learn
    (fun i => hlearn (paddedMachine i))
  intro i n hn
  obtain ⟨pre,ds,hlen,he,hf⟩ := run_data i n hn
  refine ⟨ds,hf,?_,?_⟩
  · intro d hcut
    change 2*(d+2) ≤ (unary n).length at hcut
    simp only [unary,List.length_replicate] at hcut
    rw [show (paddedMachine i).initial = 0 by rfl,he]
    refine ⟨pre.length,.erasePrefix _ _,?_⟩
    have hn2 : n*n ≤ (commonTail n).length := (padding n n).choose_spec.1
    have hlen' : (n+2)*(d+2) ≤ (pre ++ noise n).length := by
      have hm := Nat.mul_le_mul_left n hcut
      have hd : 2*(d+2) ≤ n*(d+2) := Nat.mul_le_mul_right _ (by omega)
      simp only [noise,List.length_append,List.length_cons,hlen]
      nlinarith
    rw [hlen,one_div_mul_eq_div]
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast hlen'
  · intro e hh
    rw [show (paddedMachine i).initial = 0 by rfl,he]
    exact List.mem_append_right _ hh

end GenLimit.ComputationalTrace.TM
