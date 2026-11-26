import GenLimit.Paper26_IdentificationWithComputationalTrace.Pushdown
import GenLimit.Paper26_IdentificationWithComputationalTrace.ControlPath
import GenLimit.Paper26_IdentificationWithComputationalTrace.ControlLower
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Constant-rate lower bound for deterministic pushdown machines

Every k-th input symbol pushes a marker. At end of input one pop per marker
checks the finite cutoff. Deleting this short final part of the computation
gives the same full-configuration observation for every machine accepting
the word, including the unbounded machine.
-/
namespace GenLimit.ComputationalTrace.PDA
open Control

private def limit (i : Option ℕ) := i.elim 0 (·+1)
private def sat (i : Option ℕ) (n : ℕ) := min n (limit i)
private def allowed (i : Option ℕ) (n : ℕ) := i.all (n ≤ ·)

private theorem sat_succ (i : Option ℕ) (n : ℕ) : sat i (sat i n + 1) = sat i (n+1) := by
  unfold sat; omega
private theorem allowed_iff (i : Option ℕ) (n : ℕ) :
    allowed i (sat i n) = true ↔ n ∈ extent i := by
  cases i <;> simp [allowed,sat,limit,extent]

private def checkRule (k : ℕ) (i : Option ℕ) (j : ℕ) (top : Bool) :
    Option (ℕ × Action) :=
  if top then some (k + sat i (j+1),false,.pop)
  else if allowed i j then some (k,false,.pop) else none

def blockProgram (k : ℕ) (i : Option ℕ) : Program ℕ where
  initial := 0
  rule q top look := if q < k then
    match look with
    | some true => let r := (q+1)%k
                   some (r,true, if r = 0 then .push true else .keep)
    | some false => none
    | none => if q = 0 then checkRule k i 0 top else none
  else if look.isNone then checkRule k i (q-k) top else none

private def marks (n : ℕ) := List.replicate n true ++ [false]

private theorem marks_head (n : ℕ) : (marks n).head? = some (decide (n ≠ 0)) := by
  cases n <;> simp [marks,List.replicate_succ]

private theorem input_step {k : ℕ} (hk : 0 < k) (i : Option ℕ) (m : ℕ) (tail : List Bool) :
    move device (blockProgram k i).machine (m%k,⟨true :: tail, marks (m/k)⟩) =
      some ((m+1)%k,⟨tail,marks ((m+1)/k)⟩) := by
  have hm := Nat.mod_lt m hk
  have he : (m%k+1)%k = (m+1)%k := Nat.mod_add_mod _ _ _
  by_cases h : (m+1)%k = 0
  · simp [device,move,Program.machine,blockProgram,hm,he,h,
      Nat.succ_div_of_mod_eq_zero h,Op.apply,marks,List.replicate_succ]
  · simp [device,move,Program.machine,blockProgram,hm,marks_head,he,h,
      Nat.succ_div_of_mod_ne_zero h,Op.apply]

private theorem read_path {k : ℕ} (hk : 0 < k) (m : ℕ) (tail : List Bool) :
    ∃ cs, cs.length = m ∧ ∀ i, Path device (blockProgram k i).machine
      (0,device.load (List.replicate m true ++ tail)) cs (m%k,⟨tail,marks (m/k)⟩) := by
  induction m generalizing tail with
  | zero => exact ⟨[],rfl,fun _ => by simp [device,marks]; exact .refl _⟩
  | succ m ih =>
    obtain ⟨cs,hc,hp⟩ := ih (true :: tail)
    refine ⟨cs ++ [(m%k,⟨true :: tail,marks (m/k)⟩)],by simp [hc],fun i => ?_⟩
    simpa only [List.replicate_succ',List.append_assoc,List.singleton_append] using
      (hp i).append (Path.single (by simp) (input_step hk i m tail))

private def checking (k : ℕ) (i : Option ℕ) (j n : ℕ) : Frame ℕ Memory :=
  (if j = 0 then 0 else k+sat i j,⟨[],marks n⟩)

private theorem check_table {k : ℕ} (hk : 0 < k) (i : Option ℕ) (j : ℕ) (b : Bool) :
    (blockProgram k i).rule (if j = 0 then 0 else k+sat i j) b none = checkRule k i (sat i j) b := by
  by_cases h : j = 0
  · subst j; simp [blockProgram,hk,sat]
  · simp [blockProgram,h,Nat.not_lt.mpr (Nat.le_add_right ..)]

private theorem pop_next {k : ℕ} (hk : 0 < k) (i : Option ℕ) (j n : ℕ) :
    move device (blockProgram k i).machine (checking k i j (n+1)) = some (checking k i (j+1) n) := by
  simp [checking,move,device,Program.machine,marks,List.replicate_succ,check_table hk,
    checkRule,Op.apply,sat_succ]

private theorem check_live (k : ℕ) (i : Option ℕ) (j n : ℕ) :
    isFinal device (blockProgram k i).machine (checking k i j n) = false := by
  simp [checking,marks]

private theorem bottom_step {k : ℕ} (hk : 0 < k) (i : Option ℕ) (j : ℕ) :
    move device (blockProgram k i).machine (checking k i j 0) =
      if allowed i (sat i j) then some (k,⟨[],[]⟩) else none := by
  cases he : allowed i (sat i j) <;>
    simp [checking,move,device,Program.machine,marks,check_table hk,checkRule,he,Op.apply]

private theorem check_exact {k : ℕ} (hk : 0 < k) (i : Option ℕ) (j n : ℕ) :
    ((∃ ds, Finish device (blockProgram k i).machine (checking k i j n) ds) → j+n ∈ extent i) ∧
    (j+n ∈ extent i → ∃ ds, ds.length = n+1 ∧ Finish device (blockProgram k i).machine
      (checking k i j n) ds) := by
  induction n generalizing j with
  | zero =>
    simp only [Nat.add_zero]
    constructor
    · rintro ⟨ds,hf⟩
      cases hf with
      | halt h => rw [check_live] at h; contradiction
      | next _ he _ =>
        by_contra h
        rw [bottom_step hk,if_neg (fun hh => h ((allowed_iff _ _).mp hh))] at he
        contradiction
    · intro hi
      exact ⟨[(_,_)],rfl,.next (check_live ..)
        (by rw [bottom_step hk,if_pos ((allowed_iff _ _).mpr hi)]) (.halt rfl)⟩
  | succ n ih =>
    have hp := Path.single (check_live ..) (pop_next hk i j n)
    constructor
    · rintro ⟨ds,hf⟩
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (ih (j+1)).1 (hp.finish_at_end hf)
    · intro hi
      obtain ⟨ds,hl,hf⟩ := (ih (j+1)).2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi)
      exact ⟨_ :: ds,by simp [hl],.next (check_live ..) (pop_next hk i j n) hf⟩

def blockWord (k n : ℕ) := List.replicate (k*n) true

private noncomputable def prefixList {k : ℕ} (hk : 0 < k) (n : ℕ) :=
  (read_path hk (k*n) []).choose

private def endRead (n : ℕ) : Frame ℕ Memory := (0,⟨[],marks n⟩)

private noncomputable def commonPrefix {k : ℕ} (hk : 0 < k) (n : ℕ) :=
  prefixList hk n ++ [endRead n]

private theorem block_data {k : ℕ} (hk : 0 < k) (i : Option ℕ) (n : ℕ) (hn : n ∈ extent i) :
    ∃ ds tail, Finish device (blockProgram k i).machine (0, device.load (blockWord k n)) ds ∧
      tail.length = n+1 ∧ (0,device.load (blockWord k n)) :: ds = commonPrefix hk n ++ tail := by
  have hp : Path device (blockProgram k i).machine (0,device.load (blockWord k n))
      (prefixList hk n) (endRead n) := by
    simpa [blockWord,endRead,prefixList,Nat.mul_div_cancel_left _ hk] using
      (read_path hk (k*n) []).choose_spec.2 i
  obtain ⟨tail,hlen,hf⟩ := (check_exact hk i 0 n).2 (by simpa using hn)
  obtain ⟨ds,he,hh⟩ := hp.finish (show Finish _ _ (endRead n) tail from hf)
  exact ⟨ds,tail,hh,hlen,by simpa [commonPrefix] using he⟩

private theorem first_false (w : List Bool) : ∃ n t, w = List.replicate n true ++ t ∧
    (t = [] ∨ ∃ ys, t = false :: ys) := by
  induction w with
  | nil => exact ⟨0,[],rfl,Or.inl rfl⟩
  | cons a w ih =>
    cases a with
    | false => exact ⟨0,false :: w,rfl,Or.inr ⟨w,rfl⟩⟩
    | true =>
      obtain ⟨n,t,h,ht⟩ := ih
      exact ⟨n+1,t,by simp [List.replicate_succ,h],ht⟩

theorem block_language {k : ℕ} (hk : 0 < k) (i : Option ℕ) :
    language device (blockProgram k i).machine = blockWord k '' extent i := by
  ext w
  constructor
  · rintro ⟨ds,hf⟩
    obtain ⟨m,t,rfl,ht⟩ := first_false w
    obtain ⟨cs,_,hp⟩ := read_path hk m t
    obtain ⟨xs,he⟩ := (hp i).finish_at_end hf
    have next : ∃ d, move device (blockProgram k i).machine (m%k,⟨t,marks (m/k)⟩) = some d := by
      cases he with
      | halt h => simp [marks] at h
      | next _ h _ => exact ⟨_,h⟩
    have hm := Nat.mod_lt m hk
    rcases ht with rfl | ⟨ys,rfl⟩
    · have hz : m%k = 0 := by
        by_contra h
        simp [move,device,Program.machine,blockProgram,hm,marks_head,h] at next
      rw [hz] at he
      have hi := (check_exact hk i 0 (m/k)).1 ⟨_,he⟩
      have hlen : k*(m/k) = m := by have := Nat.mod_add_div m k; omega
      exact ⟨m/k,by simpa using hi,by simp [blockWord,hlen]⟩
    · simp [move,device,Program.machine,blockProgram,hm,marks_head] at next
  · rintro ⟨n,hn,rfl⟩
    obtain ⟨ds,_,hf,_,_⟩ := block_data hk i n hn
    exact ⟨ds,hf⟩

private theorem finite_block {k : ℕ} (hk : 0 < k) (i : Option ℕ) :
    ∃ Q, FiniteStates (blockProgram k i).machine Q := by
  refine ⟨Finset.range (k+limit i+1),by simp [Program.machine,blockProgram],fun q _ o r a h => ?_⟩
  rcases o with ⟨look,top⟩
  cases top with
  | none => simp [Program.machine] at h
  | some b =>
    have proj : ∃ act, (blockProgram k i).rule q b look = some (r,act) := by
      cases ht : (blockProgram k i).rule q b look with
      | none => simp [Program.machine,ht] at h
      | some p =>
        simp [Program.machine,ht] at h
        exact ⟨a,congrArg some h.2⟩
    obtain ⟨act,ht⟩ := proj
    simp only [blockProgram,checkRule] at ht
    simp only [Finset.mem_range]
    have hrem := Nat.mod_lt (q+1) hk
    split at ht <;> repeat' split at ht
    all_goals simp_all [sat] <;> omega

theorem impossible_constant (rate : ℝ) (hr : 0 < rate) {H : Type} (denote : H → Set (List Bool))
    (learn : List (Sample Memory) → H) :
    ¬ (∀ (P : Program ℕ) s, Presentation device P.machine (RateBound rate 1) s →
      IdentifiesInLimit denote learn s (language device P.machine)) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2 / rate)
  have hkr := (div_lt_iff₀ hr).mp hk
  have hkp : 0 < k := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    norm_num at hkr
  intro hLearn
  apply no_learner_of_chain device _ (fun i => (blockProgram k i).machine) (blockWord k)
    (fun a b hh => Nat.eq_of_mul_eq_mul_left hkp (by simpa [blockWord] using congrArg List.length hh))
    (commonPrefix hkp) (finite_block hkp) (block_language hkp) _ denote learn
    (fun i => hLearn (blockProgram k i))
  intro i n hn
  obtain ⟨ds,tail,hf,ht,he⟩ := block_data hkp i n hn
  refine ⟨ds,hf,?_,?_⟩
  · intro hl
    rw [show (blockProgram k i).machine.initial = 0 by rfl,he]
    refine ⟨tail.length,.eraseSuffix _ _,?_⟩
    have hpre : (commonPrefix hkp n).length = k*n+1 := by
      rw [commonPrefix,List.length_append]
      exact congrArg (· + 1) (read_path hkp (k*n) []).choose_spec.1
    have hn0 : 0 < n := by
      by_contra! hz
      have : n=0 := by omega
      simp [blockWord,this] at hl
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hmul := mul_le_mul_of_nonneg_right hkr.le (Nat.cast_nonneg n)
    simp only [List.length_append,hpre,ht,Nat.cast_add,Nat.cast_one,Nat.cast_mul]
    nlinarith [mul_nonneg hr.le (Nat.cast_nonneg n : (0:ℝ) ≤ _)]
  · intro e h
    rw [show (blockProgram k i).machine.initial = 0 by rfl,he]
    exact List.mem_append_left _ h

end GenLimit.ComputationalTrace.PDA
