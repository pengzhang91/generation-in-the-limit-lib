import GenLimit.Core.Text
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! Realization of local game replies on actual generation histories.
If a local recommendation was generated earlier, that word is already
credited and the current round may use a fresh backup word. -/
namespace GenLimit.KleinbergWei.Banach.LocalReplies
open Set
open scoped Classical
noncomputable section
variable {V : Type*} [DecidableEq V] [Inhabited V]
variable (plan : List V → V → Option V) (backup : List V → Set V)
  (inf : ∀ h, (backup h).Infinite)

private structure State (V : Type*) where
  history : List V
  outputs : Finset V
  last : V

private def chosen (h : List V) (x : V) (old : Finset V) : V :=
  let used := (h++[x]).toFinset ∪ old
  if ok : ∃ y, plan h x = some y ∧ y ∉ used then ok.choose
  else ((inf (h++[x])).exists_notMem_finset used).choose

private def advance (p : State V) (x : V) : State V :=
  let y := chosen plan backup inf p.history x p.outputs
  ⟨p.history++[x],insert y p.outputs,y⟩

private def run (h : List V) := h.foldl (advance plan backup inf) ⟨[],∅,default⟩

private theorem push (h : List V) (x : V) :
    run plan backup inf (h++[x]) = advance plan backup inf (run plan backup inf h) x := by simp [run]

private theorem history (h : List V) : (run plan backup inf h).history = h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h x ih => rw [push]; change _++[x]=_; rw [ih]

def rule (h : List V) := (run plan backup inf h).last
def play (s : ℕ → V) (t : ℕ) := rule plan backup inf (textPrefix s (t+1))

private def outputs (s : ℕ → V) (t : ℕ) := (run plan backup inf (textPrefix s t)).outputs

private theorem output_eq (s : ℕ → V) (t : ℕ) : play plan backup inf s t =
    chosen plan backup inf (textPrefix s t) (s t) (outputs plan backup inf s t) := by
  unfold play rule
  rw [textPrefix_succ,push]
  simp [advance,history,outputs]

private theorem mem_outputs {s : ℕ → V} {t y} : y ∈ outputs plan backup inf s t ↔
    ∃ i < t, play plan backup inf s i = y := by
  induction t with
  | zero => simp [outputs,run]
  | succ t ih =>
    have eq : outputs plan backup inf s (t+1) =
        insert (play plan backup inf s t) (outputs plan backup inf s t) := by
      rw [output_eq]; unfold outputs; rw [textPrefix_succ,push]; simp [advance,history]
    rw [eq,Finset.mem_insert,ih]
    constructor
    · rintro (eq | ⟨i,lt,eq⟩)
      · exact ⟨t,by omega,eq.symm⟩
      · exact ⟨i,by omega,eq⟩
    · rintro ⟨i,hi,eq⟩
      by_cases e : i=t
      · exact Or.inl (e ▸ eq.symm)
      · exact Or.inr ⟨i,by omega,eq⟩

theorem decision (s : ℕ → V) (t : ℕ) :
    let y := play plan backup inf s t
    y ∉ textPrefix s (t+1) ∧ (∀ i < t, play plan backup inf s i ≠ y) ∧
      (plan (textPrefix s t) (s t) = some y ∨ y ∈ backup (textPrefix s (t+1))) := by
  dsimp only
  let used := (textPrefix s (t+1)).toFinset ∪ outputs plan backup inf s t
  have dec : play plan backup inf s t ∉ used ∧
      (plan (textPrefix s t) (s t) = some (play plan backup inf s t) ∨
      play plan backup inf s t ∈ backup (textPrefix s (t+1))) := by
    rw [output_eq]
    dsimp only [used,chosen]
    rw [textPrefix_succ]
    split
    next h => exact ⟨h.choose_spec.2,Or.inl h.choose_spec.1⟩
    next h =>
      have pick := (inf (textPrefix s t++[s t])).exists_notMem_finset
        ((textPrefix s t++[s t]).toFinset ∪ outputs plan backup inf s t)
      exact ⟨pick.choose_spec.2,Or.inr pick.choose_spec.1⟩
  exact ⟨fun mem => dec.1 (Finset.mem_union_left _ (List.mem_toFinset.mpr mem)),
    fun i hi eq => dec.1 (Finset.mem_union_right _ ((mem_outputs ..).mpr ⟨i,hi,eq⟩)),dec.2⟩

theorem credited {s : ℕ → V} {t : ℕ} {y : V} (p : plan (textPrefix s t) (s t) = some y)
    (fresh : y ∉ textPrefix s (t+1)) : y ∈ range (play plan backup inf s) := by
  by_cases old : y ∈ outputs plan backup inf s t
  · obtain ⟨i,_,eq⟩ := (mem_outputs ..).mp old; exact ⟨i,eq⟩
  · refine ⟨t,?_⟩
    rw [output_eq]
    unfold chosen
    have clear : y ∉ (textPrefix s t++[s t]).toFinset ∪ outputs plan backup inf s t := by
      rw [←textPrefix_succ]; simp [old,fresh]
    have ex : ∃ v, plan (textPrefix s t) (s t) = some v ∧ v ∉ (textPrefix s t++[s t]).toFinset ∪ outputs plan backup inf s t := ⟨y,p,clear⟩
    dsimp only
    rw [dif_pos ex]
    exact Option.some.inj (ex.choose_spec.1.symm.trans p)

end
end GenLimit.KleinbergWei.Banach.LocalReplies
