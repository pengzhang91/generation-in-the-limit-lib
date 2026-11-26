import GenLimit.Paper26_IdentificationWithComputationalTrace.VersionSpace
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import GenLimit.Support.BinaryWords

/-! # Finite control with observed memory

The transition table reads a finite observation of memory and chooses a
finite instruction. The memory itself can be unbounded. The complete memory
is included in every configuration passed to the edit relation.
-/
namespace GenLimit.ComputationalTrace.Control

structure Device (μ O A : Type) where
  load : List Bool → μ
  read : μ → O
  act : μ → A → μ
  terminal : μ → Bool := fun _ => true

structure Machine (σ O A : Type) where
  initial : σ
  final : σ → Bool
  table : σ → O → Option (σ × A)

variable {μ O A σ : Type} (D : Device μ O A) (M : Machine σ O A)
abbrev Frame (σ μ : Type) := σ × μ

def move (c : Frame σ μ) : Option (Frame σ μ) :=
  (M.table c.1 (D.read c.2)).map fun e => (e.1, D.act c.2 e.2)

def isFinal (c : Frame σ μ) : Bool := D.terminal c.2 && M.final c.1

inductive Finish (D : Device μ O A) (M : Machine σ O A) : Frame σ μ → List (Frame σ μ) → Prop
  | halt {c} (yes : isFinal D M c = true) : Finish D M c []
  | next {c d ds} (no : isFinal D M c = false) (step : move D M c = some d)
      (tail : Finish D M d ds) : Finish D M c (d :: ds)

theorem Finish.unique {c xs ys} (hx : Finish D M c xs) (hy : Finish D M c ys) : xs = ys := by
  induction hx generalizing ys with
  | halt yes =>
    cases hy with
    | halt => rfl
    | next no _ _ => simp_all
  | next no step _ ih =>
    cases hy with
    | halt yes => simp_all
    | next _ step' tail =>
      obtain rfl := Option.some.inj (step.symm.trans step')
      exact congrArg (List.cons _) (ih tail)

def acceptsWithin : ℕ → Frame σ μ → Bool
  | 0, c => isFinal D M c
  | n+1, c => isFinal D M c || (move D M c).any (acceptsWithin n)

theorem acceptsWithin_iff (n : ℕ) (c : Frame σ μ) :
    acceptsWithin D M n c = true ↔ ∃ ds, Finish D M c ds ∧ ds.length ≤ n := by
  induction n generalizing c with
  | zero =>
    constructor
    · exact fun h => ⟨[],.halt h,Nat.zero_le _⟩
    · rintro ⟨ds,hd,hh⟩
      cases hd with
      | halt h => exact h
      | next _ _ _ => simp at hh
  | succ n ih =>
    cases h : isFinal D M c with
    | true =>
      exact ⟨fun _ => ⟨[],.halt h,Nat.zero_le _⟩,fun _ => by simp [acceptsWithin,h]⟩
    | false =>
      cases he : move D M c with
      | none =>
        simp only [acceptsWithin,h,he,Bool.false_or,Option.any_none,Bool.false_eq_true,
          false_iff,not_exists]
        rintro _ ⟨hd,_⟩
        cases hd <;> simp_all
      | some d =>
        simp only [acceptsWithin,h,he,Bool.false_or,Option.any_some,ih]
        constructor
        · rintro ⟨ds,hh,hl⟩
          exact ⟨d :: ds,.next h he hh,Nat.succ_le_succ hl⟩
        · rintro ⟨ds,hh,hl⟩
          cases hh with
          | halt yes => simp_all
          | next _ step tail =>
            obtain rfl := Option.some.inj (he.symm.trans step)
            exact ⟨_,tail, Nat.le_of_succ_le_succ hl⟩

def language : Set (List Bool) :=
  {w | ∃ ds, Finish D M (M.initial,D.load w) ds}

theorem accepted_within {w : List Bool} {n : ℕ}
    (h : acceptsWithin D M n (M.initial,D.load w) = true) : w ∈ language D M := by
  obtain ⟨ds,hl,_⟩ := (acceptsWithin_iff D M _ _).mp h
  exact ⟨ds,hl⟩

abbrev Sample (μ : Type) := List Bool × List (Frame ℕ μ)

/-- Covers and the absence of foreign states apply even to short examples.
The edit bound only applies above the threshold. -/
structure Presentation (D : Device μ O A) (M : Machine ℕ O A)
    (budget : ℕ → List (Frame ℕ μ) → List (Frame ℕ μ) → Prop)
    (s : ℕ → Sample μ) : Prop where
  covers : Set.range (fun n => (s n).1) = language D M
  finiteStates : ∃ Q : Finset ℕ, M.initial ∈ Q ∧
    (∀ q ∈ Q, ∀ o r a, M.table q o = some (r,a) → r ∈ Q) ∧
    ∀ n c, c ∈ (s n).2 → c.1 ∈ Q
  traces : ∀ n, ∃ ds, Finish D M (M.initial,D.load (s n).1) ds ∧
    budget (s n).1.length ((M.initial,D.load (s n).1) :: ds) (s n).2

/-- Changing state names on every configuration preserves a whole accepting
computation whenever the two transition tables agree along that run. -/
theorem Finish.relabel {τ : Type} {N : Machine τ O A} {f : σ → τ} {c ds}
    (h : Finish D M c ds) (ok : ∀ e ∈ c :: ds,
      N.final (f e.1) = M.final e.1 ∧
      (N.table (f e.1) (D.read e.2)) =
        (M.table e.1 (D.read e.2)).map (fun p => (f p.1,p.2))) :
    Finish D N (f c.1,c.2) (ds.map (fun e => (f e.1,e.2))) := by
  induction h with
  | @halt c yes =>
    have hh := (ok c (by simp)).1
    exact .halt (by simpa only [isFinal,hh] using yes)
  | @next c d ds no hm tail ih =>
    have hh := ok c (by simp)
    have hm' : move D N (f c.1,c.2) = some (f d.1,d.2) := by
      unfold move at hm ⊢
      simp only [hh.2,Option.map_map]
      cases he : M.table c.1 (D.read c.2) with
      | none => simp [he] at hm
      | some v =>
        simp only [he,Option.map_some,Option.some.injEq] at hm
        rw [← hm]
        rfl
    exact .next (by simpa only [isFinal,hh.1] using no) hm' (ih fun e he => ok _ (List.mem_cons_of_mem _ he))

end GenLimit.ComputationalTrace.Control
