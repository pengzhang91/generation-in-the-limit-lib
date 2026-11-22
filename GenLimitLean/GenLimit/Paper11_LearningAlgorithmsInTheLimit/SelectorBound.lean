import GenLimit.Paper11_LearningAlgorithmsInTheLimit.EffectiveTables
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.NativeDiagonal

/-! # Computing a bound from any effective selector of legal teaching inputs

Dovetail bounded simulations on the selected finite list. By legality every
selected computation eventually halts, so the search terminates on every
table, including a partial teacher with an empty domain. -/
namespace GenLimit.LearningAlgorithmsLimit.EffectiveTable
open NativeTape
variable {Γ α : Type} [Inhabited Γ] [Primcodable Γ] [Primcodable α]

private def sumBy (f : B → ℕ) (l : List B) := l.foldr (fun x k ↦ f x + k) 0

private theorem sum_prim [Primcodable B] {f : B → ℕ} (hf : Primrec f) : Primrec (sumBy f) :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp (hf.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂)

private theorem sum_zero (f : B → ℕ) (l : List B) : sumBy f l = 0 ↔ ∀ x ∈ l, f x = 0 := by
  induction l with
  | nil => simp [sumBy]
  | cons a l ih => change f a + sumBy f l = 0 ↔ _; simp [ih]

private theorem le_sum {f : B → ℕ} {x : B} {l : List B} (hx : x ∈ l) : f x ≤ sumBy f l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    change _ ≤ f a + sumBy f l
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · exact (ih h).trans (Nat.le_add_left _ _)

private def capacity (c : Conf Γ) := c.2.1.length + 1 + c.2.2.2.length

private theorem capacity_prim : Primrec (capacity (Γ := Γ)) :=
  Primrec.nat_add.comp (Primrec.succ.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

variable (ι : α ↪ Γ)

private def trial (T : Table Γ) (xs : List (List α)) (n : ℕ) : Option ℕ :=
  let cs := xs.map (fun x ↦ run ι T x n)
  if sumBy Prod.fst cs = 0 then some (sumBy capacity cs) else none

private theorem trial_prim [Finite α] :
    Primrec (fun p : (Table Γ × List (List α)) × ℕ ↦ trial ι p.1.1 p.1.2 p.2) := by
  have cs : Primrec (fun p : (Table Γ × List (List α)) × ℕ ↦ p.1.2.map (fun x ↦ run ι p.1.1 x p.2)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.fst) (((run_prim ι).comp
      ((((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).pair
        (Primrec.snd.comp Primrec.fst))).to₂)
  exact Primrec.ite (Primrec.eq.comp ((sum_prim Primrec.fst).comp cs) (Primrec.const 0))
    (Primrec.option_some.comp ((sum_prim capacity_prim).comp cs)) (Primrec.const none)

private theorem stopped {T : Table Γ} {x n m} (hn : (run ι T x n).1 = 0) (hm : n ≤ m) :
    run ι T x m = run ι T x n := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm]
  unfold run
  rw [Function.iterate_add_apply]
  exact Function.iterate_fixed (show step T (run ι T x n) = run ι T x n by simp [step,hn]) j

variable [Fintype Γ]

private theorem physical_witness [DecidableEq Γ] {T : Table Γ} {x y}
    (h : wordSem ι (unpack T) x = some y) :
    ∃ n, (run ι T x n).1 = 0 ∧ y.length ≤ capacity (run ι T x n) := by
  obtain ⟨n,hr⟩ := run_of_wordSem ι h
  unfold TuringProgram.runWithin at hr
  simp only [wordIO] at hr
  rw [← run_eq ι T x n] at hr
  split at hr
  · rename_i hs
    exact ⟨n,hs,output_capacity ι _ hr⟩
  · contradiction

private theorem trial_exists [DecidableEq Γ] (T : Table Γ) (xs : List (List α))
    (legal : ∀ x ∈ xs, x ∈ wordDomain ι (unpack T)) : ∃ n v, trial ι T xs n = some v := by
  have all : ∃ n, ∀ x ∈ xs, (run ι T x n).1 = 0 := by
    induction xs with
    | nil => exact ⟨0,by simp⟩
    | cons x xs ih =>
      obtain ⟨t,ht⟩ := ih (fun a ha ↦ legal a (List.mem_cons_of_mem _ ha))
      obtain ⟨y,hy⟩ := legal x List.mem_cons_self
      obtain ⟨s,hs,_⟩ := physical_witness ι hy
      refine ⟨max s t,fun a ha ↦ ?_⟩
      rcases List.mem_cons.mp ha with rfl | hm
      · simpa only [stopped ι hs (Nat.le_max_left s t)] using hs
      · simpa only [stopped ι (ht a hm) (Nat.le_max_right s t)] using ht a hm
  obtain ⟨n,hn⟩ := all
  refine ⟨n,_,if_pos ((sum_zero _ _).mpr ?_)⟩
  intro c hc
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
  exact hn x hx

private theorem trial_bound [DecidableEq Γ] {T : Table Γ} {xs n v}
    (h : trial ι T xs n = some v) {x} (hx : x ∈ xs) {y} (hy : wordSem ι (unpack T) x = some y) :
    y.length ≤ v := by
  obtain ⟨s,hs,hlen⟩ := physical_witness ι hy
  simp only [trial] at h
  split at h
  · rename_i hall
    obtain rfl := Option.some.inj h
    have hx' : run ι T x n ∈ xs.map (fun a ↦ run ι T a n) := List.mem_map.mpr ⟨x,hx,rfl⟩
    have hn := (sum_zero _ _).mp hall _ hx'
    have he : run ι T x s = run ι T x n :=
      (stopped ι hs (Nat.le_max_left s n)).symm.trans (stopped ι hn (Nat.le_max_right s n))
    rw [he] at hlen
    exact hlen.trans (le_sum hx')
  · contradiction

/-- The bound is total computable on the literal finite-table syntax. -/
theorem selector_capacity [Finite α] [DecidableEq Γ] (C : Table Γ → List (List α)) (hc : Computable C)
    (legal : ∀ T x, x ∈ C T → x ∈ wordDomain ι (unpack T)) :
    ∃ f : Table Γ → ℕ, Computable f ∧ ∀ T x, x ∈ C T →
      ∀ y, wordSem ι (unpack T) x = some y → y.length ≤ f T := by
  classical
  let val (T : Table Γ) := Nat.rfindOpt (trial ι T (C T))
  have total (T) : (val T).Dom := Nat.rfindOpt_dom.mpr (trial_exists ι T (C T) (legal T))
  let f (T) := (val T).get (total T)
  have hp : Partrec val := Partrec.rfindOpt (((trial_prim ι).to_comp.comp
    ((Computable.fst.pair (hc.comp Computable.fst)).pair Computable.snd)).to₂)
  refine ⟨f,hp.of_eq (fun T ↦ Part.eq_some_iff.mpr (Part.get_mem (total T))),?_⟩
  intro T x hx y hy
  obtain ⟨n,hn⟩ := Nat.rfindOpt_spec (Part.get_mem (total T))
  exact trial_bound ι hn hx hy

end GenLimit.LearningAlgorithmsLimit.EffectiveTable
