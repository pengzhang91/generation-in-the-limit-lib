import GenLimit.Paper26_IdentificationWithComputationalTrace.FiniteControl
import Mathlib.Tactic.Ring

namespace GenLimit.ComputationalTrace.Control
open List

variable {μ O A : Type} (D : Device μ O A) (M : Machine ℕ O A)

private def neighbors (alphabet : List O) (q : ℕ) : List ℕ :=
  q :: alphabet.map fun o => ((M.table q o).map Prod.fst).getD q

def ball (alphabet : List O) (seed : List ℕ) : ℕ → List ℕ
  | 0 => seed
  | n+1 => (ball alphabet seed n).flatMap (neighbors M alphabet)

theorem ball_length (os : List O) (seed : List ℕ) (n : ℕ) :
    (ball M os seed n).length = seed.length * (os.length + 1)^n := by
  have len (xs : List ℕ) : (xs.flatMap (neighbors M os)).length = xs.length * (os.length+1) := by
    induction xs with
    | nil => simp
    | cons q xs ih => simp [neighbors,ih,Nat.add_mul,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  induction n with
  | zero => simp [ball]
  | succ n ih => rw [ball,len,ih,pow_succ,Nat.mul_assoc]

private theorem ball_mono (os : List O) (seed : List ℕ) {n k : ℕ} (hk : n ≤ k) :
    ball M os seed n ⊆ ball M os seed k := by
  induction k, hk using Nat.le_induction with
  | base => exact fun _ h => h
  | succ k _ ih =>
    intro q hq
    exact List.mem_flatMap.mpr ⟨q,ih hq,by simp [neighbors]⟩

private theorem ball_step (os : List O) (hos : ∀ o, o ∈ os) (seed : List ℕ)
    {q d : Frame ℕ μ} {j} (hq : q.1 ∈ ball M os seed j) (he : move D M q = some d) :
    d.1 ∈ ball M os seed (j+1) := by
  unfold move at he
  cases h : M.table q.1 (D.read q.2) with
  | none => simp [h] at he
  | some p =>
    simp only [h, Option.map_some,Option.some.injEq] at he
    subst d
    apply List.mem_flatMap.mpr
    exact ⟨q.1,hq,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨D.read q.2,hos _,by simp [h]⟩)⟩

private theorem ball_finish (os : List O) (hos : ∀ o, o ∈ os) (S : Finset ℕ)
    (seed : List ℕ) (hs : ∀ q ∈ S, q ∈ seed) {c ds} (hf : Finish D M c ds)
    (j : ℕ) (hc : c.1 ∈ ball M os seed j) :
    ∀ e ∈ c :: ds, e.1 ∈ ball M os seed (j + (ds.filter (fun z => decide (z.1 ∉ S))).length) := by
  induction hf generalizing j with
  | halt => simpa using hc
  | @next c d ds no he tail ih =>
    intro e h
    rcases List.mem_cons.mp h with rfl | h
    · exact ball_mono M os seed (Nat.le_add_right ..) hc
    · by_cases hh : d.1 ∈ S
      · have hmem : d.1 ∈ ball M os seed j :=
          ball_mono M os seed (Nat.zero_le j) (hs _ hh)
        simpa [hh] using ih j hmem e h
      · have hmem := ball_step D M os hos seed hc he
        simpa [hh,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (j+1) hmem e h

/-- For a long example, every visited control state lies in the radius-budget
ball from the observed states together with the initial state. -/
theorem cover_finite_error [Fintype O] {S : Finset ℕ} {C : ℕ} {w : List Bool}
    {ds ys : List (Frame ℕ μ)} (hf : Finish D M (M.initial,D.load w) ds)
    (he : ∃ k ≤ C, EditScript k ((M.initial,D.load w) :: ds) ys)
    (hy : ∀ e ∈ ys, e.1 ∈ S) :
    ∀ e ∈ (M.initial,D.load w) :: ds,
      e.1 ∈ ball M (Finset.univ : Finset O).toList (M.initial :: S.toList) C := by
  obtain ⟨k,hk,hed⟩ := he
  have hh := hed.hidden_le (fun e => decide (e.1 ∈ S)) (by simpa using hy)
  have hsub : (ds.filter (fun e => decide (e.1 ∉ S))).length ≤ C := by
    have sub : ds <+ ((M.initial,D.load w) :: ds) := (List.Sublist.refl ds).cons _
    have hb := (sub.filter (fun e => !decide (e.1 ∈ S))).length_le.trans (hh.trans hk)
    simpa using hb
  have hpath := ball_finish D M (Finset.univ : Finset O).toList (by simp) S
    (M.initial :: S.toList) (by simp_all) hf 0 (List.mem_cons_self ..)
  intro e he'
  exact ball_mono M _ _ (by simpa using hsub) (hpath e he')

theorem cover_short_run [Fintype O] {S : Finset ℕ} {n : ℕ} {w : List Bool}
    {ds : List (Frame ℕ μ)} (hf : Finish D M (M.initial,D.load w) ds) (hl : ds.length ≤ n) :
    ∀ e ∈ (M.initial,D.load w) :: ds,
      e.1 ∈ ball M (Finset.univ : Finset O).toList (M.initial :: S.toList) n := by
  have hp := ball_finish D M (Finset.univ : Finset O).toList (by simp) (∅ : Finset ℕ)
    (M.initial :: S.toList) (by simp) hf 0 (List.mem_cons_self ..)
  intro e he
  exact ball_mono M _ _ (by simpa using hl) (hp e he)

theorem seed_ball [Fintype O] (S : Finset ℕ) (n : ℕ) {q : ℕ} (hq : q ∈ S) :
    q ∈ ball M (Finset.univ : Finset O).toList (M.initial :: S.toList) n :=
  ball_mono M _ _ (Nat.zero_le n) (by simp [ball,hq])

end GenLimit.ComputationalTrace.Control
