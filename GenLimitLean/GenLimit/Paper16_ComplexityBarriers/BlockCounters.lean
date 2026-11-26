import GenLimit.Paper16_ComplexityBarriers.Threshold
import Mathlib.Data.List.Sort

/-! # Ordered counters for the regular-language lower bound

A letter below the monitored address resets its counter, an equal letter
increments it, and a greater letter leaves the counter unchanged. The
least address in any nonempty interval increases its counter
at least once in that interval. -/

namespace GenLimit.ComplexityBarriers.Blocks
open List
open scoped Classical
variable {D : Type*} [LinearOrder D]

def tick (n : ℕ) (d x : D) (c : ℕ) : Option ℕ :=
  if x < d then some 0 else if x = d then if c < n then some (c+1) else none else some c

def run (n : ℕ) (d : D) (c : ℕ) : List D → Option ℕ
  | [] => some c
  | x::xs => (tick n d x c).bind (fun j ↦ run n d j xs)

def Good (n : ℕ) (d : D) (xs : List D) := ∃ c, run n d 0 xs = some c

theorem run_append (n : ℕ) (d : D) (c : ℕ) (u v : List D) :
    run n d c (u++v) = (run n d c u).bind (fun j ↦ run n d j v) := by
  induction u generalizing c with
  | nil => rfl
  | cons x u ih => simp only [List.cons_append,run,ih,Option.bind_assoc]

theorem tick_le {n c k : ℕ} {d x : D} (hc : c ≤ n) (h : tick n d x c = some k) : k ≤ n := by
  unfold tick at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> omega

theorem run_le {n c k : ℕ} {d : D} (hc : c ≤ n) (xs : List D) (h : run n d c xs = some k) : k ≤ n := by
  induction xs generalizing c with
  | nil => simp only [run,Option.some.injEq] at h; exact h ▸ hc
  | cons x xs ih =>
    change (tick n d x c).bind _ = _ at h
    obtain ⟨j,hj,hk⟩ := Option.bind_eq_some_iff.mp h
    exact ih (tick_le hc hj) hk

private theorem strict_interval {n c k : ℕ} {d : D} (xs : List D)
    (hlo : ∀ x ∈ xs, d ≤ x) (h : run n d c xs = some k) :
    c ≤ k ∧ (d ∈ xs → c < k) := by
  induction xs generalizing c with
  | nil => simp [run] at h; simp [h]
  | cons x xs ih =>
    have hx := hlo x List.mem_cons_self
    have hl := fun y (hy : y ∈ xs) ↦ hlo y (List.mem_cons_of_mem _ hy)
    change (tick n d x c).bind _ = _ at h
    obtain ⟨j,hj,hk⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨h₁,h₂⟩ := ih hl hk
    by_cases he : x=d
    · subst x
      simp only [tick,lt_irrefl,if_false,if_true] at hj
      split at hj
      · have hv := Option.some.inj hj
        exact ⟨by omega,fun _ ↦ by omega⟩
      · contradiction
    · simp [tick,not_lt.mpr hx,he] at hj
      exact ⟨hj ▸ h₁,fun hx ↦ hj ▸ h₂ ((List.mem_cons.mp hx).resolve_left (Ne.symm he))⟩

/-- The intersection has bounded word length, even though each individual
counter resets arbitrarily often. -/
theorem common_length [Fintype D] (n : ℕ) (w : List D) (hw : ∀ d, Good n d w) :
    w.length < (n+1)^(Fintype.card D) := by
  have prefix_ok (i : ℕ) (d : D) : ∃ c : Fin (n+1), run n d 0 (w.take i) = some c.val := by
    obtain ⟨k,hk⟩ := hw d
    rw [←List.take_append_drop i w,run_append] at hk
    obtain ⟨j,hj,_⟩ := Option.bind_eq_some_iff.mp hk
    exact ⟨⟨j,Nat.lt_succ_of_le (run_le (Nat.zero_le n) _ hj)⟩,hj⟩
  choose c hc using prefix_ok
  let f := fun i : Fin (w.length+1) ↦ c i.val
  have hstrict (i j : Fin (w.length+1)) (hij : i < j) : f i ≠ f j := by
    intro he
    have hlen (i : Fin (w.length+1)) : (w.take i.val).length = i.val := by simp [Nat.le_of_lt_succ i.isLt]
    have hpre := List.prefix_of_prefix_length_le (List.take_prefix i.val w) (List.take_prefix j.val w)
      (by rw [hlen,hlen]; exact Nat.le_of_lt hij)
    obtain ⟨v,hv⟩ := hpre
    have hne : v ≠ [] := by
      rintro rfl
      have hh := congrArg List.length hv
      simp [hlen] at hh
      exact (Nat.ne_of_lt hij) hh
    obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil v hne
    have ht : v.toFinset.Nonempty := ⟨a,List.mem_toFinset.mpr ha⟩
    let d := v.toFinset.min' ht
    have hd : d ∈ v := List.mem_toFinset.mp (Finset.min'_mem _ _)
    have hl (x) (hx : x ∈ v) : d ≤ x := Finset.min'_le _ _ (List.mem_toFinset.mpr hx)
    have hrun := hc j.val d
    rw [←hv,run_append,hc] at hrun
    have hs := (strict_interval v hl hrun).2 hd
    have eqv := congrArg Fin.val (congrFun he d)
    exact (Nat.ne_of_lt hs) eqv
  have hi : Function.Injective f := by
    intro i j hh
    rcases lt_trichotomy i j with h|h|h
    · exact (hstrict i j h hh).elim
    · exact h
    · exact (hstrict j i h hh.symm).elim
  have hh := Fintype.card_le_of_injective f hi
  simpa using hh

theorem run_larger (n c : ℕ) (d : D) (xs : List D) (hl : ∀ x ∈ xs, d < x) :
    run n d c xs = some c := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := hl x List.mem_cons_self
    simpa [run,tick,not_lt.mpr hh.le,Ne.symm hh.ne] using ih (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy))

theorem run_absent (n : ℕ) (d : D) (xs : List D) (h : d ∉ xs) : run n d 0 xs = some 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hn : d ≠ x ∧ d ∉ xs := by simpa only [List.mem_cons,not_or] using h
    by_cases hx : x < d <;> simp [run,tick,hx,Ne.symm hn.1,ih hn.2]

theorem run_replicate_self (n c m : ℕ) (d : D) :
    run n d c (List.replicate m d) = if c+m ≤ n then some (c+m) else if m=0 then some c else none := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [List.replicate_succ,run]
    by_cases hc : c < n
    · simp [tick,hc,ih,Nat.add_left_comm,Nat.add_comm]
      split_ifs <;> simp_all
      omega
    · have hn : ¬ c+(m+1) ≤ n := by omega
      simp [tick,hc,hn]

private def longWord (n : ℕ) : List D → List D
  | [] => []
  | d::ds =>
    let u := longWord n ds
    (List.replicate n (u++[d])).flatten ++ u

omit [LinearOrder D] in
private theorem long_mem {n : ℕ} {ds : List D} {x : D} (hx : x ∈ longWord n ds) : x ∈ ds := by
  induction ds with
  | nil => simp [longWord] at hx
  | cons d ds ih =>
    simp only [longWord,List.mem_append,List.mem_flatten,List.mem_replicate] at hx
    rcases hx with ⟨_,⟨_,rfl⟩,hh⟩ | hh
    · rcases List.mem_append.mp hh with hu | he
      · exact List.mem_cons_of_mem _ (ih hu)
      · simp_all
    · exact List.mem_cons_of_mem _ (ih hh)

private theorem run_copies (n : ℕ) (d : D) (u : List D) (hu : run n d 0 u = some 0) (k : ℕ) :
    run n d 0 (List.replicate k u).flatten = some 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,run_append,hu,ih]

private theorem long_good (n : ℕ) (ds : List D) (hs : ds.Pairwise (· < ·)) (d : D) :
    Good n d (longWord n ds) := by
  induction ds with
  | nil => exact ⟨0,rfl⟩
  | cons a ds ih =>
    obtain ⟨ha,hds⟩ := List.pairwise_cons.mp hs
    let u := longWord n ds
    have hu (x) (hx : x ∈ u) := ha x (long_mem hx)
    rcases lt_trichotomy d a with h|rfl|h
    · exact ⟨0,run_larger n 0 d _ (fun x hx ↦ by
        rcases List.mem_cons.mp (long_mem hx) with rfl|hx
        · exact h
        · exact h.trans (ha _ hx))⟩
    · have hh (i k : ℕ) (hik : i+k ≤ n) :
          run n d i (List.replicate k (u++[d])).flatten = some (i+k) := by
        induction k generalizing i with
        | zero => simp [run]
        | succ k ih =>
          have hi : i < n := by omega
          rw [List.replicate_succ,List.flatten_cons,run_append,run_append,run_larger n i d u hu]
          simpa [run,tick,hi,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1) (by omega)
      refine ⟨n,?_⟩
      change run n d 0 (_ ++ u) = some n
      rw [run_append,hh 0 n (by omega)]
      simpa using run_larger n n d u hu
    · obtain ⟨k,hk⟩ := ih hds
      have hreset : run n d 0 (u++[a]) = some 0 := by
        rw [run_append,show run n d 0 u = some k from hk]; simp [run,tick,h]
      refine ⟨k,?_⟩
      change run n d 0 (_ ++ u) = some k
      rw [run_append,run_copies n d _ hreset]
      exact hk

omit [LinearOrder D] in
private theorem long_length (n : ℕ) (ds : List D) (hne : ds ≠ []) :
    n^ds.length ≤ (longWord n ds).length := by
  induction ds with
  | nil => contradiction
  | cons d ds ih =>
    have hl (k : ℕ) (u : List D) : (List.replicate k u).flatten.length = k*u.length := by
      induction k with
      | zero => simp
      | succ k ih => simp [List.replicate_succ,ih,Nat.succ_mul,Nat.add_comm]
    cases ds with
    | nil => simp [longWord]
    | cons e es =>
      have hi := ih (List.cons_ne_nil _ _)
      change n^((e::es).length+1) ≤ ((List.replicate n (longWord n (e::es) ++ [d])).flatten ++ longWord n (e::es)).length
      rw [pow_succ,List.length_append,hl,List.length_append,List.length_singleton]
      apply (Nat.mul_le_mul_right n hi).trans
      change (longWord n (e::es)).length*n ≤ n*((longWord n (e::es)).length+1)+(longWord n (e::es)).length
      rw [Nat.mul_add,Nat.mul_comm _ n]; omega

/-- One address sequence can support one independent free bit per block. -/
theorem exists_long_common [Fintype D] [Nonempty D] (n : ℕ) :
    ∃ w : List D, n^(Fintype.card D) ≤ w.length ∧ ∀ d, Good n d w := by
  let ds := (Finset.univ : Finset D).sort (· ≤ ·)
  have hds : ds.Pairwise (· < ·) := Finset.sort_sorted_lt _
  have hl : ds.length = Fintype.card D := by simp [ds]
  have hn : ds ≠ [] := by intro hh; simp [hh] at hl; exact Fintype.card_ne_zero hl.symm
  exact ⟨longWord n ds,hl ▸ long_length n ds hn,long_good n ds hds⟩

end GenLimit.ComplexityBarriers.Blocks
