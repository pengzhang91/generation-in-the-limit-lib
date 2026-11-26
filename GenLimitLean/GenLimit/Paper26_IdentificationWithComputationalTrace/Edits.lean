import GenLimit.Core.Text
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic

/-! # Corruption of computational traces

An alignment charges one for inserting, deleting, or replacing a configuration.
Existence of an alignment at a given budget expresses the edit-distance bound
without computing a minimum. The size threshold always measures the input.
-/
namespace GenLimit.ComputationalTrace

inductive EditScript {α : Type*} : ℕ → List α → List α → Prop
  | nil : EditScript 0 [] []
  | keep (a) : EditScript k xs ys → EditScript k (a :: xs) (a :: ys)
  | delete (a) : EditScript k xs ys → EditScript (k + 1) (a :: xs) ys
  | insert (b) : EditScript k xs ys → EditScript (k + 1) xs (b :: ys)
  | replace (a b) : EditScript k xs ys → EditScript (k + 1) (a :: xs) (b :: ys)

variable {α : Type*}

theorem EditScript.refl (xs : List α) : EditScript 0 xs xs := by
  induction xs with
  | nil => exact .nil
  | cons a _ ih => exact .keep a ih

theorem EditScript.erasePrefix (xs ys : List α) :
    EditScript xs.length (xs ++ ys) ys := by
  induction xs with
  | nil => exact .refl _
  | cons a _ ih => exact .delete a ih

theorem EditScript.eraseSuffix (xs ys : List α) :
    EditScript ys.length (xs ++ ys) xs := by
  induction xs with
  | nil => simpa using (EditScript.erasePrefix ys ([] : List α))
  | cons a xs ih => exact .keep a ih

theorem EditScript.length_bounds {k : ℕ} {xs ys : List α} (e : EditScript k xs ys) :
    xs.length ≤ ys.length + k ∧ ys.length ≤ xs.length + k := by
  induction e <;> simp_all only [List.length_nil, List.length_cons] <;> omega

/-- Each true occurrence of a state absent from the observed trace consumes
a distinct edit, even when the same hidden state occurs more than once. -/
theorem EditScript.hidden_le {k : ℕ} {xs ys : List α} (e : EditScript k xs ys)
    (seen : α → Bool) (hy : ∀ y ∈ ys, seen y = true) :
    (xs.filter fun x => !(seen x)).length ≤ k := by
  induction e with
  | nil => simp
  | keep a e ih =>
    simp [hy a (by simp), ih (fun y h => hy y (by simp [h]))]
  | delete a e ih =>
    specialize ih hy
    cases h : seen a <;> simp [h] <;> omega
  | insert b e ih =>
    exact Nat.le_succ_of_le (ih fun y h => hy y (by simp [h]))
  | replace a b e ih =>
    specialize ih (fun y h => hy y (by simp [h]))
    cases h : seen a <;> simp [h] <;> omega

def RateBound (rate : ℝ) (cutoff inputLength : ℕ) (xs ys : List α) : Prop :=
  cutoff ≤ inputLength → ∃ k, EditScript k xs ys ∧ (k : ℝ) ≤ rate * xs.length

def FiniteBound (budget cutoff inputLength : ℕ) (xs ys : List α) : Prop :=
  cutoff ≤ inputLength → ∃ k ≤ budget, EditScript k xs ys

/-- Only reciprocal positive integer rates are needed for a diminishing rate.
A modulus for all real rates as in Definition 5 supplies each of these bounds. -/
def DiminishingBound (cutoff : ℕ → ℕ) (inputLength : ℕ) (xs ys : List α) : Prop :=
  ∀ d : ℕ, RateBound (1 / ((d : ℝ) + 2)) (cutoff d) inputLength xs ys

/-- A finite envelope gives a common time at which all observations that
ever occur have already appeared. It suffices to bound the observed states,
even if there are infinitely many distinct observed full configurations. -/
theorem finite_observations_stabilize {β : Type*} [DecidableEq β]
    (obs : ℕ → Finset β) (bound : Finset β) (hb : ∀ n, obs n ⊆ bound) :
    ∃ U : Finset β, (∀ a, a ∈ U ↔ ∃ n, a ∈ obs n) ∧
      ∃ T, ∀ t ≥ T, (Finset.range t).biUnion obs = U := by
  classical
  let U := bound.filter fun a => ∃ n, a ∈ obs n
  have memU (a : β) : a ∈ U ↔ ∃ n, a ∈ obs n := by
    simp only [U, Finset.mem_filter, and_iff_right_iff_imp]
    exact fun ⟨n, hn⟩ => hb n hn
  choose idx hi using fun a : U => (memU a).mp a.property
  let T := U.attach.sup idx
  refine ⟨U, memU, T + 1, fun t ht => ?_⟩
  ext a
  rw [Finset.mem_biUnion, memU]
  constructor
  · exact fun ⟨n, _, hn⟩ => ⟨n, hn⟩
  · intro ha
    let b : U := ⟨a, (memU a).mpr ha⟩
    have hb' : idx b ≤ T := Finset.le_sup (f := idx) (U.mem_attach b)
    exact ⟨idx b, Finset.mem_range.mpr (by omega), hi b⟩

end GenLimit.ComputationalTrace
