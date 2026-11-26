import GenLimit.Paper16_ComplexityBarriers.Threshold
import Mathlib.Data.List.Infix
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Permutation
import Mathlib.Data.Fintype.Perm

/-! # Locally threshold testable profiles

Each occurrence is counted at its ending position, so overlaps count.
The empty pattern occurs at every cut, including the initial cut.
Thresholds have unary size. -/
namespace GenLimit.ComplexityBarriers.LTT
open List
open scoped Classical
noncomputable section

inductive Comparison | lt | le | eq | ge | gt deriving DecidableEq

def Comparison.test : Comparison → ℕ → ℕ → Prop
  | .lt, n, t => n < t
  | .le, n, t => n ≤ t
  | .eq, n, t => n = t
  | .ge, n, t => t ≤ n
  | .gt, n, t => t < n

structure Constraint (α : Type*) where
  word : List α
  cmp : Comparison
  bound : ℕ

structure Profile (α : Type*) where
  front : List α
  back : List α
  rules : List (Constraint α)

def occurrences (p w : List α) : ℕ := (w.inits.filter (fun u ↦ decide (p <:+ u))).length

def Profile.language (P : Profile α) : Set (List α) :=
  {w | P.front <+: w ∧ P.back <:+ w ∧ ∀ c ∈ P.rules, c.cmp.test (occurrences c.word w) c.bound}

/-- Symbol count including unary thresholds and an explicit punctuation allowance. -/
def Profile.size (P : Profile α) : ℕ :=
  7 + P.front.length + P.back.length + (P.rules.map (fun c ↦ 5+c.word.length+c.bound)).sum

/-- One token per profile and per comparison, plus the written words and unary thresholds. -/
def Profile.contentSize (P : Profile α) : ℕ :=
  1 + P.front.length + P.back.length + (P.rules.map (fun c ↦ 1+c.word.length+c.bound)).sum

theorem contentSize_le_size (P : Profile α) : P.contentSize ≤ P.size := by
  have hr (cs : List (Constraint α)) :
      (cs.map (fun c ↦ 1+c.word.length+c.bound)).sum ≤ (cs.map (fun c ↦ 5+c.word.length+c.bound)).sum := by
    induction cs with
    | nil => rfl
    | cons c cs ih => exact Nat.add_le_add (by dsimp; omega) ih
  have h := hr P.rules
  unfold Profile.contentSize Profile.size
  omega

def LTTAtMost (s : ℕ) (L : Set (List α)) : Prop :=
  ∃ Ps : List (Profile α), (Ps.map Profile.size).sum ≤ s ∧ L = {w | ∃ P ∈ Ps, w ∈ P.language}

theorem occurrences_snoc (p w : List α) (a : α) :
    occurrences p (w++[a]) = occurrences p w + if p <:+ w++[a] then 1 else 0 := by
  simp [occurrences,List.inits_append]
  split <;> simp_all

theorem suffix_snoc {p w : List α} {a b : α} : p++[b] <:+ w++[a] ↔ b=a ∧ p <:+ w := by
  rw [←List.reverse_prefix]
  simp [List.reverse_prefix]

theorem occurrences_singleton [DecidableEq α] (a : α) (w : List α) : occurrences [a] w = w.count a := by
  induction w using List.reverseRecOn with
  | nil => simp [occurrences]
  | append_singleton w b ih =>
    rw [occurrences_snoc,ih,List.count_append]
    have he : [a] <:+ w++[b] ↔ a=b := by simpa using (suffix_snoc (p := []) (w := w) (b := a) (a := b))
    by_cases h : a=b <;> (simp_all [List.count_singleton] <;> exact Ne.symm h)

private def boundedLetters (T : List α) : Profile α :=
  ⟨[],[], T.map (fun a ↦ ⟨[a],.le,1⟩)⟩

private theorem mem_boundedLetters [DecidableEq α] (T w : List α) :
    w ∈ (boundedLetters T).language ↔ ∀ a ∈ T, w.count a ≤ 1 := by
  simp [Profile.language,boundedLetters,Comparison.test,occurrences_singleton]

private theorem size_boundedLetters (T : List α) : (boundedLetters T).size = 7*(T.length+1) := by
  induction T with
  | nil => rfl
  | cons a l ih => simp [Profile.size,boundedLetters,List.map_map,Function.comp_def] at *; omega

private theorem boundedLetters_infinite [DecidableEq α] {T : List α} (a : α) (h : a ∉ T) :
    (boundedLetters T).language.Infinite := by
  let f := fun n : ℕ ↦ replicate n a
  have hi : Function.Injective f := by intro i j he; simpa [f] using congrArg List.length he
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n,rfl⟩
  rw [mem_boundedLetters]; intro b hb
  have hn : a ≠ b := fun h' ↦ h (h' ▸ hb)
  simp [f,List.count_replicate,hn]

private theorem two_pow_le_factorial {n : ℕ} (hn : 4 ≤ n) : 2^n ≤ n.factorial := by
  induction n,hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ,Nat.factorial_succ,mul_comm (n+1)]
    exact Nat.mul_le_mul ih (by omega)

/-- Two complementary systems of upper bounds. Their intersection contains
all permutations and consists entirely of words with no repeated letter. -/
theorem profile_lower (n : ℕ) (hn : 4 ≤ n) :
    ∃ P Q : Profile (Fin n), P.size ≤ 7*(n+1) ∧ Q.size ≤ 7*(n+1) ∧
      P.language.Infinite ∧ Q.language.Infinite ∧ P.language ≠ Q.language ∧
      ¬ MGeneratable {P.language,Q.language} (2^n) := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let T := (finRange n).erase a
  let P := boundedLetters T
  let Q := boundedLetters [a]
  have ht : a ∉ T := (nodup_finRange n).not_mem_erase
  have hchar (w : List (Fin n)) : w ∈ P.language ∩ Q.language ↔ w.Nodup := by
    change (w ∈ (boundedLetters T).language ∧ w ∈ (boundedLetters [a]).language) ↔ _
    rw [mem_boundedLetters,mem_boundedLetters,nodup_iff_count_le_one]
    constructor
    · rintro ⟨h₁,h₂⟩ x
      by_cases hx : x=a
      · exact h₂ x (by simp [hx])
      · exact h₁ x (by simp [T,List.mem_erase_of_ne hx])
    · exact fun h ↦ ⟨fun x _ ↦ h x,fun x _ ↦ h x⟩
  have hf : (P.language ∩ Q.language).Finite := by
    apply (shortWords (Fin n) (n+1)).finite_toSet.subset
    intro w hw
    apply (mem_shortWords ..).mpr
    have hh := Finset.card_le_univ w.toFinset
    rw [List.toFinset_card_of_nodup ((hchar w).mp hw),Fintype.card_fin] at hh
    omega
  let f := fun e : Equiv.Perm (Fin n) ↦ ofFn e
  have hi : Function.Injective f := fun _ _ h ↦ Equiv.ext (congrFun (ofFn_injective h))
  have hsub : Set.range f ⊆ P.language ∩ Q.language := by
    rintro _ ⟨e,rfl⟩; apply (hchar _).mpr
    rw [show f e = (finRange n).map e from ofFn_eq_map]
    exact (nodup_finRange n).map e.injective
  have hc := Set.ncard_le_ncard hsub hf
  rw [Set.ncard_range_of_injective hi,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hc
  have hP : P.language.Infinite := boundedLetters_infinite a ht
  have hne : P.language ≠ Q.language := by
    intro he
    exact hP (by simpa [←he] using hf)
  refine ⟨P,Q,?_,?_,hP,boundedLetters_infinite b (by simp [a,b,Fin.ext_iff]),hne,pair_obstruction hf ((two_pow_le_factorial hn).trans hc)⟩
  · change (boundedLetters T).size ≤ _
    rw [size_boundedLetters]; gcongr
    exact (List.length_erase_le ..).trans_eq length_finRange
  · change (boundedLetters [a]).size ≤ _
    rw [size_boundedLetters]; simp; omega

end
end GenLimit.ComplexityBarriers.LTT
