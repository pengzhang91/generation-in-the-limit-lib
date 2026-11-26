import GenLimit.Paper26_IdentificationWithComputationalTrace.Edits
import GenLimit.Support.BinaryWords
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith

namespace GenLimit.ComputationalTrace

/-- A deterministic binary automaton. The target uses natural state names and
a finite control set. Hypotheses below use a fixed finite state type. -/
structure BinaryDFA (σ : Type) where
  initial : σ
  step : σ → Bool → σ
  final : σ → Bool


open List

namespace BinaryDFA
variable {σ : Type} (M : BinaryDFA σ)

def run (q : σ) (w : List Bool) : σ := w.foldl M.step q

def language : Set (List Bool) := {w | M.final (M.run M.initial w) = true}

def trace (M : BinaryDFA σ) (q : σ) : List Bool → List σ
  | [] => [q]
  | a :: xs => q :: trace M (M.step q a) xs

def before (M : BinaryDFA σ) (q : σ) : List Bool → List σ
  | [] => []
  | a :: xs => q :: before M (M.step q a) xs

theorem trace_length (q : σ) (w : List Bool) : (M.trace q w).length = w.length + 1 := by
  induction w generalizing q <;> simp [trace, *]

theorem trace_append (q : σ) (u v : List Bool) :
    M.trace q (u ++ v) = M.before q u ++ M.trace (M.run q u) v := by
  induction u generalizing q <;> simp [trace, before, run, *]

theorem before_sub (q : σ) (u : List Bool) : M.before q u <+ M.trace q u := by
  induction u generalizing q with
  | nil => simp [before, trace]
  | cons a xs ih => exact (ih _).cons₂ _

/-- Split at an occurrence, preserving the suffix of the original trace. -/
theorem visit {q v : σ} {w : List Bool} (hv : v ∈ M.trace q w) :
    ∃ a b, w = a ++ b ∧ M.run q a = v ∧ M.trace v b <+ M.trace q w := by
  induction w generalizing q with
  | nil =>
    have h : v = q := by simpa [trace] using hv
    subst v
    exact ⟨[], [], rfl, rfl, List.Sublist.refl _⟩
  | cons x xs ih =>
    rcases List.mem_cons.mp hv with rfl | h
    · exact ⟨[], x :: xs, rfl, rfl, List.Sublist.refl _⟩
    · obtain ⟨a,b,hab,he,hs⟩ := ih h
      exact ⟨x :: a,b,by simp [hab],he,hs.cons _⟩

/-- Any reachable state is reached by a path with no repeated state. -/
theorem simple (q : σ) (w : List Bool) :
    ∃ v, M.run q v = M.run q w ∧ (M.trace q v).Nodup := by
  classical
  induction w generalizing q with
  | nil => exact ⟨[], rfl, by simp [trace]⟩
  | cons a xs ih =>
    obtain ⟨v,he,hn⟩ := ih (M.step q a)
    by_cases h : q ∈ M.trace (M.step q a) v
    · obtain ⟨u,z,hv,hu,hz⟩ := M.visit h
      refine ⟨z, ?_, hn.sublist hz⟩
      rw [hv] at he
      simpa only [run,List.foldl_append,show u.foldl M.step (M.step q a) = q from hu] using he
    · exact ⟨a :: v, he, List.nodup_cons.mpr ⟨h,hn⟩⟩

end BinaryDFA

private theorem seen_length {σ : Type} [DecidableEq σ] (S : Finset σ) (xs : List σ)
    (hn : xs.Nodup) : (xs.filter (· ∈ S)).length ≤ S.card := by
  let ys := xs.filter (· ∈ S)
  have hs : ys.toFinset ⊆ S := by
    intro a ha
    simpa using (List.mem_filter.mp (List.mem_toFinset.mp ha)).2
  exact (List.toFinset_card_of_nodup (hn.filter _)).symm.le.trans (Finset.card_le_card hs)

private theorem partition_length {σ : Type} (P : σ → Bool) (xs : List σ) :
    xs.length = (xs.filter P).length + (xs.filter (fun x => ! P x)).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : P a <;> simp [h] <;> omega

abbrev DFAExample := List Bool × List ℕ

structure DFAPresentation (M : BinaryDFA ℕ) (rate : ℝ) (cutoff : ℕ)
    (s : ℕ → DFAExample) : Prop where
  covers : Set.range (fun n => (s n).1) = M.language
  finiteStates : ∃ Q : Finset ℕ, M.initial ∈ Q ∧
    (∀ q ∈ Q, ∀ a, M.step q a ∈ Q) ∧ ∀ n, (s n).2.toFinset ⊆ Q
  error : ∀ n, RateBound rate cutoff (s n).1.length (M.trace M.initial (s n).1) (s n).2

/-- A state on an accepting run has a short access word. The empty observed
state set and an unrestricted corruption on a short example are both allowed. -/
theorem short_dfa_access {M : BinaryDFA ℕ} {rate : ℝ} {cutoff d : ℕ}
    {s : ℕ → DFAExample} (hs : DFAPresentation M rate cutoff s)
    (hd : 1 ≤ (d : ℝ) * (1 - rate)) (S : Finset ℕ)
    (ho : ∀ n q, q ∈ (s n).2 → q ∈ S)
    {u v : List Bool} (ha : u ++ v ∈ M.language) :
    ∃ p, M.run M.initial p = M.run M.initial u ∧
      p.length ≤ cutoff + d * (2 * S.card) := by
  obtain ⟨p,hp,hpn⟩ := M.simple M.initial u
  obtain ⟨z,hz,hzn⟩ := M.simple (M.run M.initial u) v
  let w := p ++ z
  have hw : w ∈ M.language := by
    change M.final (M.run M.initial (p ++ z)) = true
    change M.final (M.run M.initial (u ++ v)) = true at ha
    simpa only [BinaryDFA.run, List.foldl_append] using
      (show M.final (M.run (M.run M.initial p) z) = true by rw [hp, hz]; simpa [BinaryDFA.run,List.foldl_append] using ha)
  refine ⟨p,hp,?_⟩
  by_cases hl : cutoff ≤ w.length
  · obtain ⟨n,hen⟩ := hs.covers.symm ▸ hw
    change (s n).1 = w at hen
    have er := hs.error n
    rw [hen] at er
    obtain ⟨k,hk,hcost⟩ := er hl
    let tr := M.trace M.initial w
    have hhidden := hk.hidden_le (fun q => decide (q ∈ S)) (by simpa using ho n)
    have hpart := partition_length (fun q => decide (q ∈ S)) tr
    have hseen : (tr.filter (· ∈ S)).length ≤ 2 * S.card := by
      have h₁ := seen_length S _ (hpn.sublist (M.before_sub M.initial p))
      have h₂ := seen_length S _ hzn
      simp only [tr,w,BinaryDFA.trace_append,hp,List.filter_append,List.length_append]
      omega
    have hsum : tr.length ≤ 2 * S.card + k := by
      exact hpart.le.trans (Nat.add_le_add hseen hhidden)
    change (k : ℝ) ≤ rate * tr.length at hcost
    have hratio : (tr.length : ℝ) ≤ d * (2 * (S.card : ℝ)) := by
      have e₁ : (tr.length : ℝ) ≤ 2 * (S.card : ℝ) + k := by exact_mod_cast hsum
      have e₂ := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg tr.length : (0 : ℝ) ≤ _)
      have e₃ := mul_le_mul_of_nonneg_left (le_trans e₁ (add_le_add_left hcost _))
        (Nat.cast_nonneg d : (0 : ℝ) ≤ _)
      nlinarith
    have hh : tr.length ≤ d * (2 * S.card) := by exact_mod_cast hratio
    simp [tr,w,BinaryDFA.trace_length] at hh
    omega
  · simp [w] at hl
    omega

end GenLimit.ComputationalTrace
