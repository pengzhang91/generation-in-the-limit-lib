import GenLimit.Support.ComputableSearch

/-!
# Total nonadaptive oracle procedures

A procedure computes a finite query list, receives the oracle's answers in
that order, and applies a computable postprocessor. Query formation is
primitive recursive and the postprocessor is computable. Thus no arbitrary
function or unbounded oracle-dependent branching is hidden in the program.
-/

namespace GenLimit.Support

structure TruthTableProgram where
  queries : List ℕ → List ℕ
  queries_primrec : Primrec queries
  output : List ℕ × List ℕ → ℕ
  output_computable : Computable output

def TruthTableProgram.run (P : TruthTableProgram) (oracle : ℕ → ℕ) (xs : List ℕ) : ℕ :=
  P.output (xs, (P.queries xs).map oracle)

/-- Recover the answer to a queried code. Duplicate queries are harmless. -/
def tableLookup (queries answers : List ℕ) (code : ℕ) : ℕ :=
  (answers[queries.idxOf code]?).getD 0

theorem tableLookup_map (queries : List ℕ) (oracle : ℕ → ℕ) (code : ℕ)
    (h : code ∈ queries) : tableLookup queries (queries.map oracle) code = oracle code := by
  simp [tableLookup, List.getElem?_map, List.getElem?_idxOf h]

open scoped Classical in
theorem firstTrue_eq_least {α : Type*} (p : α → ℕ → Bool) (a : α) (n : ℕ)
    (R : ℕ → Prop) [DecidablePred R]
    (hp : ∀ i < n, p a i = true ↔ R i) (hR : ∀ i, R i → i < n) :
    (firstTrue p a n).getD 0 = if h : ∃ i, R i then Nat.find h else 0 := by
  classical
  by_cases h : ∃ i, R i
  · rw [dif_pos h]
    have hn : firstTrue p a n ≠ none := by
      intro hnone
      have hf := (firstTrue_eq_none_iff p a n).mp hnone (Nat.find h)
        (hR _ (Nat.find_spec h))
      have ht := (hp _ (hR _ (Nat.find_spec h))).mpr (Nat.find_spec h)
      simp [ht] at hf
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hn
    rw [hj]
    apply Nat.le_antisymm
    · exact firstTrue_le_of_true hj (hR _ (Nat.find_spec h))
        ((hp _ (hR _ (Nat.find_spec h))).mpr (Nat.find_spec h))
    · exact Nat.find_min' h ((hp j (firstTrue_spec hj).1).mp (firstTrue_spec hj).2.1)
  · rw [dif_neg h]
    have hn : firstTrue p a n = none := (firstTrue_eq_none_iff p a n).mpr (by
      intro i hi
      apply Bool.eq_false_of_not_eq_true
      intro ht
      exact h ⟨i, (hp i hi).mp ht⟩)
    rw [hn]
    rfl

end GenLimit.Support
