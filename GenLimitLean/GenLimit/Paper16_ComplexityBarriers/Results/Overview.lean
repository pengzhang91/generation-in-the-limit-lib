import GenLimit.Paper16_ComplexityBarriers.ContextFreeLower
import GenLimit.Paper16_ComplexityBarriers.CoreBridge
import GenLimit.Paper16_ComplexityBarriers.RegularLower
import GenLimit.Paper16_ComplexityBarriers.ProfilePumping
import GenLimit.Paper16_ComplexityBarriers.Patterns

/-! # Paper 16: main results for arXiv:2511.05759v2

The numbering follows *Language Generation: Complexity Barriers and Implications for Learning* by Arenas,
Barceló, Cofré, and Kozachinskiy. A generation threshold counts distinct observed words (Definition 2.2). -/

namespace GenLimit.ComplexityBarriers.Results
open scoped Classical

/-- Theorem 3.1. A partial recursive procedure may diverge outside the infinite-grammar promise. -/
theorem theorem_3_1 :
    ¬ ∃ A : CFG.Description × CFG.Description →. ℕ, Partrec A ∧
      ∀ g h : CFG.Description, (CFG.language g).Infinite → (CFG.language h).Infinite →
        ∃ m ∈ A (g,h), MGeneratable {CFG.language g,CFG.language h} m :=
  CFG.no_computable_bound

/-- Theorem 4.1. Upper and lower sample bounds for finite automata and regular expressions. -/
theorem theorem_4_1 :
    (∀ {α : Type} [Fintype α], 2 ≤ Fintype.card α → ∀ (F : Finset (Set (List α))) (s : ℕ),
      (∀ L ∈ F, L.Infinite) → ((∀ L ∈ F, Automata.NFAAtMost s L) ∨
      (∀ L ∈ F, ∃ r : RegularExpression α, r.matches' = L ∧ Automata.writtenSize r ≤ s-1)) →
      MGeneratable (F : Set (Set (List α))) ((Fintype.card α)^(s^F.card))) ∧
    (∃ k : ℕ, ∀ ℓ n : ℕ, 0 < ℓ → 0 < n → ∃ F : Finset (Set (List Bool)),
      F.card = 2^ℓ ∧ (∀ L ∈ F, L.Infinite ∧ Blocks.DFAAtMost (k*ℓ*n) L ∧
      ∃ r : RegularExpression Bool, r.matches' = L ∧ Automata.writtenSize r ≤ k*ℓ^2*n^2) ∧
      ¬ MGeneratable (F : Set (Set (List Bool))) (2^(n^F.card))) := by
  refine ⟨?_,Blocks.regular_lower⟩
  intro α _ ha F s _ h
  rcases h with hn | hr
  · exact Automata.regular_upper ha F s hn
  · apply Automata.regex_upper ha F s
    intro L hL
    obtain ⟨r,he,hs⟩ := hr L hL
    exact ⟨r,he,(Automata.size_comparison r).1.trans hs⟩

/-- Theorem 5.1. Upper and lower sample bounds for locally threshold testable languages. -/
theorem theorem_5_1 :
    (∀ {α : Type} [Fintype α], 2 ≤ Fintype.card α → ∀ (F : Finset (Set (List α))) (s : ℕ),
      (∀ L ∈ F, L.Infinite) → (∀ L ∈ F, LTT.LTTAtMost s L) →
      MGeneratable (F : Set (Set (List α))) ((Fintype.card α)^(3*(s*F.card)*((s*F.card)^2+1)^2))) ∧
    (∀ n : ℕ, 4 ≤ n → ∃ P Q : LTT.Profile (Fin n),
      P.size ≤ 7*(n+1) ∧ Q.size ≤ 7*(n+1) ∧ P.language.Infinite ∧ Q.language.Infinite ∧
      P.language ≠ Q.language ∧ ¬ MGeneratable {P.language,Q.language} (2^n)) := by
  exact ⟨fun ha F s _ hF ↦ LTT.profile_upper ha F s hF,LTT.profile_lower⟩

/-- Theorem 6.1 with the positive-size convention made explicit for Lean naturals. -/
theorem theorem_6_1 (n : ℕ) :
    (∃ p q : Patterns.Pattern, p.length = 44*n ∧ q.length = 2 ∧ (Patterns.language p).Infinite ∧
      (Patterns.language q).Infinite ∧ Patterns.language p ≠ Patterns.language q ∧
      ¬ MGeneratable {Patterns.language p,Patterns.language q} (2^n)) ↔ 0 < n := by
  refine ⟨?_,Patterns.pattern_lower n⟩
  rintro ⟨p,_,hp,_,hi,_⟩
  by_contra! hn
  have hz : n = 0 := Nat.eq_zero_of_le_zero hn
  exact hi (Patterns.no_infinite_empty_pattern p (by simpa [hz] using hp))

end GenLimit.ComplexityBarriers.Results
