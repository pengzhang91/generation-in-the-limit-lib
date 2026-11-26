import GenLimit.Paper16_ComplexityBarriers.PatternBlocks
import Mathlib.Data.List.FinRange

/-! # Finite intersections of non-erasing pattern languages -/
namespace GenLimit.ComplexityBarriers.Patterns
open List
open scoped Classical
noncomputable section

def repeatedPattern (n : ℕ) : Pattern :=
  (range n).flatMap qpat ++ (range n).flatMap rpat

def squarePattern : Pattern := [.inr 0,.inr 0]

private theorem flatMap_length_const (l : List α) (f : α → List β) (c : ℕ) (hf : ∀ i ∈ l, (f i).length = c) :
    (l.flatMap f).length = c*l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [flatMap_cons,length_append,hf a (by simp),ih (fun i hi ↦ hf i (by simp [hi])),length_cons,Nat.mul_succ,Nat.add_comm]

theorem repeatedPattern_size (n : ℕ) : (repeatedPattern n).length = 44*n := by
  simp only [repeatedPattern,length_append,flatMap_length_const _ _ 22 (fun i _ ↦ qpat_length i),
    flatMap_length_const _ _ 22 (fun i _ ↦ rpat_length i),length_range]
  omega

theorem eval_repeated (v : ℕ → List Bool) (n) : eval v (repeatedPattern n) =
    (range n).flatMap (fun i ↦ qword (v i)) ++ (range n).flatMap (fun i ↦ rword (v i)) := by
  simp only [eval,repeatedPattern,flatMap_append,flatMap_assoc]
  change (range n).flatMap (fun i ↦ eval v (qpat i)) ++ (range n).flatMap (fun i ↦ eval v (rpat i)) = _
  simp

private theorem mem_square {w : List Bool} : w ∈ language squarePattern ↔ ∃ x : List Bool, x ≠ [] ∧ x ++ x = w := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨v 0,hv 0,by simp [eval,squarePattern]⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨fun _ ↦ x,fun _ ↦ hx,by simp [eval,squarePattern]⟩

theorem square_infinite : (language squarePattern).Infinite := by
  let f := fun i : ℕ ↦ replicate (i+1) false ++ replicate (i+1) false
  have hi : Function.Injective f := by intro i j h; have := congrArg List.length h; simp [f] at this; omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨i,rfl⟩
  exact mem_square.mpr ⟨_,by simp,rfl⟩

theorem repeated_infinite {n : ℕ} (hn : 0 < n) : (language (repeatedPattern n)).Infinite := by
  let v := fun k : ℕ ↦ fun _ : ℕ ↦ List.replicate (k+1) false
  let f := fun k ↦ eval (v k) (repeatedPattern n)
  have len (k) : (f k).length = (4*(k+1)+18)*(2*n) := by
    simp [f,eval_repeated,v,qword_length,rword_length]; ring
  have hi : Function.Injective f := by
    intro i j h; have hh := congrArg List.length h; rw [len,len] at hh
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2*n) hh
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨k,rfl⟩
  exact ⟨v k,fun _ ↦ by simp [v],rfl⟩

private theorem finite_inter (n) : (language (repeatedPattern n) ∩ language squarePattern).Finite := by
  apply (shortWords Bool (100*n+1)).finite_toSet.subset
  rintro w ⟨⟨v,_,hv⟩,hs⟩
  obtain ⟨x,_,hx⟩ := mem_square.mp hs
  rw [eval_repeated] at hv
  have hh := hv.trans hx.symm
  have hl := congrArg List.length hh
  simp only [length_append] at hl
  have hlen := same_block_lengths (range n) v
  obtain ⟨h₁,h₂⟩ := split_eq hh (by omega)
  have hb := small_half (range n) v (h₁.trans h₂.symm)
  rw [h₁,length_range] at hb
  rw [←hx,Finset.mem_coe,mem_shortWords,length_append]; omega

private def half (n : ℕ) (f : Fin n → Bool) := encode (ofFn f)

private theorem half_nonempty {n : ℕ} (hn : 0 < n) (b : Fin n → Bool) : half n b ≠ [] := by
  intro h
  have he : encode (ofFn b) = encode [] := h
  have := congrArg List.length (encode_injective he)
  simp at this; omega

private theorem realized {n : ℕ} (hn : 0 < n) (b : Fin n → Bool) :
    half n b ++ half n b ∈ language (repeatedPattern n) ∩ language squarePattern := by
  refine ⟨?_,mem_square.mpr ⟨_,half_nonempty hn b,rfl⟩⟩
  let v := fun i : ℕ ↦ if h : i < n then choice (b ⟨i,h⟩) else [false]
  refine ⟨v,fun i ↦ by dsimp [v]; split <;> first | apply choice_nonempty | decide,?_⟩
  have qr (i) : qword (v i) = rword (v i) ∨ n ≤ i := by
    by_cases h : i < n
    · exact Or.inl (by simpa [v,h] using choice_solution (b ⟨i,h⟩))
    · exact Or.inr (by omega)
  have he : (range n).flatMap (fun i ↦ qword (v i)) = (range n).flatMap (fun i ↦ rword (v i)) := by
    apply flatMap_congr; intro i hi; exact (qr i).resolve_right (Nat.not_le_of_lt (mem_range.mp hi))
  rw [eval_repeated,←he]
  suffices eq : (range n).flatMap (fun i ↦ qword (v i)) = half n b by rw [eq]
  rw [←List.map_coe_finRange n]
  simp only [half,encode,ofFn_eq_map,flatMap_map]
  apply flatMap_congr; intro i _; simp [v,i.isLt]

theorem pattern_lower (n : ℕ) (hn : 0 < n) :
    ∃ p q : Pattern, p.length = 44*n ∧ q.length = 2 ∧ (language p).Infinite ∧
      (language q).Infinite ∧ language p ≠ language q ∧
      ¬ MGeneratable {language p,language q} (2^n) := by
  let f := fun b : Fin n → Bool ↦ half n b ++ half n b
  have hi : Function.Injective f := by
    intro b c hh
    have hl := congrArg List.length hh
    simp [f] at hl
    exact ofFn_injective (encode_injective (split_eq hh (by omega)).1)
  have hc := Set.ncard_le_ncard (show Set.range f ⊆ language (repeatedPattern n) ∩ language squarePattern from
    fun _ ⟨b,hb⟩ ↦ hb ▸ realized hn b) (finite_inter n)
  rw [Set.ncard_range_of_injective hi,Nat.card_eq_fintype_card] at hc
  have hne : language (repeatedPattern n) ≠ language squarePattern := by
    intro he
    exact square_infinite (by simpa [he] using finite_inter n)
  refine ⟨repeatedPattern n,squarePattern,repeatedPattern_size n,rfl,repeated_infinite hn,square_infinite,hne,pair_obstruction (finite_inter n) ?_⟩
  simpa using hc

/-- The natural-number zero case would require an infinite language of
a length-zero pattern, which generates precisely the empty word. -/
theorem no_infinite_empty_pattern (p : Pattern) (hp : p.length = 0) : (language p).Finite := by
  obtain rfl := List.length_eq_zero_iff.mp hp
  apply (Set.finite_singleton ([] : List Bool)).subset
  rintro _ ⟨v,_,rfl⟩; rfl

end
end GenLimit.ComplexityBarriers.Patterns
