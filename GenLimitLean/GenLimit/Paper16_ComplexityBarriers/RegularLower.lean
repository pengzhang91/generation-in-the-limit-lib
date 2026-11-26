import GenLimit.Paper16_ComplexityBarriers.BlockDFA
import GenLimit.Paper16_ComplexityBarriers.BlockExpressions
import GenLimit.Paper16_ComplexityBarriers.CounterExpressions

/-! # The double-exponential lower bound, with both presentation sizes -/
namespace GenLimit.ComplexityBarriers.Blocks
open List RegularExpression
open scoped Classical
noncomputable section

private def packHom (ℓ : ℕ) : _root_.Language (Token ℓ) →+* _root_.Language Bool where
  toFun := packed
  map_zero' := Set.image_empty _
  map_one' := Set.image_singleton
  map_add' := Set.image_union _
  map_mul' _ _ := Set.image_image2_distrib (fun u v ↦ List.flatMap_append (xs := u) (ys := v))

private theorem pack_one : packed (1 : _root_.Language (Token ℓ)) = 1 := (packHom ℓ).map_one
private theorem pack_sum (L K : _root_.Language (Token ℓ)) : packed (L+K) = packed L+packed K := (packHom ℓ).map_add ..
private theorem pack_mul (L K : _root_.Language (Token ℓ)) : packed (L*K) = packed L*packed K := (packHom ℓ).map_mul ..
private theorem pack_star (L : _root_.Language (Token ℓ)) : packed (KStar.kstar L) = KStar.kstar (packed L) := by
  rw [Language.kstar_eq_iSup_pow,Language.kstar_eq_iSup_pow]
  ext w
  change (∃ v ∈ (⨆ i : ℕ, L^i), encode v = w) ↔ _
  simp only [Language.mem_iSup]
  constructor
  · rintro ⟨v,⟨i,hi⟩,rfl⟩
    refine ⟨i,?_⟩
    change encode v ∈ (packHom ℓ L)^i
    rw [←(packHom ℓ).map_pow]
    exact ⟨v,hi,rfl⟩
  · rintro ⟨i,hi⟩
    change w ∈ (packHom ℓ L)^i at hi
    rw [←(packHom ℓ).map_pow] at hi
    obtain ⟨v,hv,rfl⟩ := hi
    exact ⟨v,⟨i,hv⟩,rfl⟩

private def segmentRE (d : Address ℓ) : ℕ → RE
  | 0 => (tokenExpression d .gt).star
  | k+1 => (tokenExpression d .gt).star * (1 + tokenExpression d .eq * segmentRE d k)

private def counterRE (n : ℕ) (d : Address ℓ) : RE :=
  segmentRE d n * (tokenExpression d .lt * segmentRE d n).star

private theorem segment_spec (d : Address ℓ) (k : ℕ) : (segmentRE d k).matches' = packed (segment d k) := by
  induction k with
  | zero => exact (congrArg KStar.kstar (token_spec d .gt)).trans (pack_star (Higher d)).symm
  | succ k ih =>
    simp only [segmentRE,RegularExpression.matches'_mul,RegularExpression.matches'_add,
      RegularExpression.matches'_star,RegularExpression.matches'_epsilon,token_spec,ih,segment,
      pack_mul,pack_sum,pack_star,pack_one]
    rfl

private theorem regex_correct (n : ℕ) (d : Address ℓ) : (counterRE n d).matches' = binaryLanguage n d := by
  have hh : packed (segment d n * cycles n d) = binaryLanguage n d := by
    rw [counter_description]
    ext w
    exact ⟨fun ⟨ts,h,he⟩ ↦ ⟨ts,he,h⟩,fun ⟨ts,he,h⟩ ↦ ⟨ts,h,he⟩⟩
  rw [←hh]
  simp only [counterRE,RegularExpression.matches'_mul,RegularExpression.matches'_star,segment_spec,token_spec,
    cycles,pack_mul,pack_star]
  rfl

private theorem size_segment (d : Address ℓ) (k : ℕ) :
    Automata.regexSize (segmentRE d k) ≤ (k+1)*(2*(8*(ℓ+1)^2)+6) := by
  let B := 8*(ℓ+1)^2
  have h₁ := token_size d .gt
  have h₂ := token_size d .eq
  change Automata.regexSize (tokenExpression d .gt) ≤ B at h₁
  change Automata.regexSize (tokenExpression d .eq) ≤ B at h₂
  change _ ≤ (k+1)*(2*B+6)
  induction k with
  | zero => change Automata.regexSize (tokenExpression d .gt)+1 ≤ 1*(2*B+6); omega
  | succ k ih =>
    change Automata.regexSize (tokenExpression d .gt)+1+
      (1+(Automata.regexSize (tokenExpression d .eq)+Automata.regexSize (segmentRE d k)+1)+1)+1 ≤
        (k+1+1)*(2*B+6)
    rw [Nat.add_mul,one_mul]; omega

theorem binary_regex {ℓ n : ℕ} (hl : 0 < ℓ) (hn : 0 < n) (d : Address ℓ) :
    ∃ r : RE, r.matches' = binaryLanguage n d ∧ Automata.regexSize r ≤ 400*ℓ^2*n^2 := by
  refine ⟨counterRE n d,regex_correct n d,?_⟩
  have hi := size_segment d n
  have ht := token_size d .lt
  let B := 8*(ℓ+1)^2
  let a := ℓ^2
  have ha : 1 ≤ a := Nat.succ_le_of_lt (pow_pos hl 2)
  have hB : B ≤ 32*a := by
    have hh := Nat.pow_le_pow_left (show ℓ+1 ≤ 2*ℓ by omega) 2
    dsimp [B,a]; nlinarith
  have hstep : 2*B+6 ≤ 70*a := by omega
  have hprod := Nat.mul_le_mul (show n+1 ≤ 2*n by omega) hstep
  have hs : Automata.regexSize (segmentRE d n) ≤ 140*(a*n) := hi.trans (hprod.trans_eq (by ring))
  have ha' : a ≤ a*n := by simpa using Nat.mul_le_mul_left a hn
  have hn' : n ≤ n^2 := by simpa [pow_two] using Nat.mul_le_mul_right n hn
  have hrest := Nat.mul_le_mul_left a hn'
  change Automata.regexSize (tokenExpression d .lt) ≤ B at ht
  change Automata.regexSize (segmentRE d n)+(Automata.regexSize (tokenExpression d .lt)+Automata.regexSize (segmentRE d n)+1+1)+1 ≤ 400*a*n^2
  rw [Nat.mul_assoc]
  omega

/-- The same family simultaneously admits small deterministic automata and small regexes. -/
theorem regular_lower : ∃ k : ℕ, ∀ ℓ n : ℕ, 0 < ℓ → 0 < n →
    ∃ F : Finset (Set (List Bool)), F.card = 2^ℓ ∧ (∀ L ∈ F, L.Infinite ∧
      DFAAtMost (k*ℓ*n) L ∧ ∃ r : RE, r.matches'=L ∧ Automata.writtenSize r ≤ k*ℓ^2*n^2) ∧
      ¬ MGeneratable (F : Set (Set (List Bool))) (2^(n^F.card)) := by
  refine ⟨1200,fun ℓ n hl hn ↦ ⟨family ℓ n,family_card ℓ n,?_,binary_obstruction ℓ n⟩⟩
  intro L hL
  obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hL
  obtain ⟨q,hq,M,hM⟩ := binary_dfa hl hn d
  obtain ⟨r,hr,hs⟩ := binary_regex hl hn d
  have hw := (Automata.size_comparison r).2.trans (Nat.mul_le_mul_left 3 hs)
  refine ⟨family_infinite hl n d,⟨q,hq.trans (by gcongr; decide),M,hM⟩,r,hr,?_⟩
  exact hw.trans_eq (by ring)

end
end GenLimit.ComplexityBarriers.Blocks
