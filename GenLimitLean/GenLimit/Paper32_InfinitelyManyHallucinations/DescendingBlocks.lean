import GenLimit.Paper32_InfinitelyManyHallucinations.BatchedRace

/-! # A full input which presents successive intervals in reverse order
The end of block n is large compared to the entire pool accumulated before
the block. Its last word completes an initial segment of the natural target.
-/
namespace GenLimit.InfinitelyManyHallucinations.Pods.Counterexample
open Set
open scoped Classical

def border : ℕ → ℕ
  | 0 => 0
  | n+1 => (n+1)*(border n+8)^2

theorem border_step (n : ℕ) : border n + 7 < border (n+1) := by
  rw [border]
  have h := Nat.le_mul_of_pos_left ((border n+8)^2) (by omega : 0 < n+1)
  nlinarith [sq_nonneg (border n : ℤ)]

theorem border_strict : StrictMono border :=
  strictMono_nat_of_lt_succ (fun n => by have := border_step n; omega)

private def blockIndex (t : ℕ) := Nat.find (show ∃ n, t < border (n+1) from
  ⟨t,(Nat.lt_succ_self t).trans_le (border_strict.id_le _)⟩)

private theorem blockIndex_bounds (t : ℕ) :
    border (blockIndex t) ≤ t ∧ t < border (blockIndex t+1) := by
  refine ⟨?_,Nat.find_spec (p := fun n => t < border (n+1)) _⟩
  cases e : blockIndex t with
  | zero => simp [border]
  | succ n =>
    by_contra! h
    have lt : n < blockIndex t := by omega
    exact Nat.find_min (p := fun i => t < border (i+1)) _ lt h

private theorem blockIndex_of {n t : ℕ} (lo : border n ≤ t) (hi : t < border (n+1)) :
    blockIndex t = n := by
  obtain ⟨a,b⟩ := blockIndex_bounds t
  rcases lt_trichotomy (blockIndex t) n with h|h|h
  · exact (Nat.not_lt_of_ge lo (b.trans_le (border_strict.monotone (Nat.succ_le_of_lt h)))).elim
  · exact h
  · exact (Nat.not_lt_of_ge ((border_strict.monotone (Nat.succ_le_of_lt h)).trans a) hi).elim

def word (t : ℕ) := border (blockIndex t)+border (blockIndex t+1)-1-t

theorem word_at {n t : ℕ} (lo : border n ≤ t) (hi : t < border (n+1)) :
    word t = border n + border (n+1) - 1 - t := by
  simp [word,blockIndex_of lo hi]

private theorem word_bounds (t : ℕ) :
    border (blockIndex t) ≤ word t ∧ word t < border (blockIndex t+1) := by
  obtain ⟨h1,h2⟩ := blockIndex_bounds t
  unfold word
  omega

theorem involution (t : ℕ) : word (word t) = t := by
  obtain ⟨hl,hh⟩ := word_bounds t
  rw [word_at hl hh]
  unfold word
  obtain ⟨_,hu⟩ := blockIndex_bounds t
  omega

private theorem word_before {t n : ℕ} : word t < border n ↔ t < border n := by
  have direct (x : ℕ) (hx : x < border n) : word x < border n := by
    obtain ⟨hlo,_⟩ := blockIndex_bounds x
    have ind := border_strict.lt_iff_lt.mp (hlo.trans_lt hx)
    exact (word_bounds x).2.trans_le (border_strict.monotone (Nat.succ_le_of_lt ind))
  exact ⟨fun h => involution t ▸ direct (word t) h,direct t⟩

def input := BatchedRace.blocks 1 word

theorem input_single : input.IsSingleStep := BatchedRace.block_bound 1 word

theorem input_full : input.limit = univ := by
  rw [input,BatchedRace.block_limit (by decide : 0 < 1),Set.range_eq_univ]
  exact fun x => ⟨word x,involution x⟩

private theorem in_stage {t x : ℕ} : x ∈ input.stage t ↔ word x < t := by
  rw [input,BatchedRace.block_mem,Nat.mul_one]
  constructor
  · rintro ⟨i,hi,rfl⟩
    rwa [involution]
  · exact fun h => ⟨word x,h,involution x⟩

theorem block_stage {n t : ℕ} (lo : border n ≤ t) (hi : t < border (n+1)) (x : ℕ) :
    x ∈ input.stage (t+1) ↔ x < border n ∨ word t ≤ x ∧ x < border (n+1) := by
  rw [in_stage]
  by_cases hl : x < border n
  · have hx := word_before.mpr hl
    omega
  by_cases hh : x < border (n+1)
  · rw [word_at (by omega : border n ≤ x) hh, word_at lo hi]
    omega
  · have hw := mt (@word_before x (n+1)).mp hh
    omega

theorem block_complete (n : ℕ) {x : ℕ} (hx : x < border n) : x ∈ input.stage (border n) :=
  in_stage.mpr (word_before.mpr hx)

end GenLimit.InfinitelyManyHallucinations.Pods.Counterexample
