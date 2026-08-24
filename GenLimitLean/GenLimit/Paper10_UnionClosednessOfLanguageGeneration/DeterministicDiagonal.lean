import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Definitions

/-!
# The deterministic diagonal of Proposition A.1

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, Proposition A.1.

For any deterministic generator, the construction recursively chooses the
next presented natural number above both the preceding input and the
generator's current output.  The resulting stream is strictly increasing,
presents an infinite target, and makes every positive-time output either
invalid or already observed.
-/

namespace GenLimit.UnionClosedness

/-- The exact increasing diagonal stream from Proposition A.1, shifted to
the repository convention where output at time `t` sees the `t` values with
indices strictly below `t`. -/
def deterministicDiagonalStream
    (G : GenLimit.Generic.Generator ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      max
        (G (t + 1) (fun i => deterministicDiagonalStream G i))
        (deterministicDiagonalStream G t) + 1
termination_by t => t

theorem deterministicDiagonalStream_lt_succ
    (G : GenLimit.Generic.Generator ℕ) (t : ℕ) :
    deterministicDiagonalStream G t <
      deterministicDiagonalStream G (t + 1) := by
  simp only [deterministicDiagonalStream]
  omega

theorem deterministicDiagonalStream_strictMono
    (G : GenLimit.Generic.Generator ℕ) :
    StrictMono (deterministicDiagonalStream G) :=
  strictMono_nat_of_lt_succ (deterministicDiagonalStream_lt_succ G)

theorem deterministicDiagonalStream_injective
    (G : GenLimit.Generic.Generator ℕ) :
    Function.Injective (deterministicDiagonalStream G) :=
  (deterministicDiagonalStream_strictMono G).injective

theorem deterministicDiagonal_output_lt
    (G : GenLimit.Generic.Generator ℕ) (t : ℕ) :
    GenLimit.Generic.output G (deterministicDiagonalStream G) (t + 1) <
      deterministicDiagonalStream G (t + 1) := by
  simp only [GenLimit.Generic.output, deterministicDiagonalStream]
  omega

/-- Every positive-time output is wrong on the diagonal target. -/
theorem deterministicDiagonal_not_correct
    (G : GenLimit.Generic.Generator ℕ) {t : ℕ} (ht : 0 < t) :
    ¬GenLimit.Generic.CorrectAt G
      (Set.range (deterministicDiagonalStream G))
      (deterministicDiagonalStream G) t := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  intro hcorrect
  rcases hcorrect.1 with ⟨k, hk⟩
  have houtlt := deterministicDiagonal_output_lt G s
  by_cases hks : k < s + 1
  · apply hcorrect.2
    rw [GenLimit.Generic.mem_sample_iff]
    exact ⟨k, hks, hk⟩
  · have hle :
        deterministicDiagonalStream G (s + 1) ≤
          deterministicDiagonalStream G k :=
      (deterministicDiagonalStream_strictMono G).monotone
        (Nat.le_of_not_gt hks)
    rw [hk] at hle
    exact (Nat.not_lt_of_ge hle) houtlt

/-- The diagonal target is infinite. -/
theorem deterministicDiagonalTarget_infinite
    (G : GenLimit.Generic.Generator ℕ) :
    (Set.range (deterministicDiagonalStream G)).Infinite :=
  Set.infinite_range_of_injective
    (deterministicDiagonalStream_injective G)

/-- The class of all infinite languages over `ℕ` in Proposition A.1. -/
def allInfiniteNatLanguages : GenLimit.Generic.LanguageClass ℕ :=
  {K | K.Infinite}

/-- Proposition A.1 in the source's duplicate-free exact-presentation
convention: no deterministic generator succeeds on every infinite target. -/
theorem proposition_A_1 :
    ¬GeneratableInLimitOnInjectivePresentations
      allInfiniteNatLanguages := by
  rintro ⟨G, hG⟩
  let stream := deterministicDiagonalStream G
  let target : Set ℕ := Set.range stream
  have htarget : target ∈ allInfiniteNatLanguages := by
    exact deterministicDiagonalTarget_infinite G
  have hinjective : Function.Injective stream := by
    exact deterministicDiagonalStream_injective G
  have hpresents : GenLimit.Generic.Presents stream target := rfl
  obtain ⟨T, hT⟩ :=
    hG target htarget stream hinjective hpresents
  let t := max T 1
  have htT : T ≤ t := Nat.le_max_left _ _
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one
    (Nat.le_max_right _ _)
  exact deterministicDiagonal_not_correct G htpos (hT t htT)

/-- Compatibility name for the source-facing injective statement. -/
theorem proposition_A_1_source_form :
    ¬GeneratableInLimitOnInjectivePresentations
      allInfiniteNatLanguages :=
  proposition_A_1

end GenLimit.UnionClosedness
