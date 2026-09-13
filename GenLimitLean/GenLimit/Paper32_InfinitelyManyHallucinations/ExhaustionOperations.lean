import GenLimit.Paper32_InfinitelyManyHallucinations.Definitions

/-!
# Reusable operations on Paper 32 exhaustions

Paper-local constructors for ambient-order exhaustions, stagewise language
restriction, and cardinality-clocked exhaustions.  These operations support
both the Section 2 supremum characterizations and later constructive work.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

/-- Ambient-order finite prefixes of an arbitrary language. -/
noncomputable def ambientExhaustion (L : Language) : Exhaustion := by
  classical
  exact
    { stage := fun n => (Finset.range n).filter fun x => x ∈ L
      stage_zero := by simp
      monotone_stage := by
        intro m n hmn x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
        exact ⟨hx.1.trans_le hmn, hx.2⟩ }

theorem ambientExhaustion_exhausts (L : Language) :
    (ambientExhaustion L).Exhausts L := by
  classical
  apply Set.ext
  intro x
  constructor
  · rintro ⟨n, hx⟩
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact ⟨x + 1, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_self x), hx⟩⟩

/-- The elements of a finite stage belonging to a fixed language. -/
noncomputable def finiteRestriction
    (S : Finset ℕ) (L : Language) : Finset ℕ := by
  classical
  exact S.filter fun x => x ∈ L

theorem finiteRestriction_subset (S : Finset ℕ) (L : Language) :
    finiteRestriction S L ⊆ S := by
  classical
  exact Finset.filter_subset _ _

/-- Restrict every stage of an exhaustion to a fixed language. -/
noncomputable def restrictedExhaustion
    (E : Exhaustion) (L : Language) : Exhaustion := by
  classical
  exact
    { stage := fun n => finiteRestriction (E.stage n) L
      stage_zero := by simp [E.stage_zero, finiteRestriction]
      monotone_stage := by
        intro m n hmn x hx
        simp only [finiteRestriction, Finset.mem_filter] at hx ⊢
        exact ⟨E.monotone_stage hmn hx.1, hx.2⟩ }

theorem restrictedExhaustion_increment_succ
    (E : Exhaustion) (L : Language) (n : ℕ) :
    (restrictedExhaustion E L).increment (n + 1) =
      finiteRestriction (E.increment (n + 1)) L := by
  classical
  ext x
  simp only [restrictedExhaustion, finiteRestriction,
    Exhaustion.increment, Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem restrictedExhaustion_limit
    (E : Exhaustion) (L : Language) :
    (restrictedExhaustion E L).limit = E.limit ∩ L := by
  classical
  ext x
  constructor
  · rintro ⟨n, hx⟩
    exact ⟨⟨n, (Finset.mem_filter.mp hx).1⟩,
      (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨⟨n, hxStage⟩, hxL⟩
    exact ⟨n, Finset.mem_filter.mpr ⟨hxStage, hxL⟩⟩

theorem restrictedExhaustion_boundedBy
    {E : Exhaustion} {L : Language} {f : ℕ → ℕ}
    (hbounded : E.BoundedBy f) :
    (restrictedExhaustion E L).BoundedBy f := by
  intro n
  rw [restrictedExhaustion_increment_succ]
  exact (Finset.card_le_card
    (finiteRestriction_subset (E.increment (n + 1)) L)).trans
      (hbounded n)

theorem ambientExhaustion_stage_diff_card_le
    (L : Language) (a b : ℕ) :
    ((ambientExhaustion L).stage b \
      (ambientExhaustion L).stage a).card ≤ b - a := by
  classical
  have hsubset :
      (ambientExhaustion L).stage b \
          (ambientExhaustion L).stage a ⊆
        Finset.Ico a b := by
    intro x hx
    have hxb := (Finset.mem_sdiff.mp hx).1
    have hnot := (Finset.mem_sdiff.mp hx).2
    have hxb' : x < b ∧ x ∈ L := by
      simpa [ambientExhaustion] using hxb
    have hax : a ≤ x := by
      by_contra hxa
      apply hnot
      simp [ambientExhaustion, Nat.lt_of_not_ge hxa, hxb'.2]
    exact Finset.mem_Ico.mpr ⟨hax, hxb'.1⟩
  calc
    ((ambientExhaustion L).stage b \
        (ambientExhaustion L).stage a).card ≤
        (Finset.Ico a b).card := Finset.card_le_card hsubset
    _ = b - a := by simp

/-- Exhaust `L` using the cardinality growth of `clock`.  The construction
adds no more elements at a step than `clock` does. -/
noncomputable def cardinalityClockedExhaustion
    (L : Language) (clock : Exhaustion) : Exhaustion := by
  classical
  exact
    { stage := fun n => (ambientExhaustion L).stage (clock.stage n).card
      stage_zero := by simp [clock.stage_zero, ambientExhaustion]
      monotone_stage := by
        intro m n hmn
        exact (ambientExhaustion L).monotone_stage
          (Finset.card_le_card (clock.monotone_stage hmn)) }

theorem cardinalityClockedExhaustion_exhausts
    (L : Language) (clock : Exhaustion)
    (hinfinite : clock.limit.Infinite) :
    (cardinalityClockedExhaustion L clock).Exhausts L := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨n, hx⟩
    exact (Finset.mem_filter.mp hx).2
  · intro x hxL
    have heventually :=
      (clock.card_tendsto_atTop_of_limit_infinite hinfinite).eventually
        (eventually_ge_atTop (x + 1))
    obtain ⟨n, hn⟩ := heventually.exists
    exact ⟨n, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_of_lt_of_le
        (Nat.lt_succ_self x) hn), hxL⟩⟩

theorem cardinalityClockedExhaustion_boundedBy
    (L : Language) {clock : Exhaustion} {f : ℕ → ℕ}
    (hbounded : clock.BoundedBy f) :
    (cardinalityClockedExhaustion L clock).BoundedBy f := by
  intro n
  let a := (clock.stage n).card
  let b := (clock.stage (n + 1)).card
  have hclockIncrement :
      (clock.increment (n + 1)).card = b - a := by
    rw [Exhaustion.increment,
      Finset.card_sdiff_of_subset
        (clock.monotone_stage (Nat.le_succ n))]
  change ((ambientExhaustion L).stage b \
    (ambientExhaustion L).stage a).card ≤ f (n + 1)
  exact (ambientExhaustion_stage_diff_card_le L a b).trans
    (by rw [← hclockIncrement]; exact hbounded n)

end GenLimit.InfinitelyManyHallucinations
