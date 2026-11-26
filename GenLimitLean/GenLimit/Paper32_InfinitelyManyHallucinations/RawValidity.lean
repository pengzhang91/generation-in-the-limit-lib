import GenLimit.Paper32_InfinitelyManyHallucinations.BatchedRace
import GenLimit.Paper32_InfinitelyManyHallucinations.TailPrecision

/-! # The raw-batch reading of Definition 3.2 and Proposition 3.3
A repeated word is present in the raw batch even when it makes no change
to the generated exhaustion. The distinction applies to infinite runs.
-/
namespace GenLimit.InfinitelyManyHallucinations

open Set
open scoped Classical

def RawEventuallyValid (G : BatchGenerator) (A : Exhaustion) (L : Language) : Prop :=
  ∃ T, ∀ t ≥ T, ∀ x ∈ G (t+1) (fun i => A.stage i) (generatedStages G A t), x ∈ L

/-- The increment formulation agrees with the literal raw-batch definition
when a generator never returns an already generated word. -/
theorem raw_validity_iff_of_fresh (G : BatchGenerator) (A : Exhaustion) (L : Language)
    (fresh : ∀ t, Disjoint (G (t+1) (fun i => A.stage i) (generatedStages G A t))
      (generatedStages G A t)) :
    RawEventuallyValid G A L ↔ TailPrecisionOneFromFiniteTime L (generatedExhaustion G A) := by
  rw [← proposition_3_3]
  have mem (t x : ℕ) : x ∈ (generatedExhaustion G A).increment (t+1) ↔
      x ∈ G (t+1) (fun i => A.stage i) (generatedStages G A t) := by
    change x ∈ (generatedStages G A t ∪ _) \ generatedStages G A t ↔ _
    simp only [Finset.mem_sdiff,Finset.mem_union]
    exact ⟨fun h => h.1.resolve_left h.2,fun h => ⟨Or.inr h, Finset.disjoint_left.mp (fresh t) h⟩⟩
  constructor
  · rintro ⟨T,hT⟩
    refine ⟨T+1,?_⟩
    rintro (_|t) ht x hx
    · omega
    · exact hT t (by omega) x ((mem t x).mp hx)
  · rintro ⟨T,hT⟩
    exact ⟨T,fun t ht x hx => hT (t+1) (by omega) ((mem t x).mpr hx)⟩

private def repeatZero : BatchGenerator := fun n h _ => insert 0 (h (Fin.last n))

private theorem zero_stage (A : Exhaustion) (n : ℕ) :
    (generatedExhaustion repeatZero A).stage (n+1) = insert 0 (A.stage (n+1)) := by
  induction n with
  | zero => simp [generatedExhaustion,generatedStages,repeatZero]
  | succ n ih =>
    change generatedStages repeatZero A (n+1) ∪ insert 0 (A.stage (n+2)) = _
    change generatedStages repeatZero A (n+1) = _ at ih
    rw [ih,Finset.union_eq_right.mpr (Finset.insert_subset_insert _ (A.monotone_stage (by omega)))]

/-- The target, the adversarial limit and the generated limit are all infinite.
Every raw batch includes zero, although from round two onward all new words
are positive. -/
theorem proposition_3_3_raw_counterexample :
    ∃ (G : BatchGenerator) (A : Exhaustion), A.limit.Infinite ∧
      (generatedExhaustion G A).limit.Infinite ∧ A.IsSingleStep ∧
      TailPrecisionOneFromFiniteTime A.limit (generatedExhaustion G A) ∧ ¬RawEventuallyValid G A A.limit := by
  let A := BatchedRace.blocks 1 Nat.succ
  have full : A.limit = Set.range Nat.succ := BatchedRace.block_limit (by decide) _
  have hi : A.limit.Infinite := full ▸ Set.infinite_range_of_injective Nat.succ_injective
  have sub : A.limit ⊆ (generatedExhaustion repeatZero A).limit := by
    rintro x ⟨n,h⟩
    refine ⟨n+1,?_⟩
    rw [zero_stage]
    exact Finset.mem_insert_of_mem (A.monotone_stage (Nat.le_succ n) h)
  refine ⟨repeatZero,A,hi,hi.mono sub,BatchedRace.block_bound 1 _,(proposition_3_3 _ _).mp ?_,?_⟩
  · refine ⟨2,?_⟩
    rintro (_|(_|t)) ht x hx
    · omega
    · omega
    · rw [Exhaustion.increment,zero_stage,zero_stage] at hx
      obtain ⟨h,no⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_insert.mp h with rfl|h
      · exact (no (Finset.mem_insert_self ..)).elim
      · exact A.stage_subset_limit _ h
  · rintro ⟨T,hT⟩
    have bad := hT T le_rfl 0 (Finset.mem_insert_self ..)
    rw [full] at bad
    exact Nat.succ_ne_zero _ bad.choose_spec

end GenLimit.InfinitelyManyHallucinations
