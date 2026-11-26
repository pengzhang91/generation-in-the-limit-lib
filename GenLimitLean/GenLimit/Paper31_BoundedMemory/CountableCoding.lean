import GenLimit.Paper31_BoundedMemory.IncrementalElementCoding
import Mathlib.Logic.Denumerable

/-! # Transport of the incremental coding construction along a word enumeration -/

namespace GenLimit.BoundedMemory

open Set

private theorem transportElementGenerator {N : ℕ} (e : α ≃ ℕ) (langs : Fin (N+1) → Set α)
    (hg : IncrementallyElementGenerable (fun i => e '' langs i)) :
    IncrementallyElementGenerable langs := by
  obtain ⟨G,initial,hG⟩ := hg
  let rule : IncrementalLearner α α := fun y x => e.symm (G (e y) (e x))
  refine ⟨rule, e.symm initial, ?_⟩
  intro i s hs
  have hp : Generic.Presents (e ∘ s) (e '' langs i) :=
    (Set.range_comp e s).trans (congrArg _ hs)
  obtain ⟨T,hT⟩ := hG i _ hp
  have run (t) : e (incrementalRun rule (e.symm initial) s t) =
      incrementalRun G initial (e ∘ s) t := by
    induction t with
    | zero => simp
    | succ t ih => simp [incrementalRun, rule, ih]
  refine ⟨T,fun t ht => ?_⟩
  obtain ⟨hmem,hfresh⟩ := hT t ht
  constructor
  · exact e.injective.mem_set_image.mp (run t ▸ hmem)
  · rintro ⟨j,hj⟩
    exact hfresh ⟨j, (congrArg e hj).trans (run t)⟩

/-- Appendix A.4. The compiler accepts a full-history learner over the
original example alphabet and returns a generator over that same alphabet. -/
theorem countable_coding_compilation [Countable α] [Infinite α] {N : ℕ}
    (langs : Fin (N+1) → Set α) (hi : ∀ i, (langs i).Infinite)
    (M : List α → Fin (N+1)) (hM : EventuallyAlmostContainedHypotheses langs M) :
    IncrementallyElementGenerable langs := by
  classical
  let e : α ≃ ℕ := Nonempty.some inferInstance
  apply transportElementGenerator e langs
  apply incremental_coding_compilation _ (fun i => (hi i).image e.injective.injOn)
    (fun l => M (l.map e.symm))
  intro i s hs
  have hp : Generic.Presents (e.symm ∘ s) (langs i) := by
    change Set.range (e.symm ∘ s) = _
    rw [Set.range_comp, hs]
    simp
  obtain ⟨T,hT⟩ := hM i _ hp
  refine ⟨T,fun t ht => ?_⟩
  have hlist : (elementHistoryPrefix s t).map e.symm = elementHistoryPrefix (e.symm ∘ s) t := by
    simp [elementHistoryPrefix, Function.comp_def]
  change (e '' langs (M ((elementHistoryPrefix s t).map e.symm)) \
    e '' langs i).Finite
  rw [hlist, ← Set.image_diff e.injective]
  exact (hT t ht).image _

/-- Appendix A.5. The previous output encodes the persistent state, on any
countably infinite alphabet. -/
theorem countable_incremental_element_generation [Countable α] [Infinite α] {N : ℕ}
    (langs : Fin (N+1) → Set α) (hi : ∀ i, (langs i).Infinite) :
    IncrementallyElementGenerable langs := by
  let e : α ≃ ℕ := Nonempty.some inferInstance
  exact transportElementGenerator e langs
    (incremental_element_generation _ (fun i => (hi i).image e.injective.injOn))

end GenLimit.BoundedMemory
