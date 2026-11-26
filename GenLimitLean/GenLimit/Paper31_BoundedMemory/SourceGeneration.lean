import GenLimit.Paper31_BoundedMemory.FinitelyRepeating
import GenLimit.Paper31_BoundedMemory.IncrementalIdentification
import Mathlib.Logic.Denumerable

/-! # Source formulations for memoryless generation and incremental identification -/

namespace GenLimit.BoundedMemory

open Set Function

/-- The source codomain `[X]^∞` at every observation, including observations
outside every language in the collection. -/
abbrev InfiniteOutput (α : Type*) := {S : Set α // S.Infinite}

private noncomputable def completeOutput [Infinite α] (S : Set α) : InfiniteOutput α := by
  classical
  exact if h : S.Infinite then ⟨S,h⟩ else ⟨Set.univ, Set.infinite_univ⟩

private theorem completeOutput_valid [Infinite α] {S K : Set α}
    (h : S.Infinite ∧ S ⊆ K) : (completeOutput S).val ⊆ K := by
  simpa [completeOutput, h.1] using h.2

/-- Theorem 1.1 over any countably infinite universe. All outputs of the
same family-wide generator are infinite, even on early, unsuccessful rounds. -/
theorem countable_memoryless_generation [Countable α] [Infinite α]
    (H : Set (Set α)) (hc : H.Countable) (hi : ∀ K ∈ H, K.Infinite) :
    ∃ G : α → InfiniteOutput α, ∀ K ∈ H, ∀ s : ℕ → α,
      Generic.Presents s K → FinitelyRepeating s →
        ∃ T, ∀ t ≥ T, (G (s t)).val ⊆ K := by
  classical
  let e : α ≃ ℕ := Nonempty.some inferInstance
  let F := (fun K : Set α => e '' K) '' H
  obtain ⟨G,hG⟩ := theorem_1_1 F (hc.image _) (by
    rintro L ⟨K,hK,rfl⟩
    exact (hi K hK).image e.injective.injOn)
  refine ⟨fun x => completeOutput (e ⁻¹' G (e x)), ?_⟩
  intro K hK s hs hr
  have hp : Generic.Presents (e ∘ s) (e '' K) :=
    (Set.range_comp e s).trans (congrArg _ hs)
  have hrep : FinitelyRepeating (e ∘ s) := by
    intro y
    simpa [Function.comp_def, Equiv.apply_eq_iff_eq_symm_apply] using hr (e.symm y)
  obtain ⟨T,hT⟩ := hG (e '' K) ⟨K,hK,rfl⟩ (e ∘ s) hp hrep
  refine ⟨T,fun t ht => completeOutput_valid ?_⟩
  obtain ⟨hinf,hsub⟩ := hT t ht
  exact ⟨hinf.preimage (fun y _ => e.surjective y),
    fun _ hy => e.injective.mem_set_image.mp (hsub hy)⟩

/-- The unrestricted generator sees the whole nonempty sample; its output
is required to be valid starting with the first observed example. -/
def FullMemoryAfterOne (H : Set (Set α)) : Prop :=
  ∃ G : List α → InfiniteOutput α, ∀ K ∈ H, ∀ (x : α) (xs : List α),
    x ∈ K → (∀ y ∈ xs, y ∈ K) → (G (x :: xs)).val ⊆ K

/-- Memoryless generation from arbitrary presentations with the original
infinite-set codomain. -/
def ArbitraryMemoryless (H : Set (Set α)) : Prop :=
  ∃ G : α → InfiniteOutput α, IsArbitraryPresentationMemorylessGenerator (fun x => (G x).val) H

/-- All three equivalent conditions in Theorem 3.1. -/
theorem arbitrary_generation_characterization [Countable α] [Infinite α]
    (H : Set (Set α)) :
    (ArbitraryMemoryless H ↔ FullMemoryAfterOne H) ∧
    (FullMemoryAfterOne H ↔ InfiniteSingletonCores H) := by
  have fromCore (hc : InfiniteSingletonCores H) : ArbitraryMemoryless H := by
    obtain ⟨G,hG⟩ := arbitrary_memoryless_sufficiency hc
    refine ⟨fun x => completeOutput (G x), ?_⟩
    intro K hK s hs
    obtain ⟨T,hT⟩ := hG K hK s hs
    exact ⟨T, fun t ht => ⟨(completeOutput _).property, completeOutput_valid (hT t ht)⟩⟩
  have fromMemoryless (hm : ArbitraryMemoryless H) : FullMemoryAfterOne H := by
    obtain ⟨G,hG⟩ := hm
    refine ⟨fun l => match l with
      | [] => ⟨Set.univ, Set.infinite_univ⟩
      | x :: _ => G x, ?_⟩
    intro K hK x xs hx _
    exact (arbitrary_success_implies_pointwise hG hK hx).2
  have fromFull (hf : FullMemoryAfterOne H) : InfiniteSingletonCores H := by
    obtain ⟨G,hG⟩ := hf
    intro x _
    apply (G [x]).property.mono
    intro y hy K hK hx
    exact hG K hK x [] hx (by simp) hy
  exact ⟨⟨fromMemoryless, fromCore ∘ fromFull⟩, ⟨fromFull, fromMemoryless ∘ fromCore⟩⟩

/-- Theorem 5.2 on the given indices. Conjugating the transition rule back
through the sorting permutation preserves every state at every time. -/
theorem incremental_original_indices {α : Type*} {N : ℕ} (raw : Fin (N+1) → Set α) :
    IncrementallyApproximatelyIdentifiable raw := by
  classical
  let e := Equiv.ofBijective (relabeledIndex raw) (relabeledIndex_bijective raw)
  obtain ⟨learn,start,h⟩ := theorem_5_2_ordered (topologicallyRelabeled raw)
    (fun hij => strictAlmostContained_implies_lt_relabel raw hij)
  let learn' : IncrementalLearner α (Fin (N+1)) := fun i x => e (learn (e.symm i) x)
  refine ⟨learn', e start, ?_⟩
  intro target s hs
  have hrun (t : ℕ) : incrementalRun learn' (e start) s t =
      e (incrementalRun learn start s t) := by
    induction t with
    | zero => rfl
    | succ t ih => simp [incrementalRun, ih, learn']
  have htarget : topologicallyRelabeled raw (e.symm target) = raw target :=
    congrArg raw (e.apply_symm_apply target)
  obtain ⟨T,hT⟩ := h (e.symm target) s (htarget.symm ▸ hs)
  refine ⟨T,fun t ht => ?_⟩
  rw [hrun]
  simpa only [htarget] using hT t ht

end GenLimit.BoundedMemory
