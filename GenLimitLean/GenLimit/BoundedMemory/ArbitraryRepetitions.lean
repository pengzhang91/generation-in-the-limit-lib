import GenLimit.BoundedMemory.Definitions

/-!
# Theorem 3.1: arbitrary-repetition characterization

Source: Kleinberg--Mehrotra--Saberi--Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Theorem 3.1 ("Characterization with arbitrary
repetitions").

The source states the result for a countable collection of infinite
languages.  The proof below establishes the exact semantic equivalence and
shows that countability of the collection is not needed for this theorem.
Countability of the example universe is used only to build the adversarial
presentation that repeats one prescribed point forever while still
enumerating the whole target.
-/

namespace GenLimit.BoundedMemory

section RepeatedPresentation

variable [Countable α]

/-- A chosen positive presentation of a nonempty countable set. -/
noncomputable def basePresentation (K : Set α) (hK : K.Nonempty) : ℕ → α := by
  classical
  have hcount : K.Countable := Set.countable_univ.mono (Set.subset_univ K)
  let f : ℕ → K := Classical.choose (hcount.exists_surjective hK)
  exact fun n => f n

theorem basePresentation_presents (K : Set α) (hK : K.Nonempty) :
    GenLimit.Generic.Presents (basePresentation K hK) K := by
  classical
  have hcount : K.Countable := Set.countable_univ.mono (Set.subset_univ K)
  let hf := Classical.choose_spec (hcount.exists_surjective hK)
  apply Set.Subset.antisymm
  · rintro y ⟨n, rfl⟩
    exact (Classical.choose (hcount.exists_surjective hK) n).property
  · intro y hy
    obtain ⟨n, hn⟩ := hf ⟨y, hy⟩
    refine ⟨n, ?_⟩
    exact congrArg Subtype.val hn

/-- Interleave a fixed point at every even time with a complete
presentation at every odd time. -/
noncomputable def repeatedPointPresentation
    (K : Set α) (hK : K.Nonempty) (x : α) : ℕ → α :=
  fun t => if t % 2 = 0 then x else basePresentation K hK (t / 2)

theorem repeatedPointPresentation_even
    (K : Set α) (hK : K.Nonempty) (x : α) (n : ℕ) :
    repeatedPointPresentation K hK x (2 * n) = x := by
  simp [repeatedPointPresentation]

theorem repeatedPointPresentation_odd
    (K : Set α) (hK : K.Nonempty) (x : α) (n : ℕ) :
    repeatedPointPresentation K hK x (2 * n + 1) =
      basePresentation K hK n := by
  simp only [repeatedPointPresentation]
  have hmod : (2 * n + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  congr 1
  omega

/-- The repeated-point stream is still an exact presentation. -/
theorem repeatedPointPresentation_presents
    (K : Set α) (hK : K.Nonempty) {x : α} (hx : x ∈ K) :
    GenLimit.Generic.Presents (repeatedPointPresentation K hK x) K := by
  apply Set.Subset.antisymm
  · rintro y ⟨t, rfl⟩
    by_cases ht : t % 2 = 0
    · simp [repeatedPointPresentation, ht, hx]
    · have hbase :
          basePresentation K hK (t / 2) ∈
            Set.range (basePresentation K hK) :=
        ⟨t / 2, rfl⟩
      have := hbase
      rw [basePresentation_presents K hK] at this
      simpa [repeatedPointPresentation, ht] using this
  · intro y hy
    rw [← basePresentation_presents K hK] at hy
    obtain ⟨n, rfl⟩ := hy
    refine ⟨2 * n + 1, ?_⟩
    exact repeatedPointPresentation_odd K hK x n

end RepeatedPresentation

section Characterization

variable [Countable α]

/-- An arbitrary-repetition memoryless generator must already be valid
after each individual possible observation.

This is the adversarial amplification step in the necessity half of
Theorem 3.1. -/
theorem arbitrary_success_implies_pointwise
    {G : MemorylessSetGenerator α} {H : Set (Set α)}
    (hG : IsArbitraryPresentationMemorylessGenerator G H)
    {K : Set α} (hK : K ∈ H) {x : α} (hx : x ∈ K) :
    ValidSetOutput G K x := by
  have hKnonempty : K.Nonempty := ⟨x, hx⟩
  let stream := repeatedPointPresentation K hKnonempty x
  obtain ⟨T, hT⟩ :=
    hG K hK stream
      (repeatedPointPresentation_presents K hKnonempty hx)
  have hround := hT (2 * T) (by omega)
  simpa [stream, repeatedPointPresentation_even] using hround

/-- Necessity in Theorem 3.1. -/
theorem arbitrary_memoryless_necessity
    {H : Set (Set α)}
    (h : ArbitraryPresentationMemorylessGeneratable H) :
    InfiniteSingletonCores H := by
  obtain ⟨G, hG⟩ := h
  intro x hxUnion
  rcases Set.mem_sUnion.mp hxUnion with ⟨K, hKH, hxK⟩
  have hvalidK := arbitrary_success_implies_pointwise hG hKH hxK
  apply hvalidK.1.mono
  intro y hy L hLH hxL
  exact (arbitrary_success_implies_pointwise hG hLH hxL).2 hy

omit [Countable α] in
/-- Sufficiency in Theorem 3.1.  The common intersection itself is a valid
memoryless set output on every round, not merely eventually. -/
theorem arbitrary_memoryless_sufficiency
    {H : Set (Set α)} (hcore : InfiniteSingletonCores H) :
    ArbitraryPresentationMemorylessGeneratable H := by
  refine ⟨singletonCore H, ?_⟩
  intro K hKH stream hP
  refine ⟨0, ?_⟩
  intro t _ht
  have hxt : stream t ∈ K := by
    rw [← hP]
    exact ⟨t, rfl⟩
  have hxUnion : stream t ∈ ⋃₀ H :=
    Set.mem_sUnion.mpr ⟨K, hKH, hxt⟩
  exact ⟨hcore (stream t) hxUnion,
    singletonCore_subset hKH hxt⟩

/-- Detailed Theorem 3.1 (and the characterization clause summarized in
Theorem 1.1): arbitrary-repetition memoryless set generation is equivalent
to infinitude of every singleton common core.

The source additionally assumes `H.Countable` and that each `K ∈ H` is
infinite.  They are included verbatim even though the semantic equivalence
itself only uses countability of the universe. -/
theorem theorem_3_1
    (H : Set (Set α))
    (_hCountable : H.Countable)
    (_hInfinite : ∀ K, K ∈ H → K.Infinite) :
    ArbitraryPresentationMemorylessGeneratable H ↔
      InfiniteSingletonCores H :=
  ⟨arbitrary_memoryless_necessity,
    arbitrary_memoryless_sufficiency⟩

end Characterization

end GenLimit.BoundedMemory
