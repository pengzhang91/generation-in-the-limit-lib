import GenLimit.Paper31_BoundedMemory.RankedUniverse
import GenLimit.Paper31_BoundedMemory.SourceGeneration
import GenLimit.Paper31_BoundedMemory.Results.Supporting
import GenLimit.Paper31_BoundedMemory.ExactIdentificationObstruction
import GenLimit.Paper31_BoundedMemory.IncrementalIndexObstruction

/-! # Bounded memory: main results
The density statements use word ranks in the fixed enumeration of the
universe. Every target inherits its order from that same enumeration.
-/

namespace GenLimit.BoundedMemory.Results

open Set Function GenLimit.KleinbergWei

theorem theorem_1_1 [Countable α] [Infinite α]
    (H : Set (Set α)) (hc : H.Countable) (hi : ∀ K ∈ H, K.Infinite) :
    ∃ G : α → InfiniteOutput α, ∀ K ∈ H, ∀ s : ℕ → α,
      Generic.Presents s K → FinitelyRepeating s →
        ∃ T, ∀ t ≥ T, (G (s t)).val ⊆ K :=
  countable_memoryless_generation H hc hi

theorem theorem_3_1 [Countable α] [Infinite α]
    (H : Set (Set α)) :
    (ArbitraryMemoryless H ↔ FullMemoryAfterOne H) ∧
    (FullMemoryAfterOne H ↔ InfiniteSingletonCores H) :=
  arbitrary_generation_characterization H

theorem theorem_3_2 {α : Type*} [Countable α] :
    (∀ i, (indexLanguages i).Infinite) ∧
    (∀ (K : Set α), K.Infinite →
      ∀ G : MemorylessElementGenerator α,
        ¬IsFinitelyRepeatingElementGeneratorOn G K) ∧
    (∀ G : MemorylessIndexGenerator ℕ (Fin 2),
      ¬IsFinitelyRepeatingIndexGenerator G indexLanguages) :=
  ⟨GenLimit.BoundedMemory.theorem_3_2.1, theorem_3_2_element,
    GenLimit.BoundedMemory.theorem_3_2.2.2⟩

theorem theorem_4_1 (e : α ≃ ℕ) (k : ℕ) (hk : 1 ≤ k) :
    sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ RankedUniverse.Memoryless e k σ} =
      1 / (Nat.choose (k - 1) ((k - 1) / 2) : ℝ) :=
  by simpa only [RankedUniverse.memoryless_iff] using fixedOrder_memoryless k hk

theorem theorem_4_2 (e : α ≃ ℕ) (k : ℕ) (hk : 3 ≤ k) :
    ∃ (L : RankedUniverse.Family α k) (i : Fin k), ∀ G : MemorylessSetGenerator α,
      IsFinitelyRepeatingMemorylessGenerator G (range L.lang) →
      ∀ s, Generic.Presents s (L.lang i) → FinitelyRepeating s →
        ∃ T, ∀ t ≥ T, (OrderedLanguage.canonical ((L.map e).lang i) ((L.map e).infinite i)).lowerDensity
          (e '' G (s t)) = 0 :=
  RankedUniverse.zero_lower_density e k hk

theorem theorem_4_10 (e : α ≃ ℕ) (k W : ℕ) (hk : 1 ≤ k) (hW : 0 < W) :
    sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ RankedUniverse.Windows e k W σ} =
      1 / (Nat.choose (k - 1) ((k - 1) / 2) : ℝ) :=
  by simpa only [RankedUniverse.windows_iff] using fixedOrder_window k W hk hW

theorem theorem_4_15 (e : α ≃ ℕ) (k b : ℕ) (hk : 1 ≤ k) : adaptiveBufferLowerValue k b ≤
    sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ RankedUniverse.Buffers e k b σ} :=
  by simpa only [RankedUniverse.buffers_iff] using fixedOrder_buffer k b hk

theorem proposition_5_1 :
    (∀ i, (exactObstructionLanguages i).Infinite) ∧
    Function.Injective exactObstructionLanguages ∧
    ¬IncrementallyExactlyIdentifiableOnFinitelyRepeating
      exactObstructionLanguages :=
  GenLimit.BoundedMemory.proposition_5_1

theorem theorem_5_2 {α : Type*} {N : ℕ} (raw : Fin (N+1) → Set α) :
    IncrementallyApproximatelyIdentifiable raw :=
  incremental_original_indices raw

theorem theorem_A_1 :
    ∃ langs : Fin 3 → Set ℕ,
      Function.Injective langs ∧
        (∀ i, (langs i).Infinite) ∧
          ¬IncrementallyExactlyIdentifiableOnFinitelyRepeating langs :=
  GenLimit.BoundedMemory.theorem_A_1

theorem proposition_A_2
    [Countable α]
    {T : Set α} (hT : T.Infinite) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haT : a ∉ T) (hbT : b ∉ T) (hcT : c ∉ T) :
    ¬IncrementallyIndexGenerableOnFinitelyRepeating
      (appendixTriangleLanguages T a b c) :=
  GenLimit.BoundedMemory.proposition_A_2 hT hab hac hbc haT hbT hcT

theorem theorem_A_4 [Countable α] [Infinite α] {N : ℕ}
    (langs : Fin (N+1) → Set α) (hi : ∀ i, (langs i).Infinite)
    (M : List α → Fin (N+1)) (hM : EventuallyAlmostContainedHypotheses langs M) :
    IncrementallyElementGenerable langs :=
  countable_coding_compilation langs hi M hM

theorem theorem_A_5 [Countable α] [Infinite α] {N : ℕ}
    (langs : Fin (N+1) → Set α) (hi : ∀ i, (langs i).Infinite) :
    IncrementallyElementGenerable langs :=
  countable_incremental_element_generation langs hi

end GenLimit.BoundedMemory.Results
