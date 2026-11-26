import GenLimit.Paper28_ContrastiveGeneration.CorruptedPresentations
import GenLimit.Paper28_ContrastiveGeneration.NonuniformClosure

/-! # Learners on the paper's unordered observations

A fixed choice of orientation supplies an ordered learner with input. Conversely,
forgetting each orientation supplies an unordered learner with input. The
finite history available at every round is preserved in both directions.
-/
namespace GenLimit.ContrastiveGeneration

abbrev UnorderedStrategy (α β : Type*) := Generic.FiniteHistoryOperator (UnorderedEdge α) β

theorem unordered_strategy_iff (P : (ℕ → UnorderedEdge α) → (ℕ → β) → Prop) :
    (∃ G : Generic.FiniteHistoryOperator (Edge α) β, ∀ s : ℕ → Edge α,
      P (fun i => (s i).unordered) (fun t => G t (streamPrefix s t))) ↔
    (∃ U : UnorderedStrategy α β, ∀ s : ℕ → UnorderedEdge α,
      P s (fun t => U t (fun i => s i))) := by
  constructor
  · rintro ⟨G,hG⟩
    refine ⟨fun t xs => G t (fun i => (xs i).orient), fun s => ?_⟩
    simpa only [UnorderedEdge.orient_unordered,streamPrefix] using hG (fun i => (s i).orient)
  · rintro ⟨U,hU⟩
    exact ⟨fun t xs => U t (fun i => (xs i).unordered), fun s => hU (fun i => (s i).unordered)⟩

def UnorderedPresentation (s : ℕ → UnorderedEdge α) (h : Set α) : Prop :=
  (∀ i, UnorderedCrosses h (s i)) ∧ h ⊆ {x | ∃ i, x ∈ (s i).vertices}

def UnorderedCorrupted (k : ℕ) (s : ℕ → UnorderedEdge α) (h : Set α) : Prop :=
  (Generic.ViolationIndices s (UnorderedCrosses h)).Finite ∧
    (Generic.ViolationIndices s (UnorderedCrosses h)).ncard ≤ k ∧
    h ⊆ {x | ∃ i, x ∈ (s i).vertices}

private theorem mem_vertices_iff (x : α) (e : Edge α) : x ∈ e.unordered.vertices ↔ Incident x e := by
  classical
  simp [Edge.unordered,Incident]

private theorem presentation_iff (s : ℕ → Edge α) (h : Set α) :
    UnorderedPresentation (fun i => (s i).unordered) h ↔ IsContrastivePresentation s h := by
  simp only [UnorderedPresentation,IsContrastivePresentation,unorderedCrosses_edge_iff,mem_vertices_iff]

private theorem corrupted_iff (k : ℕ) (s : ℕ → Edge α) (h : Set α) :
    UnorderedCorrupted k (fun i => (s i).unordered) h ↔ IsKCorruptedContrastivePresentation k s h := by
  simp only [UnorderedCorrupted,IsKCorruptedContrastivePresentation,Generic.ViolationIndices,
    unorderedCrosses_edge_iff,mem_vertices_iff]

theorem unordered_identification_iff (F : Generic.LanguageFamily α) :
    ContrastivelyIdentifiable F ↔ ∃ U : UnorderedStrategy α ℕ,
      ∀ s : ℕ → UnorderedEdge α, ∀ z, UnorderedPresentation s (F z) →
        ∃ j, F j = F z ∧ ∃ T, ∀ t ≥ T, U t (fun i => s i) = j := by
  rw [← unordered_strategy_iff (fun s out => ∀ z, UnorderedPresentation s (F z) →
      ∃ j, F j = F z ∧ ∃ T, ∀ t ≥ T, out t = j)]
  simp only [presentation_iff]
  exact exists_congr fun _ => forall_comm

theorem unordered_fixed_corruption_iff (F : Generic.LanguageFamily α) (k : ℕ) :
    KContrastivelyIdentifiable k F ↔ ∃ U : UnorderedStrategy α ℕ,
      ∀ s : ℕ → UnorderedEdge α, ∀ z, UnorderedCorrupted k s (F z) →
        ∃ j, F j = F z ∧ ∃ T, ∀ t ≥ T, U t (fun i => s i) = j := by
  rw [← unordered_strategy_iff (fun s out => ∀ z, UnorderedCorrupted k s (F z) →
      ∃ j, F j = F z ∧ ∃ T, ∀ t ≥ T, out t = j)]
  simp only [corrupted_iff]
  exact exists_congr fun _ => forall_comm

theorem unordered_corrupted_identification_iff (F : Generic.LanguageFamily α) :
    FinitelyCorruptionContrastivelyIdentifiable F ↔ ∃ U : UnorderedStrategy α ℕ,
      ∀ s : ℕ → UnorderedEdge α, ∀ k z, UnorderedCorrupted k s (F z) →
        ∃ j, F j = F z ∧ ∃ T, ∀ t ≥ T, U t (fun i => s i) = j := by
  rw [← unordered_strategy_iff (fun s out => ∀ k z, UnorderedCorrupted k s (F z) →
      ∃ j, F j = F z ∧ ∃ T, ∀ t ≥ T, out t = j)]
  simp only [corrupted_iff]
  exact exists_congr fun _ => ⟨fun h s k z => h k z s, fun h k z s => h s k z⟩

theorem unordered_generation_iff (H : Set (Set α)) :
    ContrastivelyGeneratable H ↔ ∃ U : UnorderedStrategy α α,
      ∀ s : ℕ → UnorderedEdge α, ∀ h ∈ H, UnorderedPresentation s h →
        ∃ T, ∀ t ≥ T, U t (fun i => s i) ∈ h ∧
          ¬∃ i : Fin t, U t (fun a => s a) ∈ (s i).vertices := by
  rw [← unordered_strategy_iff (fun s out => ∀ h ∈ H, UnorderedPresentation s h →
      ∃ T, ∀ t ≥ T, out t ∈ h ∧ ¬∃ i : Fin t, out t ∈ (s i).vertices)]
  simp only [presentation_iff,mem_vertices_iff]
  exact exists_congr fun _ => ⟨fun hg s h hh => hg h hh s, fun hg h hh s => hg s h hh⟩

/-- The output condition for a finite unordered sample, including its count of
distinct edges and all incident vertices. -/
noncomputable def UnorderedSafeAt (U : UnorderedStrategy α α) (h : Set α) (d : ℕ) : Prop := by
  classical
  exact ∀ t, ∀ xs : Fin t → UnorderedEdge α, (∀ i, UnorderedCrosses h (xs i)) →
    d ≤ (Finset.univ.image xs).card → U t xs ∈ h ∧ ¬∃ i, U t xs ∈ (xs i).vertices

private def OrderedSafeAt (G : ContrastiveGenerator α) (h : Set α) (d : ℕ) : Prop :=
  ∀ t, ∀ xs : Fin t → Edge α, (∀ i, Crosses h (xs i)) →
    d ≤ (distinctUnorderedEdges xs).card → G t xs ∈ h ∧ G t xs ∉ seenPrefix xs

private theorem safe_orient {G : ContrastiveGenerator α} {h : Set α} {d : ℕ}
    (safe : OrderedSafeAt G h d) :
    UnorderedSafeAt (fun t xs => G t (fun i => (xs i).orient)) h d := by
  intro t xs hc hn
  have hd : d ≤ (distinctUnorderedEdges (fun i => (xs i).orient)).card := by
    simpa only [distinctUnorderedEdges,UnorderedEdge.orient_unordered] using hn
  obtain ⟨hh,hout⟩ := safe t _ (fun i => (unorderedCrosses_orient_iff ..).mpr (hc i)) hd
  refine ⟨hh, ?_⟩
  rintro ⟨i,hi⟩
  apply hout
  refine ⟨i,(mem_vertices_iff ..).mp ?_⟩
  simpa only [UnorderedEdge.orient_unordered] using hi

private theorem safe_forget {U : UnorderedStrategy α α} {h : Set α} {d : ℕ}
    (safe : UnorderedSafeAt U h d) :
    OrderedSafeAt (fun t xs => U t (fun i => (xs i).unordered)) h d := by
  intro t xs hc hn
  obtain ⟨hh,hout⟩ := safe t _ (fun i => (unorderedCrosses_edge_iff ..).mpr (hc i)) hn
  exact ⟨hh,fun ⟨i,hi⟩ => hout ⟨i,(mem_vertices_iff ..).mpr hi⟩⟩

theorem unordered_uniform_iff (H : Set (Set α)) (d : ℕ) :
    UniformlyContrastivelyGeneratableAt H d ↔ ∃ U : UnorderedStrategy α α,
      ∀ h ∈ H, UnorderedSafeAt U h d := by
  constructor
  · rintro ⟨G,hG⟩
    exact ⟨_,fun h hh => safe_orient (hG h hh)⟩
  · rintro ⟨U,hU⟩
    exact ⟨_,fun h hh => safe_forget (hU h hh)⟩

theorem unordered_nonuniform_iff (H : Set (Set α)) :
    NonuniformlyContrastivelyGeneratable H ↔ ∃ U : UnorderedStrategy α α,
      ∀ h ∈ H, ∃ d, UnorderedSafeAt U h d := by
  constructor
  · rintro ⟨G,hG⟩
    exact ⟨_,fun h hh => (hG h hh).imp (fun _ hd => safe_orient hd)⟩
  · rintro ⟨U,hU⟩
    exact ⟨_,fun h hh => (hU h hh).imp (fun _ hd => safe_forget hd)⟩

end GenLimit.ContrastiveGeneration
