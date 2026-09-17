import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Feedback
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Definitions
import GenLimit.Support.StreamPrefix

/-!
# Charikar--Pabbaraju: the GnF dimension

This file formalizes Section 7.1 and Proposition 7.1.  As in the paper, a
generator strategy may depend on its own earlier outputs, and an adversary
strategy may react to them.  The proposition is stated level by level: for
every positive integer `d`, the GnF dimension is at least `d` iff the closure
dimension is at least `d`.  This is exactly the equality of the two extended
natural-valued dimensions, without introducing a separate `ℕ ∪ {∞}` type.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

structure NoFeedbackRound (α : Type*) where
  input : α
  output : α

structure NoFeedbackGeneratorStrategy (α : Type*) where
  output : List (NoFeedbackRound α) → α → α

structure NoFeedbackAdversaryStrategy (α : Type*) where
  input : List (NoFeedbackRound α) → α

def noFeedbackNextRound
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α)
    (h : List (NoFeedbackRound α)) : NoFeedbackRound α :=
  let x := A.input h
  ⟨x, G.output h x⟩

def noFeedbackHistory
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) : ℕ → List (NoFeedbackRound α)
  | 0 => []
  | n + 1 =>
      let h := noFeedbackHistory A G n
      h ++ [noFeedbackNextRound A G h]

@[simp] theorem noFeedbackHistory_length
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) (n : ℕ) :
    (noFeedbackHistory A G n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [noFeedbackHistory, ih]

def noFeedbackRound
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) (t : ℕ) : NoFeedbackRound α :=
  noFeedbackNextRound A G (noFeedbackHistory A G t)

def noFeedbackInput
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) : Stream α :=
  fun t => (noFeedbackRound A G t).input

def noFeedbackOutput
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) : Stream α :=
  fun t => (noFeedbackRound A G t).output

noncomputable def noFeedbackSampleThrough
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) (t : ℕ) : Finset α :=
  Generic.sample (noFeedbackInput A G) (t + 1)

def NoFeedbackAdversaryConsistent
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) (K : Set α) : Prop :=
  Generic.Presents (noFeedbackInput A G) K

def noFeedbackConsistentLanguagesThrough
    (C : Generic.LanguageClass α)
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) (t : ℕ) :
    Set (Generic.Language α) :=
  versionSpace C (noFeedbackSampleThrough A G t)

def noFeedbackEffectiveIntersection
    (C : Generic.LanguageClass α)
    (A : NoFeedbackAdversaryStrategy α)
    (G : NoFeedbackGeneratorStrategy α) (t : ℕ) : Set α :=
  commonCore C (noFeedbackSampleThrough A G t) \
    (↑(noFeedbackSampleThrough A G t) : Set α)

/-- Definition 9's property at level `d`. -/
def GnFDimensionAtLeast
    (C : Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ G : NoFeedbackGeneratorStrategy α,
    ∃ K, K ∈ C ∧ ∃ A : NoFeedbackAdversaryStrategy α,
      NoFeedbackAdversaryConsistent A G K ∧
      ∃ t, d ≤ t + 1 ∧ d ≤ (noFeedbackSampleThrough A G t).card ∧
        noFeedbackEffectiveIntersection C A G t = ∅

theorem gnfDimensionAtLeast_implies_closureDimensionAtLeast
    [Nonempty α]
    {C : Generic.LanguageClass α} {d : ℕ}
    (h : GnFDimensionAtLeast C d) :
    ClosureDimensionAtLeast C d := by
  let G : NoFeedbackGeneratorStrategy α :=
    ⟨fun _ _ => Classical.choice inferInstance⟩
  obtain ⟨K, hKC, A, hAK, t, _hdt, hcard, heff⟩ := h G
  let S := noFeedbackSampleThrough A G t
  refine ⟨S, hcard, ?_, ?_⟩
  · exact ⟨K, hKC, fun x hx =>
      Generic.mem_language_of_mem_sample_of_presents hAK hx⟩
  · have hsub : commonCore C S ⊆ (S : Set α) := by
      intro x hx
      by_contra hxS
      have : x ∈ noFeedbackEffectiveIntersection C A G t :=
        ⟨hx, hxS⟩
      rw [heff] at this
      exact this
    exact S.finite_toSet.subset hsub

private noncomputable abbrev prependFinsetPresentation
    [Countable α] (T : Finset α) (K : Set α) (hK : K.Nonempty) :
    Stream α :=
  GenLimit.Support.prependStream T.toList
    (presentationOfCountableSet K hK)

private theorem prependFinsetPresentation_of_lt
    [Countable α] (T : Finset α) (K : Set α) (hK : K.Nonempty)
    {n : ℕ} (hn : n < T.card) :
    prependFinsetPresentation T K hK n =
      T.toList.get ⟨n, by simpa using hn⟩ := by
  apply GenLimit.Support.prependStream_apply_of_lt

private theorem prependFinsetPresentation_presents
    [Countable α] (T : Finset α) (K : Set α) (hK : K.Nonempty)
    (hTK : (T : Set α) ⊆ K) :
    Generic.Presents (prependFinsetPresentation T K hK) K := by
  classical
  apply GenLimit.Support.prependStream_presents
  · intro x hx
    exact hTK (Finset.mem_toList.mp hx)
  · exact presentationOfCountableSet_presents K hK

private theorem sample_prependFinsetPresentation
    [Countable α] (T : Finset α) (K : Set α) (hK : K.Nonempty) :
    Generic.sample (prependFinsetPresentation T K hK) T.card = T := by
  classical
  ext x
  simp only [Generic.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, hnx⟩
    have hmem : T.toList.get ⟨n, by simpa using hn⟩ ∈ T.toList :=
      List.get_mem _ _
    rw [prependFinsetPresentation_of_lt T K hK hn] at hnx
    rw [← hnx]
    exact Finset.mem_toList.mp hmem
  · intro hx
    have hxlist : x ∈ T.toList := by simpa using hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxlist
    refine ⟨i, by simpa using i.isLt, ?_⟩
    rw [prependFinsetPresentation_of_lt T K hK
      (by simpa using i.isLt)]
    exact hi

private def streamAdversary
    (stream : Stream α) : NoFeedbackAdversaryStrategy α :=
  ⟨fun h => stream h.length⟩

private theorem noFeedbackInput_streamAdversary
    (stream : Stream α) (G : NoFeedbackGeneratorStrategy α) :
    noFeedbackInput (streamAdversary stream) G = stream := by
  funext t
  simp [noFeedbackInput, noFeedbackRound, noFeedbackNextRound,
    streamAdversary, noFeedbackHistory_length]

private theorem versionSpace_commonCore_toFinset
    {C : Generic.LanguageClass α} {S : Finset α}
    (hfinite : (commonCore C S).Finite) :
    versionSpace C hfinite.toFinset = versionSpace C S := by
  ext L
  constructor
  · rintro ⟨hLC, hTL⟩
    exact ⟨hLC, fun x hx =>
      hTL (by
        change x ∈ hfinite.toFinset
        rw [hfinite.mem_toFinset]
        exact sample_subset_commonCore hx)⟩
  · rintro hL
    refine ⟨hL.1, ?_⟩
    intro x hx
    change x ∈ hfinite.toFinset at hx
    rw [hfinite.mem_toFinset] at hx
    exact commonCore_subset_of_mem_versionSpace hL hx

theorem closureDimensionAtLeast_implies_gnfDimensionAtLeast
    [Countable α]
    {C : Generic.LanguageClass α} {d : ℕ} (hd : 0 < d)
    (h : ClosureDimensionAtLeast C d) :
    GnFDimensionAtLeast C d := by
  classical
  obtain ⟨S, hdS, hVS, hfinite⟩ := h
  let T := hfinite.toFinset
  have hST : S ⊆ T := by
    intro x hx
    rw [hfinite.mem_toFinset]
    exact sample_subset_commonCore hx
  have hdT : d ≤ T.card := hdS.trans (Finset.card_le_card hST)
  have hTnonempty : T.Nonempty :=
    Finset.card_pos.mp (hd.trans_le hdT)
  obtain ⟨K, hKVS⟩ := hVS
  have hTK : (T : Set α) ⊆ K := by
    intro x hx
    change x ∈ hfinite.toFinset at hx
    rw [hfinite.mem_toFinset] at hx
    exact commonCore_subset_of_mem_versionSpace hKVS hx
  have hKnonempty : K.Nonempty :=
    ⟨hTnonempty.choose, hTK hTnonempty.choose_spec⟩
  intro G
  let stream := prependFinsetPresentation T K hKnonempty
  let A := streamAdversary stream
  let t := T.card - 1
  have ht : t + 1 = T.card := by
    dsimp [t]
    omega
  have hinput : noFeedbackInput A G = stream :=
    noFeedbackInput_streamAdversary stream G
  have hsample : noFeedbackSampleThrough A G t = T := by
    unfold noFeedbackSampleThrough
    rw [hinput, ht]
    exact sample_prependFinsetPresentation T K hKnonempty
  refine ⟨K, hKVS.1, A, ?_, t, ?_, ?_, ?_⟩
  · rw [NoFeedbackAdversaryConsistent, hinput]
    exact prependFinsetPresentation_presents T K hKnonempty hTK
  · simpa [ht] using hdT
  · simpa [hsample] using hdT
  · unfold noFeedbackEffectiveIntersection
    rw [hsample]
    have hvs := versionSpace_commonCore_toFinset hfinite
    have hcores : commonCore C T = commonCore C S := by
      ext x
      change
        (∀ L, L ∈ versionSpace C T → x ∈ L) ↔
          ∀ L, L ∈ versionSpace C S → x ∈ L
      rw [hvs]
    have hcore : commonCore C T = (T : Set α) := by
      apply Set.Subset.antisymm
      · intro x hx
        change x ∈ hfinite.toFinset
        rw [hfinite.mem_toFinset]
        rw [← hcores]
        exact hx
      · exact sample_subset_commonCore
    rw [hcore, Set.diff_self]

/-- Proposition 7.1, level-by-level form. -/
theorem proposition7_1_gnf_eq_closure
    [Nonempty α] [Countable α]
    (C : Generic.LanguageClass α) {d : ℕ} (hd : 0 < d) :
    GnFDimensionAtLeast C d ↔ ClosureDimensionAtLeast C d :=
  ⟨gnfDimensionAtLeast_implies_closureDimensionAtLeast,
    closureDimensionAtLeast_implies_gnfDimensionAtLeast hd⟩

end GenLimit.CharikarPabbaraju
