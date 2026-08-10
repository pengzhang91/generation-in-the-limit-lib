import GenLimit.Paper00_LanguageIdentification.Text.Model
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Countable

/-!
# #0 Language Identification: locking sequences from text

This file proves the semantic locking-sequence lemma for arbitrary exact positive texts:
If a semantic learner identifies a nonempty language `L` from every
arbitrary text for `L`, then there is a finite `L`-consistent history after
which every further `L`-consistent extension leaves the learner's
conjecture equal to `L`.

`Superfinite.lean` uses this locking lemma to prove
the semantic arbitrary-text superfinite impossibility result described in
Section 8 of Gold's paper.

The proof is the standard diagonal construction.  In the absence of a
stabilizing history, it builds nested finite histories which both enumerate a
fixed text for the target and force one more mind change at every stage.
-/

namespace GenLimit
namespace Gold
namespace Text

/-- Every datum in a finite history belongs to `L`. -/
def HistoryIn (history : List ℕ) (L : Language) : Prop :=
  ∀ x ∈ history, x ∈ L

@[simp] theorem historyIn_nil (L : Language) : HistoryIn [] L := by
  simp [HistoryIn]

@[simp] theorem historyIn_singleton {L : Language} {x : ℕ} :
    HistoryIn [x] L ↔ x ∈ L := by
  simp [HistoryIn]

@[simp] theorem historyIn_append {L : Language} {σ τ : List ℕ} :
    HistoryIn (σ ++ τ) L ↔ HistoryIn σ L ∧ HistoryIn τ L := by
  simp only [HistoryIn, List.mem_append, or_imp, forall_and]

theorem HistoryIn.mono {K L : Language} {σ : List ℕ}
    (hσ : HistoryIn σ K) (hKL : K ⊆ L) :
    HistoryIn σ L := by
  intro x hx
  exact hKL (hσ x hx)

theorem historyIn_textPrefix {stream : ℕ → ℕ} {L : Language}
    (hP : Presents stream L) (t : ℕ) :
    HistoryIn (textPrefix stream t) L := by
  intro x hx
  rw [mem_textPrefix_iff] at hx
  obtain ⟨s, -, rfl⟩ := hx
  rw [← hP]
  exact ⟨s, rfl⟩

/-- At `σ`, the learner is syntactically stable under every finite extension
whose data remain in `L`.  Correctness is intentionally not part of this
definition; it follows from identification by completing `σ` to a text. -/
def IsStabilizing (M : TextLearner Language) (L : Language)
    (σ : List ℕ) : Prop :=
  HistoryIn σ L ∧
    ∀ τ, HistoryIn τ L → M (σ ++ τ) = M σ

/-- A Gold locking sequence is a stabilizing sequence whose conjecture is the
target language. -/
def IsLocking (M : TextLearner Language) (L : Language)
    (σ : List ℕ) : Prop :=
  HistoryIn σ L ∧ M σ = L ∧
    ∀ τ, HistoryIn τ L → M (σ ++ τ) = L

theorem exists_presentation_of_nonempty {L : Language} (hL : L.Nonempty) :
    ∃ stream : ℕ → ℕ, Presents stream L := by
  classical
  letI : Nonempty {x // x ∈ L} := hL.to_subtype
  obtain ⟨f, hf⟩ := exists_surjective_nat {x // x ∈ L}
  let stream : ℕ → ℕ := fun n => (f n).1
  refine ⟨stream, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact (f n).2
  · intro x hx
    obtain ⟨n, hn⟩ := hf ⟨x, hx⟩
    refine ⟨n, ?_⟩
    exact congrArg Subtype.val hn

private theorem exists_change_extension
    {M : TextLearner Language} {L : Language}
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    {σ : List ℕ} (hσ : HistoryIn σ L) :
    ∃ τ, HistoryIn τ L ∧ M (σ ++ τ) ≠ M σ := by
  by_contra h
  push_neg at h
  exact hnone ⟨σ, hσ, h⟩

noncomputable section

private def changeExtension
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (σ : List ℕ) (hσ : HistoryIn σ L) : List ℕ :=
  Classical.choose (exists_change_extension hnone hσ)

private theorem changeExtension_historyIn
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (σ : List ℕ) (hσ : HistoryIn σ L) :
    HistoryIn (changeExtension M L hnone σ hσ) L :=
  (Classical.choose_spec (exists_change_extension hnone hσ)).1

private theorem changeExtension_changes
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (σ : List ℕ) (hσ : HistoryIn σ L) :
    M (σ ++ changeExtension M L hnone σ hσ) ≠ M σ :=
  (Classical.choose_spec (exists_change_extension hnone hσ)).2

private def badState
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) :
    ℕ → {σ : List ℕ // HistoryIn σ L}
  | 0 => ⟨[], historyIn_nil L⟩
  | n + 1 =>
      let previous := badState M L hnone base hbase n
      let probe : List ℕ := previous.1 ++ [base n]
      have hprobe : HistoryIn probe L := by
        rw [historyIn_append]
        refine ⟨previous.2, ?_⟩
        rw [historyIn_singleton, ← hbase]
        exact ⟨n, rfl⟩
      let extension := changeExtension M L hnone probe hprobe
      ⟨probe ++ extension,
        (historyIn_append.mpr
          ⟨hprobe, changeExtension_historyIn M L hnone probe hprobe⟩)⟩

private def badHistory
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) : List ℕ :=
  (badState M L hnone base hbase n).1

private def badProbe
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) : List ℕ :=
  badHistory M L hnone base hbase n ++ [base n]

private theorem badHistory_historyIn
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    HistoryIn (badHistory M L hnone base hbase n) L :=
  (badState M L hnone base hbase n).2

private theorem badProbe_historyIn
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    HistoryIn (badProbe M L hnone base hbase n) L := by
  rw [badProbe, historyIn_append]
  refine ⟨badHistory_historyIn M L hnone base hbase n, ?_⟩
  rw [historyIn_singleton, ← hbase]
  exact ⟨n, rfl⟩

private theorem badHistory_succ
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    badHistory M L hnone base hbase (n + 1) =
      badProbe M L hnone base hbase n ++
        changeExtension M L hnone
          (badProbe M L hnone base hbase n)
          (badProbe_historyIn M L hnone base hbase n) := by
  simp only [badHistory, badState, badProbe]

private theorem badProbe_prefix_succ
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    badProbe M L hnone base hbase n <+:
      badHistory M L hnone base hbase (n + 1) := by
  rw [badHistory_succ]
  exact List.prefix_append _ _

private theorem badHistory_prefix_probe
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    badHistory M L hnone base hbase n <+:
      badProbe M L hnone base hbase n := by
  exact List.prefix_append _ _

private theorem badHistory_prefix_succ
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    badHistory M L hnone base hbase n <+:
      badHistory M L hnone base hbase (n + 1) :=
  (badHistory_prefix_probe M L hnone base hbase n).trans
    (badProbe_prefix_succ M L hnone base hbase n)

private theorem badHistory_mono
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L)
    {n m : ℕ} (hnm : n ≤ m) :
    badHistory M L hnone base hbase n <+:
      badHistory M L hnone base hbase m := by
  induction m with
  | zero =>
      have : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact List.prefix_refl _
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
      · exact List.prefix_refl _
      · exact (ih (Nat.le_of_lt_succ hlt)).trans
          (badHistory_prefix_succ M L hnone base hbase m)

private theorem badHistory_length_lower
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    n ≤ (badHistory M L hnone base hbase n).length := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := (badProbe_prefix_succ M L hnone base hbase n).length_le
      simp only [badProbe, List.length_append, List.length_singleton] at hp
      omega

private def badText
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (t : ℕ) : ℕ :=
  (badHistory M L hnone base hbase (t + 1)).get
    ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t)
      (badHistory_length_lower M L hnone base hbase (t + 1))⟩

private theorem get_eq_of_prefix
    {α : Type*} {σ τ : List α} (h : σ <+: τ)
    (i : ℕ) (hi : i < σ.length) :
    τ.get ⟨i, lt_of_lt_of_le hi h.length_le⟩ = σ.get ⟨i, hi⟩ := by
  obtain ⟨ρ, rfl⟩ := h
  exact List.getElem_append_left hi

private theorem badText_agrees_with_history
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L)
    (n i : ℕ) (hi : i < (badHistory M L hnone base hbase n).length) :
    badText M L hnone base hbase i =
      (badHistory M L hnone base hbase n).get ⟨i, hi⟩ := by
  unfold badText
  rcases le_total n (i + 1) with hni | hin
  · exact get_eq_of_prefix
      (badHistory_mono M L hnone base hbase hni) i hi
  · symm
    exact get_eq_of_prefix
      (badHistory_mono M L hnone base hbase hin) i
      (lt_of_lt_of_le (Nat.lt_succ_self i)
        (badHistory_length_lower M L hnone base hbase (i + 1)))

private theorem textPrefix_badText_eq_history
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    textPrefix (badText M L hnone base hbase)
        (badHistory M L hnone base hbase n).length =
      badHistory M L hnone base hbase n := by
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    simp only [textPrefix, List.get_eq_getElem, List.getElem_map, List.getElem_range]
    exact badText_agrees_with_history M L hnone base hbase n i h₂

private theorem textPrefix_badText_eq_of_prefix_history
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L)
    {σ : List ℕ} {n : ℕ}
    (hσ : σ <+: badHistory M L hnone base hbase n) :
    textPrefix (badText M L hnone base hbase) σ.length = σ := by
  have hfull := textPrefix_badText_eq_history M L hnone base hbase n
  have hlen := hσ.length_le
  have htake :
      (textPrefix (badText M L hnone base hbase)
        (badHistory M L hnone base hbase n).length).take σ.length =
        textPrefix (badText M L hnone base hbase) σ.length := by
    rw [textPrefix, textPrefix, ← List.map_take]
    simp [hlen]
  rw [← htake, hfull]
  exact (List.prefix_iff_eq_take.mp hσ).symm

private theorem badText_presents
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) :
    Presents (badText M L hnone base hbase) L := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    have hmem :
        (badHistory M L hnone base hbase (t + 1)).get
            ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t)
              (badHistory_length_lower M L hnone base hbase (t + 1))⟩ ∈
          badHistory M L hnone base hbase (t + 1) :=
      List.get_mem _ _
    exact badHistory_historyIn M L hnone base hbase (t + 1) _ hmem
  · intro x hx
    rw [← hbase] at hx
    obtain ⟨n, rfl⟩ := hx
    have hmem :
        base n ∈ badHistory M L hnone base hbase (n + 1) := by
      exact (badProbe_prefix_succ M L hnone base hbase n).mem
        (by simp [badProbe])
    rw [← textPrefix_badText_eq_history M L hnone base hbase (n + 1)] at hmem
    rw [mem_textPrefix_iff] at hmem
    obtain ⟨t, -, ht⟩ := hmem
    exact ⟨t, ht⟩

private theorem badHistory_mind_change
    (M : TextLearner Language) (L : Language)
    (hnone : ¬ ∃ σ, IsStabilizing M L σ)
    (base : ℕ → ℕ) (hbase : Presents base L) (n : ℕ) :
    M (badHistory M L hnone base hbase (n + 1)) ≠
      M (badProbe M L hnone base hbase n) := by
  rw [badHistory_succ]
  exact changeExtension_changes M L hnone
    (badProbe M L hnone base hbase n)
    (badProbe_historyIn M L hnone base hbase n)

/-- **Semantic stabilizing-sequence lemma.**  Identification of a nonempty
language from every arbitrary exact text yields a finite target-consistent
history after which no target-consistent finite extension changes the
conjecture. -/
theorem exists_stabilizing_of_identifiesLanguage
    {M : TextLearner Language} {L : Language}
    (hL : L.Nonempty)
    (hM : IdentifiesLanguage semanticNaming M L) :
    ∃ σ, IsStabilizing M L σ := by
  by_contra hnone
  obtain ⟨base, hbase⟩ := exists_presentation_of_nonempty hL
  obtain ⟨guess, _, T, hT⟩ :=
    hM (badText M L hnone base hbase)
      (badText_presents M L hnone base hbase)
  have hprobePrefix :
      badProbe M L hnone base hbase T <+:
        badHistory M L hnone base hbase (T + 1) :=
    badProbe_prefix_succ M L hnone base hbase T
  have hprobeTime :
      T ≤ (badProbe M L hnone base hbase T).length := by
    have hlow := badHistory_length_lower M L hnone base hbase T
    simp only [badProbe, List.length_append, List.length_singleton]
    omega
  have hhistoryTime :
      T ≤ (badHistory M L hnone base hbase (T + 1)).length :=
    le_trans hprobeTime hprobePrefix.length_le
  have hprobeGuess :
      M (badProbe M L hnone base hbase T) = guess := by
    rw [← textPrefix_badText_eq_of_prefix_history M L hnone base hbase hprobePrefix]
    exact hT _ hprobeTime
  have hhistoryGuess :
      M (badHistory M L hnone base hbase (T + 1)) = guess := by
    rw [← textPrefix_badText_eq_history M L hnone base hbase (T + 1)]
    exact hT _ hhistoryTime
  exact (badHistory_mind_change M L hnone base hbase T)
    (hhistoryGuess.trans hprobeGuess.symm)

/-- **Semantic locking-sequence lemma.**  The stabilizing conjecture is the
target itself, because the stabilizing history can be completed to an exact
text for `L`. -/
theorem exists_locking_of_identifiesLanguage
    {M : TextLearner Language} {L : Language}
    (hL : L.Nonempty)
    (hM : IdentifiesLanguage semanticNaming M L) :
    ∃ σ, IsLocking M L σ := by
  obtain ⟨σ, hσL, hstable⟩ :=
    exists_stabilizing_of_identifiesLanguage hL hM
  obtain ⟨base, hbase⟩ := exists_presentation_of_nonempty hL
  let stream : ℕ → ℕ := fun t =>
    if ht : t < σ.length then σ.get ⟨t, ht⟩ else base (t - σ.length)
  have hstreamP : Presents stream L := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, rfl⟩
      by_cases ht : t < σ.length
      · simp only [stream, dif_pos ht]
        exact hσL _ (List.get_mem σ ⟨t, ht⟩)
      · simp only [stream, dif_neg ht]
        rw [← hbase]
        exact ⟨t - σ.length, rfl⟩
    · intro x hx
      rw [← hbase] at hx
      obtain ⟨n, rfl⟩ := hx
      refine ⟨σ.length + n, ?_⟩
      have hnot : ¬ σ.length + n < σ.length := by omega
      simp [stream, hnot]
  have hprefix : textPrefix stream σ.length = σ := by
    apply List.ext_get
    · simp
    · intro i h₁ h₂
      simp only [textPrefix, List.get_eq_getElem, List.getElem_map,
        List.getElem_range, stream, dif_pos h₂]
  obtain ⟨guess, hguess, T, hT⟩ := hM stream hstreamP
  have hguess' : guess = L := by
    simpa [semanticNaming] using hguess
  let t := max T σ.length
  have hσPrefix : σ <+: textPrefix stream t := by
    rw [List.prefix_iff_eq_take]
    have hlen : σ.length ≤ t := le_max_right _ _
    rw [← hprefix]
    rw [textPrefix, textPrefix, ← List.map_take]
    simp [hlen]
  obtain ⟨τ, hτ⟩ := hσPrefix
  have hτL : HistoryIn τ L := by
    have hall := historyIn_textPrefix hstreamP t
    rw [← hτ, historyIn_append] at hall
    exact hall.2
  have hMσ : M σ = L := by
    calc
      M σ = M (σ ++ τ) := (hstable τ hτL).symm
      _ = M (textPrefix stream t) := by rw [hτ]
      _ = guess := hT t (le_max_left _ _)
      _ = L := hguess'
  refine ⟨σ, hσL, hMσ, ?_⟩
  intro τ hτL
  exact (hstable τ hτL).trans hMσ

end

end Text
end Gold
end GenLimit
