import GenLimit.Paper00A_PositiveDataInference.Effective.Definitions
import GenLimit.Paper00_LanguageIdentification.Text.Locking

/-!
# Syntactic stabilization for effective Angluin learners

This module isolates the diagonal fact needed by effective necessity: a
successful list learner has a finite target-consistent history after which its
syntactic index conjecture cannot change along any target-consistent finite
continuation.  The construction is separate from the semantic tell-tale
reduction, which reuses Gold directly.
-/

namespace GenLimit.Angluin

open GenLimit.Generic
open GenLimit.Gold.Text

/-! ## The syntactic stabilization fact needed by the effective construction -/

/-- A list learner makes the same *index* conjecture after every
target-consistent finite continuation. -/
def SyntacticallyStabilizing
    (M : EffectiveIdentifier) (L : Set ℕ) (history : List ℕ) : Prop :=
  HistoryIn history L ∧
    ∀ extension, HistoryIn extension L →
      M (history ++ extension) = M history

private theorem exists_change_extension
    {M : EffectiveIdentifier} {L : Set ℕ}
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    {history : List ℕ} (hhistory : HistoryIn history L) :
    ∃ extension, HistoryIn extension L ∧
      M (history ++ extension) ≠ M history := by
  by_contra h
  push_neg at h
  exact hnone ⟨history, hhistory, h⟩

noncomputable section

private def changeExtension
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (history : List ℕ) (hhistory : HistoryIn history L) : List ℕ :=
  Classical.choose (exists_change_extension hnone hhistory)

private theorem changeExtension_historyIn
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (history : List ℕ) (hhistory : HistoryIn history L) :
    HistoryIn (changeExtension M L hnone history hhistory) L :=
  (Classical.choose_spec (exists_change_extension hnone hhistory)).1

private theorem changeExtension_changes
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (history : List ℕ) (hhistory : HistoryIn history L) :
    M (history ++ changeExtension M L hnone history hhistory) ≠ M history :=
  (Classical.choose_spec (exists_change_extension hnone hhistory)).2

private def badState
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) :
    ℕ → {history : List ℕ // HistoryIn history L}
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
        historyIn_append.mpr
          ⟨hprobe, changeExtension_historyIn M L hnone probe hprobe⟩⟩

private def badHistory
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L)
    (n : ℕ) : List ℕ :=
  (badState M L hnone base hbase n).1

private def badProbe
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L)
    (n : ℕ) : List ℕ :=
  badHistory M L hnone base hbase n ++ [base n]

private theorem badHistory_historyIn
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    HistoryIn (badHistory M L hnone base hbase n) L :=
  (badState M L hnone base hbase n).2

private theorem badProbe_historyIn
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    HistoryIn (badProbe M L hnone base hbase n) L := by
  rw [badProbe, historyIn_append]
  refine ⟨badHistory_historyIn M L hnone base hbase n, ?_⟩
  rw [historyIn_singleton, ← hbase]
  exact ⟨n, rfl⟩

private theorem badHistory_succ
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    badHistory M L hnone base hbase (n + 1) =
      badProbe M L hnone base hbase n ++
        changeExtension M L hnone
          (badProbe M L hnone base hbase n)
          (badProbe_historyIn M L hnone base hbase n) := by
  simp only [badHistory, badState, badProbe]

private theorem badProbe_prefix_succ
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    badProbe M L hnone base hbase n <+:
      badHistory M L hnone base hbase (n + 1) := by
  rw [badHistory_succ]
  exact List.prefix_append _ _

private theorem badHistory_prefix_probe
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    badHistory M L hnone base hbase n <+:
      badProbe M L hnone base hbase n :=
  List.prefix_append _ _

private theorem badHistory_prefix_succ
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    badHistory M L hnone base hbase n <+:
      badHistory M L hnone base hbase (n + 1) :=
  (badHistory_prefix_probe M L hnone base hbase n).trans
    (badProbe_prefix_succ M L hnone base hbase n)

private theorem badHistory_mono
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L)
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
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    n ≤ (badHistory M L hnone base hbase n).length := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := (badProbe_prefix_succ M L hnone base hbase n).length_le
      simp only [badProbe, List.length_append, List.length_singleton] at hp
      omega

private def badText
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L)
    (t : ℕ) : ℕ :=
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
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L)
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
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    GenLimit.textPrefix (badText M L hnone base hbase)
        (badHistory M L hnone base hbase n).length =
      badHistory M L hnone base hbase n := by
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    simp only [GenLimit.textPrefix, List.get_eq_getElem, List.getElem_map,
      List.getElem_range]
    exact badText_agrees_with_history M L hnone base hbase n i h₂

private theorem textPrefix_badText_eq_of_prefix_history
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L)
    {history : List ℕ} {n : ℕ}
    (hhistory : history <+: badHistory M L hnone base hbase n) :
    GenLimit.textPrefix (badText M L hnone base hbase) history.length =
      history := by
  have hfull := textPrefix_badText_eq_history M L hnone base hbase n
  have hlen := hhistory.length_le
  have htake :
      (GenLimit.textPrefix (badText M L hnone base hbase)
        (badHistory M L hnone base hbase n).length).take history.length =
        GenLimit.textPrefix (badText M L hnone base hbase) history.length := by
    rw [GenLimit.textPrefix, GenLimit.textPrefix, ← List.map_take]
    simp [hlen]
  rw [← htake, hfull]
  exact (List.prefix_iff_eq_take.mp hhistory).symm

private theorem badText_presents
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) :
    GenLimit.Presents (badText M L hnone base hbase) L := by
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
    have hmem : base n ∈ badHistory M L hnone base hbase (n + 1) :=
      (badProbe_prefix_succ M L hnone base hbase n).mem
        (by simp [badProbe])
    rw [← textPrefix_badText_eq_history M L hnone base hbase (n + 1)] at hmem
    rw [GenLimit.mem_textPrefix_iff] at hmem
    obtain ⟨t, -, ht⟩ := hmem
    exact ⟨t, ht⟩

private theorem badHistory_mind_change
    (M : EffectiveIdentifier) (L : Set ℕ)
    (hnone : ¬ ∃ history, SyntacticallyStabilizing M L history)
    (base : ℕ → ℕ) (hbase : GenLimit.Presents base L) (n : ℕ) :
    M (badHistory M L hnone base hbase (n + 1)) ≠
      M (badProbe M L hnone base hbase n) := by
  rw [badHistory_succ]
  exact changeExtension_changes M L hnone
    (badProbe M L hnone base hbase n)
    (badProbe_historyIn M L hnone base hbase n)

theorem exists_syntacticallyStabilizing
    {M : EffectiveIdentifier} {L : Set ℕ} (hL : L.Nonempty)
    (hM : ∀ stream : ℕ → ℕ, GenLimit.Presents stream L →
      ∃ guess T, ∀ t, T ≤ t →
        M (GenLimit.textPrefix stream t) = guess) :
    ∃ history, SyntacticallyStabilizing M L history := by
  by_contra hnone
  obtain ⟨base, hbase⟩ := exists_presentation_of_nonempty hL
  obtain ⟨guess, T, hT⟩ :=
    hM (badText M L hnone base hbase)
      (badText_presents M L hnone base hbase)
  have hprobePrefix :
      badProbe M L hnone base hbase T <+:
        badHistory M L hnone base hbase (T + 1) :=
    badProbe_prefix_succ M L hnone base hbase T
  have hprobeTime : T ≤ (badProbe M L hnone base hbase T).length := by
    have hlow := badHistory_length_lower M L hnone base hbase T
    simp only [badProbe, List.length_append, List.length_singleton]
    omega
  have hhistoryTime :
      T ≤ (badHistory M L hnone base hbase (T + 1)).length :=
    hprobeTime.trans hprobePrefix.length_le
  have hprobeGuess : M (badProbe M L hnone base hbase T) = guess := by
    rw [← textPrefix_badText_eq_of_prefix_history
      M L hnone base hbase hprobePrefix]
    exact hT _ hprobeTime
  have hhistoryGuess :
      M (badHistory M L hnone base hbase (T + 1)) = guess := by
    rw [← textPrefix_badText_eq_history M L hnone base hbase (T + 1)]
    exact hT _ hhistoryTime
  exact (badHistory_mind_change M L hnone base hbase T)
    (hhistoryGuess.trans hprobeGuess.symm)

end

end GenLimit.Angluin
