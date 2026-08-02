import GenLimit.ContrastiveGeneration.CorruptedPresentations
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

/-!
# Absence counts for corrupted co-singleton presentations

This file formalizes Algorithm 1 and Example 6.7 of Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*
(arXiv:2605.06211v1).

For the co-singleton support centered at `s`, an honest contrastive edge is
exactly an edge incident to `s`.  Consequently, the absence count of the true
center is bounded by the number of corrupted observations.
-/

namespace GenLimit
namespace ContrastiveGeneration

instance instDecidableIncident [DecidableEq α]
    (x : α) (e : Edge α) : Decidable (Incident x e) := by
  unfold Incident
  infer_instance

instance instDecidableCrossesCoSingleton [DecidableEq α]
    (s : α) (e : Edge α) :
    Decidable (Crosses (coSingletonSupport s) e) := by
  unfold Crosses coSingletonSupport
  infer_instance

/-- Endpoints observed in a finite contrastive history. -/
def seenEndpoints [DecidableEq α]
    {t : ℕ} (history : Fin t → Edge α) : Finset α :=
  (Finset.univ.image fun i => (history i).left) ∪
    (Finset.univ.image fun i => (history i).right)

/-- Algorithm 1's absence count on a finite contrastive history. -/
def absenceCount [DecidableEq α]
    {t : ℕ} (history : Fin t → Edge α) (x : α) : ℕ :=
  (Finset.univ.filter fun i => ¬Incident x (history i)).card

/-- The equivalent prefix count for an infinite stream. -/
def streamAbsenceCount [DecidableEq α]
    (stream : ℕ → Edge α) (x : α) (t : ℕ) : ℕ :=
  ((Finset.range t).filter fun i => ¬Incident x (stream i)).card

theorem absenceCount_streamPrefix
    [DecidableEq α]
    (stream : ℕ → Edge α) (x : α) (t : ℕ) :
    absenceCount (streamPrefix stream t) x =
      streamAbsenceCount stream x t := by
  classical
  unfold absenceCount streamAbsenceCount streamPrefix
  let e : Fin t ↪ ℕ := Fin.valEmbedding
  rw [← Finset.card_map e]
  congr 1
  ext n
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, by simpa [streamPrefix] using hi⟩
  · rintro ⟨hnt, hn⟩
    refine ⟨⟨n, hnt⟩, ?_, rfl⟩
    simpa [streamPrefix] using hn

theorem mem_seenEndpoints_iff
    [DecidableEq α]
    {t : ℕ} {history : Fin t → Edge α} {x : α} :
    x ∈ seenEndpoints history ↔
      ∃ i, Incident x (history i) := by
  classical
  simp only [seenEndpoints, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and, Incident]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩
  · rintro ⟨i, hi | hi⟩
    · left
      exact ⟨i, hi.symm⟩
    · right
      exact ⟨i, hi.symm⟩

/-- For a co-singleton target, crossing the cut is the same as containing its
unique negative point. -/
theorem crosses_coSingletonSupport_iff_incident
    (s : α) (e : Edge α) :
    Crosses (coSingletonSupport s) e ↔ Incident s e := by
  classical
  constructor
  · intro hcross
    rcases hcross with hcross | hcross
    · exact Or.inr (not_ne_iff.mp hcross.2).symm
    · exact Or.inl (not_ne_iff.mp hcross.2).symm
  · intro hincident
    rcases hincident with rfl | rfl
    · exact Or.inr ⟨e.ne.symm, by simp [coSingletonSupport]⟩
    · exact Or.inl ⟨e.ne, by simp [coSingletonSupport]⟩

/-- Every prefix absence of the true co-singleton center is a corrupted
observation. -/
theorem trueCenter_absence_indices_subset_bad
    [DecidableEq α]
    (stream : ℕ → Edge α) (s : α) (t : ℕ) :
    ((Finset.range t).filter fun i => ¬Incident s (stream i)) ⊆
      ((Finset.range t).filter fun i =>
        ¬Crosses (coSingletonSupport s) (stream i)) := by
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, fun hcross =>
    hi.2 ((crosses_coSingletonSupport_iff_incident s (stream i)).mp hcross)⟩

/-- The true center's absence count is bounded by the declared corruption
budget at every time. -/
theorem trueCenter_streamAbsenceCount_le
    {k s t : ℕ} {stream : ℕ → Edge ℕ}
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s)) :
    streamAbsenceCount stream s t ≤ k := by
  classical
  let bad : Set ℕ :=
    {i : ℕ | ¬Crosses (coSingletonSupport s) (stream i)}
  have hsubset :
      {i ∈ Finset.range t | ¬Incident s (stream i)} ⊆
        hP.1.toFinset := by
    intro i hi
    have hibad :
        ¬Crosses (coSingletonSupport s) (stream i) :=
      (Finset.mem_filter.mp
        (trueCenter_absence_indices_subset_bad stream s t hi)).2
    exact hP.1.mem_toFinset.mpr hibad
  calc
    streamAbsenceCount stream s t =
        ((Finset.range t).filter
          fun i => ¬Incident s (stream i)).card := by
          simp only [streamAbsenceCount]
    _ ≤ hP.1.toFinset.card := Finset.card_le_card hsubset
    _ = bad.ncard := by
      symm
      exact Set.ncard_eq_toFinset_card bad hP.1
    _ ≤ k := hP.2.1

/-- Vertices appearing at observation indices from `I`. -/
def verticesAtIndices
    (stream : ℕ → Edge α) (I : Set ℕ) : Set α :=
  (fun n => (stream n).left) '' I ∪
    (fun n => (stream n).right) '' I

theorem verticesAtIndices_finite
    {stream : ℕ → Edge α} {I : Set ℕ} (hI : I.Finite) :
    (verticesAtIndices stream I).Finite :=
  (hI.image fun n => (stream n).left).union
    (hI.image fun n => (stream n).right)

theorem mem_verticesAtIndices_of_incident
    {stream : ℕ → Edge α} {I : Set ℕ} {n : ℕ} {x : α}
    (hn : n ∈ I) (hx : Incident x (stream n)) :
    x ∈ verticesAtIndices stream I := by
  rcases hx with rfl | rfl
  · exact Or.inl ⟨n, hn, rfl⟩
  · exact Or.inr ⟨n, hn, rfl⟩

theorem incident_eq_of_two_distinct_incident
    {e : Edge α} {s x u : α}
    (hsx : s ≠ x)
    (hs : Incident s e) (hx : Incident x e)
    (hu : Incident u e) :
    u = s ∨ u = x := by
  rcases hs with rfl | rfl <;>
    rcases hx with hx | hx <;>
    rcases hu with hu | hu
  · exact False.elim (hsx hx.symm)
  · exact False.elim (hsx hx.symm)
  · exact Or.inl hu
  · exact Or.inr (hu.trans hx.symm)
  · exact Or.inr (hu.trans hx.symm)
  · exact Or.inl hu
  · exact False.elim (hsx hx.symm)
  · exact False.elim (hsx hx.symm)

/-- Every false candidate is omitted by infinitely many observations of a
finitely corrupted co-singleton presentation. -/
theorem falseCenter_omission_indices_infinite
    {k s x : ℕ} {stream : ℕ → Edge ℕ}
    (hxs : x ≠ s)
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s)) :
    {n : ℕ | ¬Incident x (stream n)}.Infinite := by
  classical
  by_contra homitInfinite
  have homit : {n : ℕ | ¬Incident x (stream n)}.Finite :=
    Set.not_infinite.mp homitInfinite
  let bad : Set ℕ :=
    {n : ℕ | ¬Crosses (coSingletonSupport s) (stream n)}
  let exceptional : Set ℕ :=
    bad ∪ {n : ℕ | ¬Incident x (stream n)}
  have hexceptional : exceptional.Finite :=
    hP.1.union homit
  let used : Set ℕ :=
    verticesAtIndices stream exceptional ∪ {s, x}
  have hused : used.Finite :=
    (verticesAtIndices_finite hexceptional).union
      ((Set.finite_singleton x).insert s)
  obtain ⟨u, hu⟩ := hused.exists_notMem
  have hus : u ≠ s := by
    intro hus
    apply hu
    exact Or.inr (by simp [hus])
  have hux : u ≠ x := by
    intro hux
    apply hu
    exact Or.inr (by simp [hux])
  have huTarget : u ∈ coSingletonSupport s := hus
  obtain ⟨n, hun⟩ := hP.2.2 huTarget
  have hnnot : n ∉ exceptional := by
    intro hn
    apply hu
    exact Or.inl
      (mem_verticesAtIndices_of_incident hn hun)
  have hnHonest :
      Crosses (coSingletonSupport s) (stream n) := by
    by_contra hbad
    exact hnnot (Or.inl hbad)
  have hnx : Incident x (stream n) := by
    by_contra hnot
    exact hnnot (Or.inr hnot)
  have hns : Incident s (stream n) :=
    (crosses_coSingletonSupport_iff_incident s (stream n)).mp hnHonest
  rcases incident_eq_of_two_distinct_incident
      hxs.symm hns hnx hun with hus' | hux'
  · exact hus hus'
  · exact hux hux'

/-- Infinitely many omissions force every fixed finite absence threshold to
be exceeded eventually. -/
theorem eventually_streamAbsenceCount_gt
    [DecidableEq α]
    {stream : ℕ → Edge α} {x : α}
    (hinfinite : {n : ℕ | ¬Incident x (stream n)}.Infinite)
    (k : ℕ) :
    ∃ T, ∀ t, T ≤ t →
      k < streamAbsenceCount stream x t := by
  classical
  obtain ⟨F, hFsubset, hFcard⟩ :=
    hinfinite.exists_subset_card_eq (k + 1)
  obtain ⟨T, hFT⟩ := F.exists_nat_subset_range
  refine ⟨T, ?_⟩
  intro t hT
  have hsubset :
      F ⊆ (Finset.range t).filter
        (fun i => ¬Incident x (stream i)) := by
    intro n hn
    have hnT : n ∈ Finset.range T := hFT hn
    exact Finset.mem_filter.mpr
      ⟨Finset.range_mono hT hnT, hFsubset hn⟩
  have hcard :
      k + 1 ≤
        ((Finset.range t).filter
          (fun i => ¬Incident x (stream i))).card := by
    rw [← hFcard]
    exact Finset.card_le_card hsubset
  simpa only [streamAbsenceCount] using hcard

/-- The true center eventually belongs to the observed candidate set. -/
theorem trueCenter_eventually_seen
    {k s : ℕ} {stream : ℕ → Edge ℕ}
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s)) :
    ∃ T, ∀ t, T ≤ t →
      s ∈ seenEndpoints (streamPrefix stream t) := by
  classical
  obtain ⟨n, hnHonest⟩ := hP.1.exists_notMem
  have hcross :
      Crosses (coSingletonSupport s) (stream n) := by
    simpa using hnHonest
  have hincident : Incident s (stream n) :=
    (crosses_coSingletonSupport_iff_incident s (stream n)).mp hcross
  refine ⟨n + 1, ?_⟩
  intro t ht
  rw [mem_seenEndpoints_iff]
  let i : Fin t :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) ht⟩
  exact ⟨i, by simpa [streamPrefix, i] using hincident⟩

/-- An absence-count minimizer on the currently observed endpoints.  The
choice among tied minimizers is immaterial to the convergence proof. -/
noncomputable def absenceCountIdentifier : ContrastiveIdentifier ℕ :=
  fun _t history => by
    classical
    by_cases hseen : (seenEndpoints history).Nonempty
    · exact Classical.choose
        (Finset.exists_min_image
          (seenEndpoints history)
          (fun x => absenceCount history x) hseen)
    · exact 0

theorem absenceCountIdentifier_mem
    {t : ℕ} {history : Fin t → Edge ℕ}
    (hseen : (seenEndpoints history).Nonempty) :
    absenceCountIdentifier t history ∈ seenEndpoints history := by
  classical
  simp only [absenceCountIdentifier, dif_pos hseen]
  exact
    (Classical.choose_spec
      (Finset.exists_min_image
        (seenEndpoints history)
        (fun x => absenceCount history x) hseen)).1

theorem absenceCountIdentifier_minimal
    {t : ℕ} {history : Fin t → Edge ℕ}
    (hseen : (seenEndpoints history).Nonempty)
    {x : ℕ} (hx : x ∈ seenEndpoints history) :
    absenceCount history (absenceCountIdentifier t history) ≤
      absenceCount history x := by
  classical
  simp only [absenceCountIdentifier, dif_pos hseen]
  exact
    (Classical.choose_spec
      (Finset.exists_min_image
        (seenEndpoints history)
        (fun y => absenceCount history y) hseen)).2 x hx

/-- A candidate whose absence count is at most `k` must already occur in the
first `k+1` observations.  This is the finite-competitor reduction in the
proof of Theorem 6.6. -/
theorem seen_early_of_streamAbsenceCount_le
    [DecidableEq α]
    {stream : ℕ → Edge α} {x : α} {t k : ℕ}
    (hx : x ∈ seenEndpoints (streamPrefix stream t))
    (hcount : streamAbsenceCount stream x t ≤ k) :
    x ∈ seenEndpoints (streamPrefix stream (k + 1)) := by
  classical
  rw [mem_seenEndpoints_iff] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  let hex : ∃ n : ℕ, Incident x (stream n) :=
    ⟨i, by simpa [streamPrefix] using hi⟩
  let first := Nat.find hex
  have hfirstIncident : Incident x (stream first) :=
    Nat.find_spec hex
  have hfirstLt : first < t := by
    exact
      Nat.lt_of_le_of_lt
        (Nat.find_min' hex
          (by simpa [streamPrefix] using hi))
        i.isLt
  have hrange :
      Finset.range first ⊆
        (Finset.range t).filter
          (fun n => ¬Incident x (stream n)) := by
    intro n hn
    have hnfirst : n < first := Finset.mem_range.mp hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hnfirst.trans hfirstLt),
        Nat.find_min hex hnfirst⟩
  have hfirstLeCount :
      first ≤ streamAbsenceCount stream x t := by
    simpa [streamAbsenceCount] using
      (Finset.card_le_card hrange)
  have hfirstLe : first ≤ k :=
    hfirstLeCount.trans hcount
  let j : Fin (k + 1) :=
    ⟨first, Nat.lt_succ_iff.mpr hfirstLe⟩
  exact ⟨j, by simpa [streamPrefix, j] using hfirstIncident⟩

private noncomputable def competitorThreshold
    {k s : ℕ} {stream : ℕ → Edge ℕ}
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s))
    (x : ℕ) : ℕ := by
  classical
  by_cases hxs : x = s
  · exact 0
  · exact Classical.choose
      (eventually_streamAbsenceCount_gt
        (falseCenter_omission_indices_infinite hxs hP) k)

private theorem competitorThreshold_spec
    {k s x : ℕ} {stream : ℕ → Edge ℕ}
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s))
    (hxs : x ≠ s) :
    ∀ t, competitorThreshold hP x ≤ t →
      k < streamAbsenceCount stream x t := by
  classical
  simpa [competitorThreshold, hxs] using
    (Classical.choose_spec
      (eventually_streamAbsenceCount_gt
        (falseCenter_omission_indices_infinite hxs hP) k))

private theorem earlyCandidates_nonempty
    [DecidableEq α]
    (stream : ℕ → Edge α) (k : ℕ) :
    (seenEndpoints
      (streamPrefix stream (k + 1))).Nonempty := by
  let i : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
  refine ⟨(stream 0).left, ?_⟩
  rw [mem_seenEndpoints_iff]
  exact ⟨i, Or.inl (by simp [streamPrefix, i])⟩

/-- The named absence-count identifier succeeds for every finite corruption
budget.  This exposes the concrete witness used in Theorem 6.6. -/
theorem absenceCountIdentifier_finitely_identifies :
    ∀ k s stream,
      KContrastivelyIdentifiesFrom k absenceCountIdentifier
        coSingletonFamily s stream := by
  classical
  intro k s stream hP
  obtain ⟨Tseen, hTseen⟩ := trueCenter_eventually_seen hP
  let early :=
    seenEndpoints (streamPrefix stream (k + 1))
  have hearly : early.Nonempty :=
    earlyCandidates_nonempty stream k
  let threshold : ℕ → ℕ :=
    competitorThreshold hP
  let thresholds : Finset ℕ :=
    early.image threshold
  have hthresholds : thresholds.Nonempty :=
    hearly.image threshold
  let Tfalse := thresholds.max' hthresholds
  let T := max Tseen Tfalse
  refine ⟨s, rfl, T, ?_⟩
  intro t hT
  have htSeen : Tseen ≤ t :=
    (Nat.le_max_left Tseen Tfalse).trans hT
  have htFalse : Tfalse ≤ t :=
    (Nat.le_max_right Tseen Tfalse).trans hT
  have hsSeen :
      s ∈ seenEndpoints (streamPrefix stream t) :=
    hTseen t htSeen
  have hseen :
      (seenEndpoints (streamPrefix stream t)).Nonempty :=
    ⟨s, hsSeen⟩
  let y :=
    absenceCountIdentifier t (streamPrefix stream t)
  have hySeen :
      y ∈ seenEndpoints (streamPrefix stream t) :=
    absenceCountIdentifier_mem hseen
  have hyLe :
      absenceCount (streamPrefix stream t) y ≤
        absenceCount (streamPrefix stream t) s :=
    absenceCountIdentifier_minimal hseen hsSeen
  have hsLe :
      streamAbsenceCount stream s t ≤ k :=
    trueCenter_streamAbsenceCount_le hP
  have hyLeK :
      streamAbsenceCount stream y t ≤ k := by
    rw [← absenceCount_streamPrefix stream y t]
    rw [← absenceCount_streamPrefix stream s t] at hsLe
    exact hyLe.trans hsLe
  have hyEarly :
      y ∈ early :=
    seen_early_of_streamAbsenceCount_le hySeen hyLeK
  have hyEq : y = s := by
    by_contra hys
    have hthresholdMem :
        threshold y ∈ thresholds :=
      Finset.mem_image.mpr ⟨y, hyEarly, rfl⟩
    have hthresholdLe :
        threshold y ≤ Tfalse :=
      Finset.le_max' thresholds (threshold y) hthresholdMem
    have hyGt :
        k < streamAbsenceCount stream y t :=
      competitorThreshold_spec hP hys t
        (hthresholdLe.trans htFalse)
    omega
  exact hyEq

/-- Theorem 6.6: one budget-independent absence-count identifier recovers
every co-singleton target under every finite contrastive corruption budget.
-/
theorem theorem_6_6 :
    FinitelyCorruptionContrastivelyIdentifiable
      coSingletonFamily :=
  ⟨absenceCountIdentifier, absenceCountIdentifier_finitely_identifies⟩

/-! ## Example 6.7 -/

private def example67Edge (a b : ℕ) (hab : a ≠ b) : Edge ℕ :=
  ⟨a, b, hab⟩

/-- The six-edge prefix displayed in Example 6.7. -/
def example67History : Fin 6 → Edge ℕ
  | ⟨0, _⟩ => example67Edge 3 0 (by omega)
  | ⟨1, _⟩ => example67Edge 3 1 (by omega)
  | ⟨2, _⟩ => example67Edge 0 4 (by omega)
  | ⟨3, _⟩ => example67Edge 3 2 (by omega)
  | ⟨4, _⟩ => example67Edge 3 4 (by omega)
  | ⟨5, _⟩ => example67Edge 3 5 (by omega)

/-- Example 6.7's displayed absence-count vector. -/
theorem example_6_7_absence_counts :
    absenceCount example67History 0 = 4 ∧
    absenceCount example67History 1 = 5 ∧
    absenceCount example67History 2 = 5 ∧
    absenceCount example67History 3 = 1 ∧
    absenceCount example67History 4 = 4 ∧
    absenceCount example67History 5 = 5 := by
  decide

/-- In Example 6.7, the target hole `3` is the unique absence minimizer among
the six observed endpoints. -/
theorem example_6_7_unique_minimizer :
    3 ∈ seenEndpoints example67History ∧
      ∀ x ∈ seenEndpoints example67History,
        x ≠ 3 → absenceCount example67History 3 <
          absenceCount example67History x := by
  decide

end ContrastiveGeneration
end GenLimit
