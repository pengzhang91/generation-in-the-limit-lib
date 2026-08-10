import GenLimit.Paper28_ContrastiveGeneration.GenerationCores
import GenLimit.Angluin.SemanticNecessity

/-!
# Exact characterization of contrastive identification

This file formalizes Lemma 4.6 and the identifier-existence part of
Theorem 4.7 of Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*
(arXiv:2605.06211v1).

The example space is countably infinite and comes with the paper's fixed
enumeration.  Hypotheses are represented by an indexed family; convergence
is extensional, so repeated indices denoting the same support cause no
problem.  Contrastive histories still use the oriented `Edge` carrier from
`Geometry.lean`, but all validity tests use `Crosses`, which is invariant
under reversing an edge.
-/

namespace GenLimit
namespace ContrastiveGeneration

/-- A semantic contrastive identifier maps a finite edge history to a
hypothesis index. -/
abbrev ContrastiveIdentifier (α : Type*) :=
  ∀ t : ℕ, (Fin t → Edge α) → ℕ

/-- Run a contrastive identifier on the first `t` edges of a stream. -/
def contrastiveIdentifierOutput
    (I : ContrastiveIdentifier α) (stream : ℕ → Edge α) (t : ℕ) : ℕ :=
  I t (streamPrefix stream t)

/-- Identification of one indexed target from one contrastive
presentation.  The stable index may differ from the target's given index,
but it must denote the same support. -/
def ContrastivelyIdentifiesFrom
    (I : ContrastiveIdentifier α)
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (stream : ℕ → Edge α) : Prop :=
  ∃ j, F j = F z ∧
    ∃ T, ∀ t, T ≤ t →
      contrastiveIdentifierOutput I stream t = j

/-- Definition 3.4's semantic contrastive-identification property. -/
def ContrastivelyIdentifies
    (I : ContrastiveIdentifier α)
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : ℕ → Edge α,
    IsContrastivePresentation stream (F z) →
      ContrastivelyIdentifiesFrom I F z stream

/-- A countable indexed family is contrastively identifiable. -/
def ContrastivelyIdentifiable
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ I : ContrastiveIdentifier α, ContrastivelyIdentifies I F

/-- The semantic text-identification notion in Theorems 3.6 and 4.7. -/
def TextIdentifiable
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    GenLimit.Angluin.SemanticallyIdentifies M F

/-- Every member has a positive point and a negative point, i.e. is proper
and nontrivial as required throughout Sections 4--6 of the source. -/
def AllProperNontrivial
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ i, (F i).Nonempty ∧ (F i)ᶜ.Nonempty

/-! ## Lemma 4.6: contrastive identification implies text identification -/

theorem exists_enumerated_point_not_seen
    [Infinite α] (enumerate : ℕ → α) (henumerate : Function.Surjective enumerate)
    {t : ℕ} (history : Fin t → α) :
    ∃ n, enumerate n ∉ GenLimit.Generic.sequenceSample history := by
  by_contra h
  push_neg at h
  have hunivSubset :
      (Set.univ : Set α) ⊆
        (↑(GenLimit.Generic.sequenceSample history) : Set α) := by
    intro x _hx
    obtain ⟨n, rfl⟩ := henumerate x
    exact h n
  have hunivFinite : (Set.univ : Set α).Finite :=
    (GenLimit.Generic.sequenceSample history).finite_toSet.subset hunivSubset
  exact Set.infinite_univ hunivFinite

/-- Index of the first point in the fixed domain enumeration not yet seen in
a positive-data history. -/
noncomputable def firstUnseenIndex
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {t : ℕ} (history : Fin t → α) : ℕ := by
  classical
  exact
    Nat.find
      (exists_enumerated_point_not_seen enumerate henumerate history)

theorem firstUnseenIndex_spec
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {t : ℕ} (history : Fin t → α) :
    enumerate (firstUnseenIndex enumerate henumerate history) ∉
      GenLimit.Generic.sequenceSample history := by
  classical
  exact
    Nat.find_spec
      (exists_enumerated_point_not_seen enumerate henumerate history)

/-- The simulated contrastive prefix in Lemma 4.6.  Every positive example
is paired with the least domain point absent from the whole current prefix. -/
noncomputable def syntheticContrastiveHistory
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {t : ℕ} (history : Fin t → α) : Fin t → Edge α :=
  fun i =>
    ⟨history i,
      enumerate (firstUnseenIndex enumerate henumerate history),
      by
        intro heq
        have hi :
            history i ∈ GenLimit.Generic.sequenceSample history :=
          GenLimit.Generic.mem_sequenceSample_iff.mpr ⟨i, rfl⟩
        have hnot :=
          firstUnseenIndex_spec enumerate henumerate history
        exact hnot (heq ▸ hi)⟩

/-- The text identifier obtained by simulating the contrastive identifier on
the paper's least-unseen synthetic pairs. -/
noncomputable def textIdentifierOfContrastive
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    (I : ContrastiveIdentifier α) :
    GenLimit.Angluin.SemanticIdentifier α :=
  fun _t history =>
    I _ (syntheticContrastiveHistory enumerate henumerate history)

theorem firstUnseenIndex_eventually_eq_first_complement
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {L : Set α} (k : ℕ)
    (hknot : enumerate k ∉ L)
    (hkmin : ∀ n, n < k → enumerate n ∈ L)
    {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream L) :
    ∃ T, ∀ t, T ≤ t →
      firstUnseenIndex enumerate henumerate
        (fun i : Fin t => stream i) = k := by
  classical
  let lower : Finset α := (Finset.range k).image enumerate
  have hlowerL : (↑lower : Set α) ⊆ L := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hnk : n < k := Finset.mem_range.mp hn
    exact hkmin n hnk
  obtain ⟨T, hT⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hP lower hlowerL
  refine ⟨T, ?_⟩
  intro t ht
  have hlowerSample :
      lower ⊆ GenLimit.Generic.sample stream t :=
    hT.trans (GenLimit.Generic.sample_mono ht)
  have hkUnseen :
      enumerate k ∉
        GenLimit.Generic.sequenceSample
          (fun i : Fin t => stream i) := by
    rw [GenLimit.Generic.sequenceSample_prefix]
    intro hk
    exact hknot
      (GenLimit.Generic.mem_language_of_mem_sample_of_presents hP hk)
  have hfirstLe :
      firstUnseenIndex enumerate henumerate
          (fun i : Fin t => stream i) ≤ k :=
    Nat.find_min'
      (exists_enumerated_point_not_seen enumerate henumerate
        (fun i : Fin t => stream i))
      hkUnseen
  have hkLe :
      k ≤ firstUnseenIndex enumerate henumerate
          (fun i : Fin t => stream i) := by
    by_contra hnot
    have hlt :
        firstUnseenIndex enumerate henumerate
            (fun i : Fin t => stream i) < k :=
      Nat.lt_of_not_ge hnot
    have hmemLower :
        enumerate
            (firstUnseenIndex enumerate henumerate
              (fun i : Fin t => stream i)) ∈ lower := by
      exact Finset.mem_image.mpr
        ⟨_, Finset.mem_range.mpr hlt, rfl⟩
    have hmemSample :=
      hlowerSample hmemLower
    have hmemSequence :
        enumerate
            (firstUnseenIndex enumerate henumerate
              (fun i : Fin t => stream i)) ∈
          GenLimit.Generic.sequenceSample
            (fun i : Fin t => stream i) := by
      simpa [GenLimit.Generic.sequenceSample_prefix] using hmemSample
    exact
      (firstUnseenIndex_spec enumerate henumerate
        (fun i : Fin t => stream i)) hmemSequence
  exact Nat.le_antisymm hfirstLe hkLe

theorem syntheticContrastiveHistory_eq_fixed
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {stream : GenLimit.Generic.Stream α} {t k : ℕ}
    (hk :
      firstUnseenIndex enumerate henumerate
        (fun i : Fin t => stream i) = k)
    (hne : ∀ i : Fin t, stream i ≠ enumerate k) :
    syntheticContrastiveHistory enumerate henumerate
        (fun i : Fin t => stream i) =
      fun i : Fin t => (⟨stream i, enumerate k, hne i⟩ : Edge α) := by
  funext i
  simp [syntheticContrastiveHistory, hk]

/-- Lemma 4.6, inclusion direction.  The strictness example is separate from
the characterization and is not needed by Theorem 4.7. -/
theorem lemma_4_6_inclusion
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F → TextIdentifiable F := by
  classical
  intro hCtr
  obtain ⟨I, hI⟩ := hCtr
  obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat α
  refine ⟨textIdentifierOfContrastive enumerate henumerate I, ?_⟩
  intro z stream hP
  let hex : ∃ n, enumerate n ∉ F z := by
    obtain ⟨x, hx⟩ := (hproper z).2
    obtain ⟨n, rfl⟩ := henumerate x
    exact ⟨n, hx⟩
  let k := Nat.find hex
  have hknot : enumerate k ∉ F z := Nat.find_spec hex
  have hstreamMem : ∀ n, stream n ∈ F z := by
    intro n
    rw [← hP]
    exact ⟨n, rfl⟩
  let cstream : ℕ → Edge α :=
    fun n =>
      ⟨stream n, enumerate k,
        fun heq => hknot (heq ▸ hstreamMem n)⟩
  have hcstream :
      IsContrastivePresentation cstream (F z) := by
    constructor
    · intro n
      exact Or.inl ⟨hstreamMem n, hknot⟩
    · intro x hx
      rw [← hP] at hx
      obtain ⟨n, rfl⟩ := hx
      exact ⟨n, Or.inl rfl⟩
  obtain ⟨j, hj, TI, hTI⟩ := hI z cstream hcstream
  obtain ⟨TS, hTS⟩ :=
    firstUnseenIndex_eventually_eq_first_complement
      enumerate henumerate k hknot
      (fun n hn => by
        by_contra hnmem
        exact Nat.find_min hex hn hnmem)
      hP
  refine ⟨j, hj, max TI TS, ?_⟩
  intro t ht
  have htI : TI ≤ t :=
    le_trans (Nat.le_max_left _ _) ht
  have htS : TS ≤ t :=
    le_trans (Nat.le_max_right _ _) ht
  have hk :
      firstUnseenIndex enumerate henumerate
        (fun i : Fin t => stream i) = k := by
    simpa [hex, k] using hTS t htS
  have hne : ∀ i : Fin t, stream i ≠ enumerate k := by
    intro i heq
    exact hknot (heq ▸ hstreamMem i)
  have hh :=
    syntheticContrastiveHistory_eq_fixed
      enumerate henumerate hk hne
  change
    I t
        (syntheticContrastiveHistory enumerate henumerate
          (fun i : Fin t => stream i)) = j
  rw [hh]
  exact hTI t htI

/-! ## Necessity of the non-eliminability containment -/

theorem commonPresentation_for_noncontained
    {h g : Set α}
    (hcover : h ⊆ commonVertices h g)
    (hnsub : ¬h ⊆ g) :
    g ⊆ commonVertices h g := by
  have hregions := (theorem_4_3 h g).1 hcover
  have hB : (hOnly h g).Nonempty := by
    exact Set.not_subset.mp hnsub
  have hC : (gOnly h g).Nonempty :=
    hregions.2 hB
  have hAtoD :
      (bothPositive g h).Nonempty →
        (bothNegative g h).Nonempty := by
    intro hA
    have hA' : (bothPositive h g).Nonempty := by
      simpa [bothPositive, Set.inter_comm] using hA
    simpa [bothNegative, Set.union_comm] using hregions.1 hA'
  have hCtoB :
      (hOnly g h).Nonempty →
        (gOnly g h).Nonempty := by
    intro _hC'
    simpa [gOnly, hOnly] using hB
  have hgcover' :
      g ⊆ commonVertices g h :=
    (theorem_4_3 g h).2 ⟨hAtoD, hCtoB⟩
  intro x hx
  obtain ⟨e, he, hinc⟩ := hgcover' hx
  exact ⟨e, ⟨he.2, he.1⟩, hinc⟩

theorem contrastiveIdentifiable_nonEliminabilityContained
    [Nonempty α] [Countable α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F)
    (hCtr : ContrastivelyIdentifiable F) :
    NonEliminabilityContained (Set.range F) := by
  classical
  obtain ⟨I, hI⟩ := hCtr
  obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat α
  intro h hh g hg hcover
  by_contra hnsub
  have hgcover :
      g ⊆ commonVertices h g :=
    commonPresentation_for_noncontained hcover hnsub
  have hunion :
      h ∪ g ⊆ commonVertices h g := by
    intro x hx
    rcases hx with hx | hx
    · exact hcover hx
    · exact hgcover hx
  obtain ⟨ih, rfl⟩ := hh
  obtain ⟨ig, rfl⟩ := hg
  let x₀ := Classical.choose (hproper ih).1
  have hx₀ : x₀ ∈ F ih ∪ F ig :=
    Or.inl (Classical.choose_spec (hproper ih).1)
  have henum :
      F ih ∪ F ig ⊆ Set.range enumerate := by
    intro x _hx
    exact henumerate x
  obtain ⟨stream, hhstream, hgstream⟩ :=
    (lemma_4_4 x₀ hx₀ enumerate henum).2 hunion
  obtain ⟨jh, hjh, Th, hTh⟩ :=
    hI ih stream hhstream
  obtain ⟨jg, hjg, Tg, hTg⟩ :=
    hI ig stream hgstream
  have houtEq :
      contrastiveIdentifierOutput I stream (max Th Tg) = jh :=
    hTh _ (Nat.le_max_left _ _)
  have houtEq' :
      contrastiveIdentifierOutput I stream (max Th Tg) = jg :=
    hTg _ (Nat.le_max_right _ _)
  have hj : jh = jg := houtEq.symm.trans houtEq'
  have hfg : F ih = F ig := by
    calc
      F ih = F jh := hjh.symm
      _ = F jg := congrArg F hj
      _ = F ig := hjg
  exact hnsub (fun _ hx => hfg ▸ hx)

/-! ## The least-eligible contrastive learner -/

/-- One fixed choice of an Angluin tell-tale for every indexed support. -/
noncomputable def chosenTellTale
    {F : GenLimit.Generic.LanguageFamily α}
    (hTell : GenLimit.Angluin.ConditionTwo F) (i : ℕ) : Finset α :=
  Classical.choose (hTell i)

theorem chosenTellTale_spec
    {F : GenLimit.Generic.LanguageFamily α}
    (hTell : GenLimit.Angluin.ConditionTwo F) (i : ℕ) :
    GenLimit.Angluin.IsTellTale F i (chosenTellTale hTell i) :=
  Classical.choose_spec (hTell i)

/-- The eligibility test in the proof of Theorem 4.7: the index is within
the finite search range, its tell-tale vertices have appeared, and it is
consistent with every observed XOR pair. -/
def ContrastiveEligible
    (F : GenLimit.Generic.LanguageFamily α)
    (T : ℕ → Finset α)
    {t : ℕ} (history : Fin t → Edge α) (i : ℕ) : Prop :=
  i ≤ t ∧
    (↑(T i) : Set α) ⊆ seenPrefix history ∧
    ∀ r, Crosses (F i) (history r)

/-- The information-theoretic least-eligible learner in Theorem 4.7. -/
noncomputable def contrastiveTellTaleLearner
    (F : GenLimit.Generic.LanguageFamily α)
    (T : ℕ → Finset α) :
    ContrastiveIdentifier α := by
  classical
  exact fun t history =>
    if h : ∃ i, ContrastiveEligible F T history i then
      Nat.find h
    else
      0

theorem contrastiveTellTaleLearner_eligible
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {t : ℕ} {history : Fin t → Edge α}
    (h : ∃ i, ContrastiveEligible F T history i) :
    ContrastiveEligible F T history
      (contrastiveTellTaleLearner F T t history) := by
  classical
  rw [contrastiveTellTaleLearner, dif_pos h]
  exact Nat.find_spec h

theorem contrastiveTellTaleLearner_le_of_eligible
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {t i : ℕ} {history : Fin t → Edge α}
    (hi : ContrastiveEligible F T history i) :
    contrastiveTellTaleLearner F T t history ≤ i := by
  classical
  let h : ∃ j, ContrastiveEligible F T history j := ⟨i, hi⟩
  rw [contrastiveTellTaleLearner, dif_pos h]
  exact Nat.find_min' h hi

theorem finite_vertices_eventually_seen
    {stream : ℕ → Edge α} {h : Set α}
    (hstream : IsContrastivePresentation stream h)
    (S : Finset α) (hS : (↑S : Set α) ⊆ h) :
    ∃ T, ∀ t, T ≤ t →
      (↑S : Set α) ⊆ seenPrefix (streamPrefix stream t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x S hx ih =>
      have hxH : x ∈ h := hS (by simp)
      have hSH : (↑S : Set α) ⊆ h := by
        intro y hy
        exact hS (by simp [hy])
      obtain ⟨n, hn⟩ := hstream.2 hxH
      obtain ⟨TS, hTS⟩ := ih hSH
      refine ⟨max (n + 1) TS, ?_⟩
      intro t ht y hy
      rw [Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hy
      · refine ⟨⟨n, ?_⟩, ?_⟩
        · exact lt_of_lt_of_le (Nat.lt_succ_self n)
            (le_trans (Nat.le_max_left _ _) ht)
        · exact hn
      · exact hTS t
          (le_trans (Nat.le_max_right _ _) ht) hy

theorem eventually_target_contrastiveEligible
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {z : ℕ} {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream (F z))
    (hT : (↑(T z) : Set α) ⊆ F z) :
    ∃ N, ∀ t, N ≤ t →
      ContrastiveEligible F T (streamPrefix stream t) z := by
  obtain ⟨NS, hNS⟩ :=
    finite_vertices_eventually_seen hstream (T z) hT
  refine ⟨max z NS, ?_⟩
  intro t ht
  constructor
  · exact le_trans (Nat.le_max_left _ _) ht
  constructor
  · exact hNS t (le_trans (Nat.le_max_right _ _) ht)
  · intro r
    exact hstream.1 r

theorem incident_member_of_target_of_candidate_consistency
    {h g : Set α} (hsub : h ⊆ g)
    {e : Edge α} (hh : Crosses h e) (hg : Crosses g e)
    {x : α} (hxg : x ∈ g) (hxinc : Incident x e) :
    x ∈ h := by
  rcases hxinc with rfl | rfl
  · by_contra hx
    have hyr : e.right ∈ h :=
      right_mem_of_left_not_mem_of_crosses hx hh
    have hyrg : e.right ∈ g := hsub hyr
    exact (right_not_mem_of_left_mem_of_crosses hxg hg) hyrg
  · by_contra hx
    have hyl : e.left ∈ h :=
      left_mem_of_right_not_mem_of_crosses hx hh
    have hylg : e.left ∈ g := hsub hyl
    exact (left_not_mem_of_right_mem_of_crosses hxg hg) hylg

theorem eligible_candidate_eq_of_target_subset
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {z i t : ℕ} {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream (F z))
    (hTell : GenLimit.Angluin.IsTellTale F i (T i))
    (hsub : F z ⊆ F i)
    (heligible :
      ContrastiveEligible F T (streamPrefix stream t) i) :
    F i = F z := by
  have hTz : (↑(T i) : Set α) ⊆ F z := by
    intro x hx
    have hxFi : x ∈ F i := hTell.1 hx
    obtain ⟨r, hr⟩ := heligible.2.1 hx
    exact incident_member_of_target_of_candidate_consistency
      hsub (hstream.1 r) (heligible.2.2 r) hxFi hr
  exact (hTell.eq_of_between hTz hsub).symm

theorem eventually_not_eligible_of_target_not_subset
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {z i : ℕ} {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream (F z))
    (hrel : NonEliminabilityContained (Set.range F))
    (hnsub : ¬F z ⊆ F i) :
    ∃ N, ∀ t, N ≤ t →
      ¬ContrastiveEligible F T (streamPrefix stream t) i := by
  have hbad : ∃ n, ¬Crosses (F i) (stream n) := by
    by_contra h
    push_neg at h
    have hcover : F z ⊆ commonVertices (F z) (F i) := by
      intro x hx
      obtain ⟨n, hn⟩ := hstream.2 hx
      exact ⟨stream n, ⟨hstream.1 n, h n⟩, hn⟩
    exact hnsub
      (hrel (F z) ⟨z, rfl⟩ (F i) ⟨i, rfl⟩ hcover)
  obtain ⟨n, hn⟩ := hbad
  refine ⟨n + 1, ?_⟩
  intro t ht heligible
  let r : Fin t :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) ht⟩
  exact hn (heligible.2.2 r)

theorem eventually_not_eligible_of_different_language
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {z i : ℕ} {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream (F z))
    (hrel : NonEliminabilityContained (Set.range F))
    (hTell : GenLimit.Angluin.IsTellTale F i (T i))
    (hdiff : F i ≠ F z) :
    ∃ N, ∀ t, N ≤ t →
      ¬ContrastiveEligible F T (streamPrefix stream t) i := by
  by_cases hsub : F z ⊆ F i
  · refine ⟨0, ?_⟩
    intro t _ht heligible
    exact hdiff
      (eligible_candidate_eq_of_target_subset
        hstream hTell hsub heligible)
  · exact eventually_not_eligible_of_target_not_subset
      hstream hrel hsub

theorem contrastiveTellTaleLearner_identifies
    {F : GenLimit.Generic.LanguageFamily α}
    (hTell : GenLimit.Angluin.ConditionTwo F)
    (hrel : NonEliminabilityContained (Set.range F)) :
    ContrastivelyIdentifies
      (contrastiveTellTaleLearner F (chosenTellTale hTell)) F := by
  classical
  intro z stream hstream
  let hex : ∃ i, F i = F z := ⟨z, rfl⟩
  let k := Nat.find hex
  have hk : F k = F z := Nat.find_spec hex
  have hbelow : ∀ i, i < k → F i ≠ F z := by
    intro i hi
    exact Nat.find_min hex hi
  have hkTell :
      GenLimit.Angluin.IsTellTale F k
        (chosenTellTale hTell k) :=
    chosenTellTale_spec hTell k
  obtain ⟨Neligible, hEligible⟩ :=
    eventually_target_contrastiveEligible
      (z := k)
      (stream := stream)
      (by simpa [hk] using hstream)
      hkTell.1
  have hpointwise : ∀ i, i < k → ∃ N, ∀ t, N ≤ t →
      ¬ContrastiveEligible F (chosenTellTale hTell)
        (streamPrefix stream t) i := by
    intro i hi
    exact eventually_not_eligible_of_different_language
      hstream hrel (chosenTellTale_spec hTell i) (hbelow i hi)
  obtain ⟨Nlower, hLower⟩ :=
    GenLimit.Angluin.eventually_all_lt hpointwise
  refine ⟨k, hk, max Neligible Nlower, ?_⟩
  intro t ht
  have htEligible : Neligible ≤ t :=
    le_trans (Nat.le_max_left _ _) ht
  have htLower : Nlower ≤ t :=
    le_trans (Nat.le_max_right _ _) ht
  have hkEligible :
      ContrastiveEligible F (chosenTellTale hTell)
        (streamPrefix stream t) k :=
    hEligible t htEligible
  have hexists :
      ∃ i, ContrastiveEligible F (chosenTellTale hTell)
        (streamPrefix stream t) i :=
    ⟨k, hkEligible⟩
  let j :=
    contrastiveTellTaleLearner F (chosenTellTale hTell) t
      (streamPrefix stream t)
  have hjEligible :
      ContrastiveEligible F (chosenTellTale hTell)
        (streamPrefix stream t) j :=
    contrastiveTellTaleLearner_eligible hexists
  have hjle : j ≤ k :=
    contrastiveTellTaleLearner_le_of_eligible hkEligible
  have hjnotlt : ¬j < k := by
    intro hjlt
    exact hLower t htLower j hjlt hjEligible
  exact Nat.le_antisymm hjle (Nat.not_lt.mp hjnotlt)

theorem contrastivelyIdentifiable_of_text_and_nonEliminability
    [Nonempty α] [Countable α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hText : TextIdentifiable F)
    (hrel : NonEliminabilityContained (Set.range F)) :
    ContrastivelyIdentifiable F := by
  have hTell : GenLimit.Angluin.ConditionTwo F := by
    exact
      GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable F hText
  exact
    ⟨contrastiveTellTaleLearner F (chosenTellTale hTell),
      contrastiveTellTaleLearner_identifies hTell hrel⟩

/-- Theorem 4.7, conditions (i) and (ii), including actual existence of the
contrastive identifier. -/
theorem theorem_4_7_identifier_equivalence
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧
        NonEliminabilityContained (Set.range F) := by
  constructor
  · intro hCtr
    exact
      ⟨lemma_4_6_inclusion F hproper hCtr,
        contrastiveIdentifiable_nonEliminabilityContained
          F hproper hCtr⟩
  · rintro ⟨hText, hrel⟩
    exact contrastivelyIdentifiable_of_text_and_nonEliminability
      F hText hrel

/-- Theorem 4.7, conditions (i) and (iii).  Together with
`theorem_4_7_identifier_equivalence` and
`theorem_4_7_geometric_equivalence`, this is the source's complete
three-way characterization. -/
theorem theorem_4_7
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧
        IncomparablePairsOverlap (Set.range F) := by
  rw [theorem_4_7_identifier_equivalence F hproper]
  constructor
  · rintro ⟨hText, hrel⟩
    exact ⟨hText,
      nonEliminabilityContained_implies_overlap hrel⟩
  · rintro ⟨hText, hoverlap⟩
    exact ⟨hText,
      incomparableOverlap_implies_nonEliminabilityContained hoverlap⟩

end ContrastiveGeneration
end GenLimit
