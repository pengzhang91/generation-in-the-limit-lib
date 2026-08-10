import GenLimit.Paper02_LearningTheory.FiniteConeCover
import Mathlib.Data.List.OfFn

/-!
# A countable union of zero-closure classes need not generate in the limit

This file formalizes Lemma 4.3 of Li--Raman--Tewari,
*Generation through the Lens of Learning Theory*, arXiv:2410.13714v5 /
COLT 2025 (source label `lem:hardgeninlim`).

The paper encodes the construction with prime ratios in the positive
rationals.  We use the isomorphic incidence structure on a tagged countable
type: a shared infinite row of anchors and pairwise disjoint infinite private
tails.  Component zero is the upward cone above all anchors; component
`n + 1` is the upward cone above anchor `n` and private tail `n`.

Given a proposed limit generator, stage `n` extends the current history to a
prefix of a presentation from component `n + 1`, waits until the generator is
correct, and records its fresh output in private tail `n` without revealing
it.  Later stages use disjoint private tails, so every recorded output remains
absent.  The compatible limit history contains every anchor and therefore
belongs to component zero, but the generator outputs a recorded point outside
that target at arbitrarily late stage endpoints.
-/

namespace GenLimit.LiRamanTewari

/-- A tagged version of the prime-ratio incidence structure in Lemma 4.3. -/
abbrev CountableUnionUniverse := ℕ ⊕ (ℕ × ℕ)

def countableUnionAnchor (n : ℕ) : CountableUnionUniverse :=
  Sum.inl n

def countableUnionTail (n : ℕ) : Set CountableUnionUniverse :=
  {x | ∃ k, x = Sum.inr (n, k)}

/-- The common core of component zero is the infinite anchor row.  The core
of component `n + 1` is anchor `n` together with private tail `n`. -/
def countableUnionCore : ℕ → Set CountableUnionUniverse
  | 0 => {x | ∃ n, x = countableUnionAnchor n}
  | n + 1 => {countableUnionAnchor n} ∪ countableUnionTail n

def countableUnionClasses :
    ℕ → GenLimit.Generic.LanguageClass CountableUnionUniverse :=
  fun n ↦ upwardCone (countableUnionCore n)

def countableUnionHardClass :
    GenLimit.Generic.LanguageClass CountableUnionUniverse :=
  ⋃ n, countableUnionClasses n

theorem countableUnionTail_mem (n k : ℕ) :
    (Sum.inr (n, k) : CountableUnionUniverse) ∈
      countableUnionTail n :=
  ⟨k, rfl⟩

theorem countableUnionAnchor_mem_zero (n : ℕ) :
    countableUnionAnchor n ∈ countableUnionCore 0 :=
  ⟨n, rfl⟩

theorem countableUnionAnchor_mem_succ (n : ℕ) :
    countableUnionAnchor n ∈ countableUnionCore (n + 1) := by
  exact Set.mem_union_left _ (Set.mem_singleton _)

theorem countableUnionTail_mem_succ (n k : ℕ) :
    (Sum.inr (n, k) : CountableUnionUniverse) ∈
      countableUnionCore (n + 1) := by
  exact Set.mem_union_right _ (countableUnionTail_mem n k)

private theorem countableUnionTail_not_mem_otherCore
    {n m : ℕ} (hnm : n ≠ m) {x : CountableUnionUniverse}
    (hx : x ∈ countableUnionTail n) :
    x ∉ countableUnionCore (m + 1) := by
  rintro (hxAnchor | hxTail)
  · obtain ⟨k, rfl⟩ := hx
    simp [countableUnionAnchor] at hxAnchor
  · obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, hl⟩ := hxTail
    simp only [Sum.inr.injEq, Prod.mk.injEq] at hl
    exact hnm hl.1

theorem countableUnionCore_infinite (n : ℕ) :
    (countableUnionCore n).Infinite := by
  cases n with
  | zero =>
      let f : ℕ → CountableUnionUniverse := countableUnionAnchor
      have hf : Function.Injective f := by
        intro a b hab
        exact Sum.inl.inj hab
      exact (Set.infinite_range_of_injective hf).mono (by
        rintro x ⟨k, rfl⟩
        exact countableUnionAnchor_mem_zero k)
  | succ n =>
      let f : ℕ → CountableUnionUniverse := fun k ↦ Sum.inr (n, k)
      have hf : Function.Injective f := by
        intro a b hab
        exact congrArg Prod.snd (Sum.inr.inj hab)
      exact (Set.infinite_range_of_injective hf).mono (by
        rintro x ⟨k, rfl⟩
        exact countableUnionTail_mem_succ n k)

theorem countableUnionClasses_uus (n : ℕ) :
    UUS (countableUnionClasses n) := by
  intro L hL
  exact (countableUnionCore_infinite n).mono hL

theorem countableUnionClasses_closure_dimension_zero (n : ℕ) :
    HasClosureDimension (countableUnionClasses n) 0 :=
  upwardCone_has_closure_dimension_zero (countableUnionCore_infinite n)

private def countableUnionCoreStream (n : ℕ) :
    GenLimit.Generic.Stream CountableUnionUniverse
  | 0 => countableUnionAnchor n
  | k + 1 => Sum.inr (n, k)

private theorem range_countableUnionCoreStream (n : ℕ) :
    Set.range (countableUnionCoreStream n) =
      countableUnionCore (n + 1) := by
  apply Set.Subset.antisymm
  · rintro x ⟨k, rfl⟩
    cases k with
    | zero => exact countableUnionAnchor_mem_succ n
    | succ k => exact countableUnionTail_mem_succ n k
  · intro x hx
    rcases hx with hx | hx
    · have hxEq : x = countableUnionAnchor n :=
        Set.mem_singleton_iff.mp hx
      exact ⟨0, hxEq.symm⟩
    · obtain ⟨k, rfl⟩ := hx
      exact ⟨k + 1, rfl⟩

/-- Prefix a stream by a finite list. -/
private def prependListStream (l : List α)
    (base : GenLimit.Generic.Stream α) : GenLimit.Generic.Stream α :=
  fun k ↦ if h : k < l.length then l.get ⟨k, h⟩
    else base (k - l.length)

private theorem prependListStream_of_lt
    (l : List α) (base : GenLimit.Generic.Stream α)
    {k : ℕ} (hk : k < l.length) :
    prependListStream l base k = l.get ⟨k, hk⟩ := by
  simp [prependListStream, hk]

private theorem prependListStream_add
    (l : List α) (base : GenLimit.Generic.Stream α) (k : ℕ) :
    prependListStream l base (l.length + k) = base k := by
  simp [prependListStream]

private theorem range_prependListStream [DecidableEq α]
    (l : List α) (base : GenLimit.Generic.Stream α) :
    Set.range (prependListStream l base) =
      (↑l.toFinset : Set α) ∪ Set.range base := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨k, rfl⟩
    by_cases hk : k < l.length
    · apply Set.mem_union_left
      change prependListStream l base k ∈ l.toFinset
      rw [List.mem_toFinset]
      rw [prependListStream_of_lt l base hk]
      exact List.get_mem l ⟨k, hk⟩
    · apply Set.mem_union_right
      exact ⟨k - l.length, by simp [prependListStream, hk]⟩
  · intro x hx
    rcases hx with hxList | hxBase
    · change x ∈ l.toFinset at hxList
      rw [List.mem_toFinset] at hxList
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxList
      refine ⟨i, ?_⟩
      simpa [prependListStream, i.isLt] using hi
    · obtain ⟨k, rfl⟩ := hxBase
      exact ⟨l.length + k, prependListStream_add l base k⟩

private def countableUnionStageTarget
    (n : ℕ) (l : List CountableUnionUniverse) :
    GenLimit.Generic.Language CountableUnionUniverse :=
  (↑l.toFinset : Set CountableUnionUniverse) ∪
    countableUnionCore (n + 1)

private def countableUnionStageStream
    (n : ℕ) (l : List CountableUnionUniverse) :
    GenLimit.Generic.Stream CountableUnionUniverse :=
  prependListStream l (countableUnionCoreStream n)

private theorem countableUnionStageStream_presents
    (n : ℕ) (l : List CountableUnionUniverse) :
    GenLimit.Generic.Presents
      (countableUnionStageStream n l)
      (countableUnionStageTarget n l) := by
  classical
  change Set.range
      (prependListStream l (countableUnionCoreStream n)) =
    (↑l.toFinset : Set CountableUnionUniverse) ∪
      countableUnionCore (n + 1)
  rw [range_prependListStream, range_countableUnionCoreStream]

private theorem countableUnionStageTarget_mem_hardClass
    (n : ℕ) (l : List CountableUnionUniverse) :
    countableUnionStageTarget n l ∈ countableUnionHardClass := by
  apply Set.mem_iUnion.mpr
  refine ⟨n + 1, ?_⟩
  exact Set.subset_union_right

private theorem countableUnionStageTarget_infinite
    (n : ℕ) (l : List CountableUnionUniverse) :
    (countableUnionStageTarget n l).Infinite :=
  (countableUnionCore_infinite (n + 1)).mono Set.subset_union_right

private def listInput (l : List α) : Fin l.length → α :=
  fun i ↦ l.get i

private theorem sequenceSample_listInput [DecidableEq α] (l : List α) :
    GenLimit.Generic.sequenceSample (listInput l) = l.toFinset := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sequenceSample_iff, List.mem_toFinset]
  exact List.mem_iff_get.symm

private theorem countableUnionStage_anchor_in_sample
    (n : ℕ) (l : List CountableUnionUniverse) {s : ℕ}
    (hs : l.length + 1 ≤ s) :
    countableUnionAnchor n ∈
      GenLimit.Generic.sample (countableUnionStageStream n l) s := by
  apply GenLimit.Generic.mem_sample_iff.mpr
  refine ⟨l.length, ?_, ?_⟩
  · omega
  · simpa [countableUnionStageStream, countableUnionCoreStream] using
      prependListStream_add l (countableUnionCoreStream n) 0

private theorem countableUnionStage_list_subset_sample
    (n : ℕ) (l : List CountableUnionUniverse) {s : ℕ}
    (hls : l.length ≤ s) :
    l.toFinset ⊆
      GenLimit.Generic.sample (countableUnionStageStream n l) s := by
  intro x hx
  rw [List.mem_toFinset] at hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  apply GenLimit.Generic.mem_sample_iff.mpr
  refine ⟨i, i.isLt.trans_le hls, ?_⟩
  simpa [countableUnionStageStream, prependListStream, i.isLt] using hi

/-- A stage endpoint extending `l`, together with the two properties needed
by the diagonal: its generator output is in private tail `n`, and that output
has not been revealed. -/
private def IsCountableUnionStageExtension
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (n : ℕ) (l l' : List CountableUnionUniverse) : Prop :=
  l <+: l' ∧
  l.length < l'.length ∧
  (∀ x, x ∈ l' → x ∈ countableUnionStageTarget n l) ∧
  countableUnionAnchor n ∈ l' ∧
  gen l'.length (listInput l') ∈ countableUnionTail n ∧
  gen l'.length (listInput l') ∉ l'

private theorem exists_countableUnionStageExtension
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n : ℕ) (l : List CountableUnionUniverse) :
    ∃ l', IsCountableUnionStageExtension gen n l l' := by
  classical
  let target := countableUnionStageTarget n l
  let stream := countableUnionStageStream n l
  have hTargetMem : target ∈ countableUnionHardClass :=
    countableUnionStageTarget_mem_hardClass n l
  have hPresentation : GenLimit.Generic.Presents stream target :=
    countableUnionStageStream_presents n l
  obtain ⟨T, hT⟩ := hgen target hTargetMem stream hPresentation
  let s := max T (l.length + 1)
  let l' : List CountableUnionUniverse :=
    List.ofFn (fun i : Fin s ↦ stream i)
  have hlens : l'.length = s := by
    simp only [l', List.length_ofFn]
  have hTs : T ≤ l'.length := by
    rw [hlens]
    exact Nat.le_max_left _ _
  have hlenS : l.length + 1 ≤ l'.length := by
    rw [hlens]
    exact Nat.le_max_right _ _
  have hcorrect :
      GenLimit.Generic.CorrectAt gen target stream l'.length :=
    hT l'.length hTs
  have hprefix : l <+: l' := by
    apply List.prefix_iff_getElem.mpr
    have hlen : l.length ≤ l'.length := by
      simpa [l'] using (show l.length ≤ s by omega)
    refine ⟨hlen, ?_⟩
    · intro k hk
      simp only [l', List.getElem_ofFn]
      rw [show stream k = l.get ⟨k, hk⟩ by
        exact prependListStream_of_lt l _ hk]
      rfl
  have hlength : l.length < l'.length := by
    simp only [l', List.length_ofFn]
    omega
  have hwithin :
      ∀ x, x ∈ l' → x ∈ countableUnionStageTarget n l := by
    intro x hx
    change x ∈ target
    rw [← hPresentation]
    dsimp only [l'] at hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨i, rfl⟩
  have hsample :
      GenLimit.Generic.sample stream l'.length = l'.toFinset := by
    ext x
    rw [GenLimit.Generic.mem_sample_iff]
    rw [List.mem_toFinset]
    rw [hlens]
    change (∃ k < s, stream k = x) ↔ x ∈ l'
    dsimp only [l']
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · intro hx
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, i.isLt, hi⟩
  have houtput :
      GenLimit.Generic.output gen stream l'.length =
        gen l'.length (listInput l') := by
    unfold GenLimit.Generic.output
    congr 1
    funext i
    simp [l', listInput]
  have hanchorList : countableUnionAnchor n ∈ l' := by
    dsimp only [l']
    rw [List.mem_ofFn]
    let i : Fin s := ⟨l.length, by omega⟩
    refine ⟨i, ?_⟩
    change stream l.length = countableUnionAnchor n
    simpa [stream, countableUnionStageStream,
      countableUnionCoreStream] using
      prependListStream_add l (countableUnionCoreStream n) 0
  have hfreshList : gen l'.length (listInput l') ∉ l' := by
    intro hmem
    apply hcorrect.2
    rw [houtput, hsample]
    exact List.mem_toFinset.mpr hmem
  have hvalid :
      gen l'.length (listInput l') ∈
        countableUnionStageTarget n l := by
    simpa only [houtput] using hcorrect.1
  have hnotOld :
      gen l'.length (listInput l') ∉ l.toFinset := by
    intro hmem
    apply hfreshList
    exact hprefix.subset (List.mem_toFinset.mp hmem)
  have hnotAnchor :
      gen l'.length (listInput l') ≠ countableUnionAnchor n := by
    intro hout
    apply hcorrect.2
    rw [houtput, hout]
    exact countableUnionStage_anchor_in_sample n l hlenS
  have htail :
      gen l'.length (listInput l') ∈ countableUnionTail n := by
    rcases hvalid with hOld | hCore
    · exact False.elim (hnotOld hOld)
    · rcases hCore with hAnchor | hTail
      · exact False.elim (hnotAnchor (Set.mem_singleton_iff.mp hAnchor))
      · exact hTail
  exact ⟨l', hprefix, hlength, hwithin, hanchorList, htail, hfreshList⟩

private noncomputable def countableUnionStageExtension
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n : ℕ) (l : List CountableUnionUniverse) :
    List CountableUnionUniverse :=
  Classical.choose (exists_countableUnionStageExtension gen hgen n l)

private theorem countableUnionStageExtension_spec
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n : ℕ) (l : List CountableUnionUniverse) :
    IsCountableUnionStageExtension gen n l
      (countableUnionStageExtension gen hgen n l) :=
  Classical.choose_spec (exists_countableUnionStageExtension gen hgen n l)

private noncomputable def countableUnionHistory
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) :
    ℕ → List CountableUnionUniverse
  | 0 => []
  | n + 1 =>
      countableUnionStageExtension gen hgen n
        (countableUnionHistory gen hgen n)

private noncomputable def countableUnionBadOutput
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n : ℕ) : CountableUnionUniverse :=
  let l := countableUnionHistory gen hgen (n + 1)
  gen l.length (listInput l)

private theorem countableUnionHistory_prefix_succ
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) (n : ℕ) :
    countableUnionHistory gen hgen n <+:
      countableUnionHistory gen hgen (n + 1) := by
  rw [countableUnionHistory]
  exact (countableUnionStageExtension_spec gen hgen n _).1

private theorem countableUnionHistory_prefix
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    {n m : ℕ} (hnm : n ≤ m) :
    countableUnionHistory gen hgen n <+:
      countableUnionHistory gen hgen m := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
      exact ih.trans (countableUnionHistory_prefix_succ gen hgen m)

private theorem countableUnionHistory_length
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) (n : ℕ) :
    n ≤ (countableUnionHistory gen hgen n).length := by
  induction n with
  | zero => simp [countableUnionHistory]
  | succ n ih =>
      have hstep :=
        (countableUnionStageExtension_spec gen hgen n
          (countableUnionHistory gen hgen n)).2.1
      rw [countableUnionHistory]
      omega

private theorem countableUnionHistory_next_within
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n : ℕ) {x : CountableUnionUniverse}
    (hx : x ∈ countableUnionHistory gen hgen (n + 1)) :
    x ∈ countableUnionStageTarget n
      (countableUnionHistory gen hgen n) := by
  rw [countableUnionHistory] at hx
  exact
    (countableUnionStageExtension_spec gen hgen n
      (countableUnionHistory gen hgen n)).2.2.1 x hx

private theorem countableUnionBadOutput_mem_tail
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) (n : ℕ) :
    countableUnionBadOutput gen hgen n ∈ countableUnionTail n := by
  exact
    (countableUnionStageExtension_spec gen hgen n
      (countableUnionHistory gen hgen n)).2.2.2.2.1

private theorem countableUnionBadOutput_not_mem_next
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) (n : ℕ) :
    countableUnionBadOutput gen hgen n ∉
      countableUnionHistory gen hgen (n + 1) := by
  exact
    (countableUnionStageExtension_spec gen hgen n
      (countableUnionHistory gen hgen n)).2.2.2.2.2

private theorem countableUnionBadOutput_not_mem_later
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n : ℕ) :
    ∀ m, n + 1 ≤ m →
      countableUnionBadOutput gen hgen n ∉
        countableUnionHistory gen hgen m := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact countableUnionBadOutput_not_mem_next gen hgen n
  | succ m hbase ih =>
      intro hmem
      have htarget :=
        countableUnionHistory_next_within gen hgen m hmem
      rcases htarget with hOld | hCore
      · exact ih (List.mem_toFinset.mp hOld)
      · exact countableUnionTail_not_mem_otherCore
          (by omega)
          (countableUnionBadOutput_mem_tail gen hgen n) hCore

private theorem countableUnionBadOutput_not_mem_history
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n m : ℕ) :
    countableUnionBadOutput gen hgen n ∉
      countableUnionHistory gen hgen m := by
  rcases le_total m (n + 1) with hmn | hnm
  · intro hmem
    exact countableUnionBadOutput_not_mem_next gen hgen n
      ((countableUnionHistory_prefix gen hgen hmn).subset hmem)
  · exact countableUnionBadOutput_not_mem_later gen hgen n m hnm

private noncomputable def countableUnionFinalStream
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) :
    GenLimit.Generic.Stream CountableUnionUniverse :=
  fun k ↦
    let history := countableUnionHistory gen hgen (k + 1)
    history.get ⟨k, by
      have hlen := countableUnionHistory_length gen hgen (k + 1)
      exact lt_of_lt_of_le (Nat.lt_succ_self k) hlen⟩

private theorem countableUnionFinalStream_eq_history_get
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n k : ℕ)
    (hk : k < (countableUnionHistory gen hgen n).length) :
    countableUnionFinalStream gen hgen k =
      (countableUnionHistory gen hgen n).get ⟨k, hk⟩ := by
  rw [countableUnionFinalStream]
  have hbound :
      k < (countableUnionHistory gen hgen (k + 1)).length := by
    have hlen := countableUnionHistory_length gen hgen (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) n with hkn | hnk
  · exact
      (List.prefix_iff_getElem.mp
        (countableUnionHistory_prefix gen hgen hkn)).2 k hbound
  · exact
      ((List.prefix_iff_getElem.mp
        (countableUnionHistory_prefix gen hgen hnk)).2 k hk).symm

private theorem countableUnionHistory_subset_finalRange
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass)
    (n : ℕ) :
    (↑(countableUnionHistory gen hgen n).toFinset :
        Set CountableUnionUniverse) ⊆
      Set.range (countableUnionFinalStream gen hgen) := by
  intro x hx
  change x ∈ (countableUnionHistory gen hgen n).toFinset at hx
  rw [List.mem_toFinset] at hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  refine ⟨i, ?_⟩
  exact (countableUnionFinalStream_eq_history_get
    gen hgen n i i.isLt).trans hi

private theorem countableUnionAnchor_mem_nextHistory
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) (n : ℕ) :
    countableUnionAnchor n ∈
      countableUnionHistory gen hgen (n + 1) := by
  rw [countableUnionHistory]
  exact
    (countableUnionStageExtension_spec gen hgen n
      (countableUnionHistory gen hgen n)).2.2.2.1

private theorem countableUnionFinalLanguage_mem_hardClass
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) :
    Set.range (countableUnionFinalStream gen hgen) ∈
      countableUnionHardClass := by
  apply Set.mem_iUnion.mpr
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact countableUnionHistory_subset_finalRange gen hgen (n + 1)
    (List.mem_toFinset.mpr
      (countableUnionAnchor_mem_nextHistory gen hgen n))

private theorem countableUnionBadOutput_not_mem_finalLanguage
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) (n : ℕ) :
    countableUnionBadOutput gen hgen n ∉
      Set.range (countableUnionFinalStream gen hgen) := by
  rintro ⟨k, hk⟩
  apply countableUnionBadOutput_not_mem_history gen hgen n (k + 1)
  rw [← hk]
  exact List.get_mem _ _

private theorem countableUnionOutput_at_stage
    (gen : GenLimit.Generic.Generator CountableUnionUniverse)
    (hgen : IsLimitGenerator gen countableUnionHardClass) (n : ℕ) :
    GenLimit.Generic.output gen (countableUnionFinalStream gen hgen)
        (countableUnionHistory gen hgen (n + 1)).length =
      countableUnionBadOutput gen hgen n := by
  unfold GenLimit.Generic.output countableUnionBadOutput
  congr 1
  funext i
  exact countableUnionFinalStream_eq_history_get
    gen hgen (n + 1) i i.isLt

theorem countableUnionHardClass_not_generatable_in_limit :
    ¬GeneratableInLimit countableUnionHardClass := by
  rintro ⟨gen, hgen⟩
  let stream := countableUnionFinalStream gen hgen
  let target : GenLimit.Generic.Language CountableUnionUniverse :=
    Set.range stream
  have hTarget : target ∈ countableUnionHardClass :=
    countableUnionFinalLanguage_mem_hardClass gen hgen
  have hPresentation : GenLimit.Generic.Presents stream target := rfl
  obtain ⟨T, hT⟩ := hgen target hTarget stream hPresentation
  let s := (countableUnionHistory gen hgen (T + 1)).length
  have hTs : T ≤ s := by
    exact le_trans (Nat.le_add_right T 1)
      (countableUnionHistory_length gen hgen (T + 1))
  have hcorrect := hT s hTs
  have hbad :
      GenLimit.Generic.output gen stream s ∉ target := by
    change GenLimit.Generic.output gen
      (countableUnionFinalStream gen hgen)
        (countableUnionHistory gen hgen (T + 1)).length ∉
      Set.range (countableUnionFinalStream gen hgen)
    rw [countableUnionOutput_at_stage gen hgen T]
    exact countableUnionBadOutput_not_mem_finalLanguage gen hgen T
  exact hbad hcorrect.1

/-- Lemma 4.3 (`lem:hardgeninlim`): a countable sequence of UUS classes,
each of closure dimension zero, whose union is not generatable in the
limit.  `CountableUnionUniverse` is a concrete countable example space
isomorphic to the prime-ratio incidence structure used in the paper. -/
theorem exists_countable_sequence_zero_closure_union_not_limit :
    ∃ classes :
        ℕ → GenLimit.Generic.LanguageClass CountableUnionUniverse,
      (∀ n, UUS (classes n)) ∧
      (∀ n, HasClosureDimension (classes n) 0) ∧
      ¬GeneratableInLimit (⋃ n, classes n) := by
  exact ⟨countableUnionClasses, countableUnionClasses_uus,
    countableUnionClasses_closure_dimension_zero,
    countableUnionHardClass_not_generatable_in_limit⟩

end GenLimit.LiRamanTewari
