import GenLimit.Paper14_ListLanguageIdentification.Algorithm
import GenLimit.Support.Locking

/-!
# Necessity: locking content and the one-list case

Source: Charikar--Pabbaraju--Tewari,
*A Characterization of List Language Identification in the Limit*,
arXiv:2511.04103v1, Section 6 (Theorem 7).

The full theorem uses the paper's bounded-depth adaptive chain adversary.
This module establishes two reusable pieces of that argument without assuming
the remaining diagonal:

* every successful list identifier has a finite target-locking history; and
* Theorem 7 is complete for list size one.

The target lock is behavioral: every continuation within the target makes the
output list contain an extensionally correct index.  This is the appropriate
notion when repeated copies of a language may occur at different indices.
-/

namespace GenLimit.ListIdentification

open GenLimit.Generic
open GenLimit.Angluin

/-- Run a fixed-width list identifier through Core's ordered finite-history
learner adapter. -/
abbrev listIdentifierOnHistory
    (A : ListIdentifier α k) : GenLimit.Learner α (Fin k → ℕ) :=
  GenLimit.learnerOfFiniteHistory A

theorem listIdentifierOnHistory_streamPrefix
    (A : ListIdentifier α k)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    listIdentifierOnHistory A (GenLimit.textPrefix stream t) =
      listOutput A stream t := by
  simpa [listOutput] using
    (GenLimit.learnerOfFiniteHistory_textPrefix A stream t)

/-- The binary indicator that the current list contains the target language. -/
noncomputable def targetRecognitionBit
    (A : ListIdentifier α k)
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (xs : List α) : ℕ := by
  classical
  exact
    if TargetInGuess F z (listIdentifierOnHistory A xs) then 1 else 0

theorem targetRecognitionBit_eq_one_iff
    {A : ListIdentifier α k}
    {F : GenLimit.Generic.LanguageFamily α}
    {z : ℕ} {xs : List α} :
    targetRecognitionBit A F z xs = 1 ↔
      TargetInGuess F z (listIdentifierOnHistory A xs) := by
  classical
  simp [targetRecognitionBit]

/-- Syntactic convergence for a history function over an arbitrary example
type.  Angluin's `EffectiveConvergesTo` fixes encoded words to `ℕ`; the
locking diagonal itself has no such restriction. -/
abbrev HistoryConvergesTo
    (M : List α → ℕ) (stream : GenLimit.Generic.Stream α)
    (j : ℕ) : Prop :=
  GenLimit.StabilizesTo
    (fun t => M (GenLimit.textPrefix stream t)) j

/-- A behavioral lock for one target: after `xs`, every continuation drawn
from the target makes the output list contain that target. -/
def IsTargetLockingSequence
    (A : ListIdentifier α k)
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (xs : List α) : Prop :=
  ListWithin xs (F z) ∧
    ∀ tail, ListWithin tail (F z) →
      TargetInGuess F z
        (listIdentifierOnHistory A (xs ++ tail))

/-- Identification of one presentable target on all of its presentations
already supplies finite behavioral locking content for that target. -/
theorem exists_targetLockingSequence_of_identifies
    {A : ListIdentifier α k}
    {F : GenLimit.Generic.LanguageFamily α}
    {z : ℕ}
    (hA : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F z) →
        IdentifiesFrom A F z stream)
    {base : GenLimit.Generic.Stream α}
    (hbaseP : GenLimit.Generic.Presents base (F z)) :
    ∃ xs : List α, IsTargetLockingSequence A F z xs := by
  classical
  let M : List α → ℕ := targetRecognitionBit A F z
  have hConverges :
      ∀ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream (F z) →
          ∃ j, HistoryConvergesTo M stream j := by
    intro stream hP
    obtain ⟨T, hT⟩ := hA stream hP
    refine ⟨1, T, ?_⟩
    intro t ht
    rw [targetRecognitionBit_eq_one_iff]
    rw [listIdentifierOnHistory_streamPrefix]
    exact hT t ht
  obtain ⟨xs, j, hlock⟩ :=
    exists_lockingSequence_of_converges_with_base
      hbaseP hConverges
  have hj : j = 1 := by
    let combined := prependStream xs base
    have hcombinedP :
        GenLimit.Generic.Presents combined (F z) :=
      prependStream_presents hlock.1 hbaseP
    obtain ⟨T, hT⟩ := hA combined hcombinedP
    have hbaseIn :
        GenLimit.Generic.StreamIn base (F z) :=
      GenLimit.Generic.streamIn_of_presents hbaseP
    have htailIn :
        ListWithin (GenLimit.textPrefix base T) (F z) :=
      streamPrefix_listWithin hbaseIn T
    have hlocked :
        M (xs ++ GenLimit.textPrefix base T) = j :=
      hlock.2 _ htailIn
    have hprefix :
        GenLimit.textPrefix combined (xs.length + T) =
          xs ++ GenLimit.textPrefix base T :=
      streamPrefix_prependStream xs base T
    have hrecognized :
        M (xs ++ GenLimit.textPrefix base T) = 1 := by
      rw [← hprefix]
      rw [targetRecognitionBit_eq_one_iff]
      rw [listIdentifierOnHistory_streamPrefix]
      exact hT _ (Nat.le_add_left T xs.length)
    exact hlocked.symm.trans hrecognized
  refine ⟨xs, hlock.1, ?_⟩
  intro tail htail
  rw [← targetRecognitionBit_eq_one_iff]
  exact (hlock.2 tail htail).trans hj

/-- Every successful list identifier has finite behavioral locking content
for each presentable target. -/
theorem exists_targetLockingSequence
    {A : ListIdentifier α k}
    {F : GenLimit.Generic.LanguageFamily α}
    (hA : ListIdentifies A F)
    (z : ℕ)
    {base : GenLimit.Generic.Stream α}
    (hbaseP : GenLimit.Generic.Presents base (F z)) :
    ∃ xs : List α, IsTargetLockingSequence A F z xs :=
  exists_targetLockingSequence_of_identifies
    (fun stream hP => hA z stream hP) hbaseP

/-- At list size one, behavioral locking content is an Angluin tell-tale.
This is the base case of the adaptive chain argument in Theorem 7. -/
theorem targetLockingSequence_isTellTale_one
    [DecidableEq α]
    {A : ListIdentifier α 1}
    {F : GenLimit.Generic.LanguageFamily α}
    (hA : ListIdentifies A F)
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i))
    {z : ℕ} {xs : List α}
    (hlock : IsTargetLockingSequence A F z xs) :
    GenLimit.Angluin.IsTellTale F z xs.toFinset := by
  classical
  constructor
  · intro x hx
    exact hlock.1 x (List.mem_toFinset.mp hx)
  · intro j hcontent hjz
    obtain ⟨base, hbaseP⟩ := hPresentable j
    have hxsJ : ListWithin xs (F j) := by
      intro x hx
      exact hcontent (List.mem_toFinset.mpr hx)
    let combined := prependStream xs base
    have hcombinedP :
        GenLimit.Generic.Presents combined (F j) :=
      prependStream_presents hxsJ hbaseP
    obtain ⟨T, hT⟩ := hA j combined hcombinedP
    have hbaseInJ :
        GenLimit.Generic.StreamIn base (F j) :=
      GenLimit.Generic.streamIn_of_presents hbaseP
    have htailInZ :
        ListWithin (GenLimit.textPrefix base T) (F z) := by
      apply streamPrefix_listWithin
      intro x hx
      exact hjz (hbaseInJ hx)
    obtain ⟨rz, hrz⟩ :=
      hlock.2 (GenLimit.textPrefix base T) htailInZ
    have hprefix :
        GenLimit.textPrefix combined (xs.length + T) =
          xs ++ GenLimit.textPrefix base T :=
      streamPrefix_prependStream xs base T
    have hjGuess :
        TargetInGuess F j
          (listIdentifierOnHistory A
            (xs ++ GenLimit.textPrefix base T)) := by
      rw [← hprefix]
      rw [listIdentifierOnHistory_streamPrefix]
      exact hT _ (Nat.le_add_left T xs.length)
    obtain ⟨rj, hrj⟩ := hjGuess
    have hr : rz = rj := Subsingleton.elim _ _
    exact by
      rw [hr, hrj] at hrz
      exact hrz.symm.subset

/-- Theorem 7 for list size one on an arbitrary universe, assuming each
indexed language has an exact positive presentation. -/
theorem theorem7_one_list_necessity
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i))
    (h : ListIdentifiable F 1) :
    KAngluinCondition F 1 := by
  obtain ⟨A, hA⟩ := h
  rw [kAngluin_one_iff_conditionTwo]
  intro z
  obtain ⟨base, hbaseP⟩ := hPresentable z
  obtain ⟨xs, hlock⟩ :=
    exists_targetLockingSequence hA z hbaseP
  exact ⟨xs.toFinset,
    targetLockingSequence_isTellTale_one hA hPresentable hlock⟩

/-- Source-facing specialization: over the canonical countable universe
`ℕ`, nonempty languages are presentable, so one-list identifiability implies
the one-Angluin condition without an extra presentation hypothesis. -/
theorem theorem7_one_list_necessity_nat
    {F : GenLimit.Generic.LanguageFamily ℕ}
    (hNonempty : GenLimit.Angluin.AllNonempty F)
    (h : ListIdentifiable F 1) :
    KAngluinCondition F 1 := by
  apply theorem7_one_list_necessity
  · intro i
    exact
      ⟨presentationOfNonempty (F i) (hNonempty i),
        presentationOfNonempty_presents (F i) (hNonempty i)⟩
  · exact h

/-- The main characterization theorem at list size one, on any universe
where every indexed language has an exact positive presentation. -/
theorem one_list_identifiable_iff_kAngluin
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i)) :
    ListIdentifiable F 1 ↔ KAngluinCondition F 1 := by
  constructor
  · exact theorem7_one_list_necessity hPresentable
  · exact theorem6_kAngluin_listIdentifiable

/-- Canonical-universe version of the complete characterization for one
guess. -/
theorem one_list_identifiable_iff_kAngluin_nat
    {F : GenLimit.Generic.LanguageFamily ℕ}
    (hNonempty : GenLimit.Angluin.AllNonempty F) :
    ListIdentifiable F 1 ↔ KAngluinCondition F 1 := by
  apply one_list_identifiable_iff_kAngluin
  intro i
  exact
    ⟨presentationOfNonempty (F i) (hNonempty i),
      presentationOfNonempty_presents (F i) (hNonempty i)⟩

end GenLimit.ListIdentification
