import GenLimit.Paper14_ListLanguageIdentification.Necessity
import Mathlib.Data.Fin.SuccPred

/-!
# The general list-identification lower bound

Source: Charikar--Pabbaraju--Tewari,
*A Characterization of List Language Identification in the Limit*,
arXiv:2511.04103v1, Section 6 (Theorem 7).

The source proves necessity using a bounded-depth adaptive enumeration.  The
formal proof below packages the same finite-injury idea as an induction on
the list width.  A behavioral lock for the current target permanently
occupies one output slot on every smaller consistent target.  Removing that
slot yields a `(k - 1)`-list identifier on the strict sublanguage cone; the
locking history is accumulated into the next finite witness.

Accumulating the history is important: it is the formal counterpart of the
source adversary never deleting examples when it descends to a smaller
language.  It also makes the induction work for finite as well as infinite
nonempty languages.
-/

namespace GenLimit.ListIdentification

open GenLimit.Generic
open GenLimit.Angluin

/-- Identification restricted to an active set of family indices. -/
def IdentifiesOnIndices
    (A : ListIdentifier α k)
    (F : GenLimit.Generic.LanguageFamily α)
    (I : Set ℕ) : Prop :=
  ∀ i, i ∈ I →
    ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i) →
        IdentifiesFrom A F i stream

/-- The active cone accumulated by the lower-bound induction: languages
containing the finite history and strictly below the current upper target. -/
def strictLanguageCone
    (F : GenLimit.Generic.LanguageFamily α)
    (base : Finset α)
    (upper : GenLimit.Generic.Language α) : Set ℕ :=
  {i | (↑base : Set α) ⊆ F i ∧ F i ⊂ upper}

/-- Choose one slot whose denoted language is the locked target. -/
noncomputable def removableTargetSlot
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (μ : Fin (k + 1) → ℕ) : Fin (k + 1) := by
  classical
  exact
    if h : TargetInGuess F z μ then
      Classical.choose h
    else
      0

theorem removableTargetSlot_spec
    {F : GenLimit.Generic.LanguageFamily α}
    {z : ℕ} {μ : Fin (k + 1) → ℕ}
    (h : TargetInGuess F z μ) :
    F (μ (removableTargetSlot F z μ)) = F z := by
  classical
  rw [removableTargetSlot, dif_pos h]
  exact Classical.choose_spec h

/-- Delete one target-denoting slot from a `(k + 1)`-slot output. -/
noncomputable def dropTargetGuess
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (μ : Fin (k + 1) → ℕ) : Fin k → ℕ :=
  fun r => μ ((removableTargetSlot F z μ).succAbove r)

/-- Deleting one occurrence of the locked target preserves every guessed
language that is extensionally different from that target. -/
theorem targetInGuess_dropTargetGuess
    {F : GenLimit.Generic.LanguageFamily α}
    {z j : ℕ} {μ : Fin (k + 1) → ℕ}
    (hz : TargetInGuess F z μ)
    (hj : TargetInGuess F j μ)
    (hneq : F j ≠ F z) :
    TargetInGuess F j (dropTargetGuess F z μ) := by
  classical
  obtain ⟨rj, hrj⟩ := hj
  have hslot :
      F (μ (removableTargetSlot F z μ)) = F z :=
    removableTargetSlot_spec hz
  have hrjne :
      rj ≠ removableTargetSlot F z μ := by
    intro hr
    apply hneq
    exact hrj.symm.trans (by simpa [hr] using hslot)
  obtain ⟨r, hr⟩ :=
    Fin.exists_succAbove_eq hrjne
  exact ⟨r, by simp [dropTargetGuess, hr, hrj]⟩

/-- Feed a locked prefix to the old identifier and remove one output slot
denoting the locked target. -/
noncomputable def reducedAfterTargetLock
    (A : ListIdentifier α (k + 1))
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (xs : List α) :
    ListIdentifier α k :=
  fun _ ys =>
    dropTargetGuess F z
      (listIdentifierOnHistory A (xs ++ List.ofFn ys))

/-- On a strict subtarget containing the lock, the reduced identifier still
eventually contains that subtarget. -/
theorem reducedAfterTargetLock_identifies_strict_subtarget
    {A : ListIdentifier α (k + 1)}
    {F : GenLimit.Generic.LanguageFamily α}
    {z j : ℕ} {xs : List α}
    (hlock : IsTargetLockingSequence A F z xs)
    (hAj : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F j) →
        IdentifiesFrom A F j stream)
    (hxsJ : ListWithin xs (F j))
    (hproper : F j ⊂ F z) :
    ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F j) →
        IdentifiesFrom (reducedAfterTargetLock A F z xs) F j stream := by
  classical
  intro stream hP
  let combined := prependStream xs stream
  have hcombinedP :
      GenLimit.Generic.Presents combined (F j) :=
    prependStream_presents hxsJ hP
  obtain ⟨N, hN⟩ := hAj combined hcombinedP
  refine ⟨N, ?_⟩
  intro t ht
  have htailJ :
      ListWithin (GenLimit.textPrefix stream t) (F j) :=
    streamPrefix_listWithin
      (GenLimit.Generic.streamIn_of_presents hP) t
  have htailZ :
      ListWithin (GenLimit.textPrefix stream t) (F z) := by
    intro x hx
    exact hproper.1 (htailJ x hx)
  have hzGuess :
      TargetInGuess F z
        (listIdentifierOnHistory A
          (xs ++ GenLimit.textPrefix stream t)) :=
    hlock.2 _ htailZ
  have hprefix :
      GenLimit.textPrefix combined (xs.length + t) =
        xs ++ GenLimit.textPrefix stream t :=
    streamPrefix_prependStream xs stream t
  have hjGuess :
      TargetInGuess F j
        (listIdentifierOnHistory A
          (xs ++ GenLimit.textPrefix stream t)) := by
    rw [← hprefix]
    rw [listIdentifierOnHistory_streamPrefix]
    exact hN _ (ht.trans (Nat.le_add_left t xs.length))
  have hneq : F j ≠ F z := by
    intro heq
    exact hproper.2 (by simp [heq])
  have hdropped :=
    targetInGuess_dropTargetGuess hzGuess hjGuess hneq
  rw [GenLimit.textPrefix_eq_ofFn] at hdropped
  simpa [reducedAfterTargetLock, listOutput] using hdropped

/-- One adaptive step of the bounded-depth necessity argument.  After a
locking history is accumulated into the finite base and the upper language
descends to the locked target, deleting the locked output slot preserves
identification throughout the resulting strict inner cone. -/
theorem reducedAfterTargetLock_identifies_innerCone
    [DecidableEq α]
    {A : ListIdentifier α (k + 1)}
    {F : GenLimit.Generic.LanguageFamily α}
    {base : Finset α}
    {upper : GenLimit.Generic.Language α}
    {i : ℕ} {xs : List α}
    (hlock : IsTargetLockingSequence A F i xs)
    (hA : IdentifiesOnIndices A F
      (strictLanguageCone F base upper))
    (hi : i ∈ strictLanguageCone F base upper) :
    IdentifiesOnIndices (reducedAfterTargetLock A F i xs) F
      (strictLanguageCone F (base ∪ xs.toFinset) (F i)) := by
  intro ell hell stream hP
  have hellOld :
      ell ∈ strictLanguageCone F base upper := by
    constructor
    · intro x hxBase
      apply hell.1
      exact Finset.mem_union_left xs.toFinset hxBase
    · exact hell.2.trans hi.2
  have hxsEll : ListWithin xs (F ell) := by
    intro x hx
    apply hell.1
    exact Finset.mem_union_right base
      (List.mem_toFinset.mpr hx)
  exact
    reducedAfterTargetLock_identifies_strict_subtarget
      hlock (hA ell hellOld) hxsEll hell.2 stream hP

/-- Inductive lower bound on an accumulated strict cone.  This is the
bounded-depth core of Theorem 7. -/
theorem psi_of_identifiesOn_strictLanguageCone
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i)) :
    ∀ k : ℕ, ∀ base : Finset α,
      ∀ upper : GenLimit.Generic.Language α,
      ∀ A : ListIdentifier α k,
        IdentifiesOnIndices A F
          (strictLanguageCone F base upper) →
        ∀ i, i ∈ strictLanguageCone F base upper →
          Psi F i k := by
  intro k
  induction k with
  | zero =>
      intro base upper A hA i hi
      obtain ⟨stream, hP⟩ := hPresentable i
      obtain ⟨N, hN⟩ := hA i hi stream hP
      obtain ⟨r, _hr⟩ := hN N le_rfl
      exact Fin.elim0 r
  | succ k ih =>
      intro base upper A hA i hi
      obtain ⟨presentation, hPresentation⟩ := hPresentable i
      obtain ⟨xs, hlock⟩ :=
        exists_targetLockingSequence_of_identifies
          (hA i hi) hPresentation
      let T : Finset α := base ∪ xs.toFinset
      refine ⟨T, ?_, ?_⟩
      · intro x hx
        change x ∈ T at hx
        simp only [T, Finset.mem_union, List.mem_toFinset] at hx
        rcases hx with hxBase | hxList
        · exact hi.1 hxBase
        · exact hlock.1 x hxList
      · intro j hTj hproper
        let B : ListIdentifier α k :=
          reducedAfterTargetLock A F i xs
        have hB :
            IdentifiesOnIndices B F
              (strictLanguageCone F T (F i)) := by
          simpa [B, T] using
            (reducedAfterTargetLock_identifies_innerCone
              (base := base) (upper := upper) hlock hA hi)
        exact ih T (F i) B hB j ⟨hTj, hproper⟩

/-- Theorem 7 (Lower Bound): list identification implies the `k`-Angluin
condition, assuming the paper's standing hypothesis that every indexed
language has a positive presentation. -/
theorem theorem7_kAngluin_necessity
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i))
    {k : ℕ}
    (h : ListIdentifiable F k) :
    KAngluinCondition F k := by
  obtain ⟨A, hA⟩ := h
  cases k with
  | zero =>
      intro z
      obtain ⟨stream, hP⟩ := hPresentable z
      obtain ⟨N, hN⟩ := hA z stream hP
      obtain ⟨r, _hr⟩ := hN N le_rfl
      exact Fin.elim0 r
  | succ k =>
      intro z
      obtain ⟨presentation, hPresentation⟩ := hPresentable z
      obtain ⟨xs, hlock⟩ :=
        exists_targetLockingSequence_of_identifies
          (hA z) hPresentation
      refine ⟨xs.toFinset, ?_, ?_⟩
      · intro x hx
        exact hlock.1 x (List.mem_toFinset.mp hx)
      · intro j hxsJ hproper
        let B : ListIdentifier α k :=
          reducedAfterTargetLock A F z xs
        have hB :
            IdentifiesOnIndices B F
              (strictLanguageCone F xs.toFinset (F z)) := by
          intro ell hell stream hP
          have hxsEll : ListWithin xs (F ell) := by
            intro x hx
            exact hell.1 (List.mem_toFinset.mpr hx)
          exact
            reducedAfterTargetLock_identifies_strict_subtarget
              hlock (hA ell) hxsEll hell.2 stream hP
        exact
          psi_of_identifiesOn_strictLanguageCone hPresentable
            k xs.toFinset (F z) B hB j ⟨hxsJ, hproper⟩

/-- Theorem 7 on the paper's canonical countable universe. -/
theorem theorem7_kAngluin_necessity_nat
    {F : GenLimit.Generic.LanguageFamily ℕ}
    (hNonempty : GenLimit.Angluin.AllNonempty F)
    {k : ℕ}
    (h : ListIdentifiable F k) :
    KAngluinCondition F k := by
  apply theorem7_kAngluin_necessity
  · intro i
    exact
      ⟨presentationOfNonempty (F i) (hNonempty i),
        presentationOfNonempty_presents (F i) (hNonempty i)⟩
  · exact h

/-- Main deterministic characterization (Theorems 6 and 7). -/
theorem listIdentifiable_iff_kAngluin
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i))
    (k : ℕ) :
    ListIdentifiable F k ↔ KAngluinCondition F k :=
  ⟨theorem7_kAngluin_necessity hPresentable,
    theorem6_kAngluin_listIdentifiable⟩

/-- Canonical-universe version of the main deterministic characterization. -/
theorem listIdentifiable_iff_kAngluin_nat
    {F : GenLimit.Generic.LanguageFamily ℕ}
    (hNonempty : GenLimit.Angluin.AllNonempty F)
    (k : ℕ) :
    ListIdentifiable F k ↔ KAngluinCondition F k := by
  apply listIdentifiable_iff_kAngluin
  intro i
  exact
    ⟨presentationOfNonempty (F i) (hNonempty i),
      presentationOfNonempty_presents (F i) (hNonempty i)⟩

end GenLimit.ListIdentification
