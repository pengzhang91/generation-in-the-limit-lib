import GenLimit.Angluin.LockingExistence
import Mathlib.Data.Countable.Defs

/-!
# Semantic necessity of Angluin's tell-tale condition

This module proves the domain-generic, semantic necessity direction of
Angluin's finite tell-tale characterization.  It is independent of any later
paper's detector definitions and can therefore be reused by developments
that need identification-to-tell-tale reasoning.

The source describes an enumeration as an infinite sequence all of whose
entries lie in the language.  Consequently an empty language has no legal
enumeration.  The public equivalence below handles that edge case exactly:
identification is vacuous there, and the empty set is a tell-tale.  Nonempty
targets use the usual locking-sequence argument.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

noncomputable local instance semanticNecessityPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## Semantic identification supplies tell-tales -/

/-- Turn the shared finite-function identifier interface into the list
interface used by the locking-sequence development. -/
def listIdentifierOf
    (M : GenLimit.Angluin.SemanticIdentifier α) : List α → ℕ :=
  fun xs => M xs.length xs.get

theorem listIdentifierOf_streamPrefix
    (M : GenLimit.Angluin.SemanticIdentifier α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    listIdentifierOf M (GenLimit.Angluin.streamPrefix stream t) =
      GenLimit.Angluin.identifierOutput M stream t := by
  let f : Fin t → α := fun i => stream i
  have htuple :
      (⟨(List.ofFn f).length, (List.ofFn f).get⟩ :
        Σ n, Fin n → α) = ⟨t, f⟩ := by
    exact List.equivSigmaTuple.apply_symm_apply ⟨t, f⟩
  exact congrArg
    (fun h : Σ n, Fin n → α => M h.1 h.2) htuple

/-- Syntactic convergence for a list identifier over an arbitrary domain. -/
def ListConvergesTo
    (M : List α → ℕ) (stream : GenLimit.Generic.Stream α) (j : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t → M (GenLimit.Angluin.streamPrefix stream t) = j

/-- A fixed surjective domain enumeration yields an exact presentation of
every nonempty language, using one target point as padding. -/
noncomputable def presentationFromDomainEnumeration
    (enumerate : ℕ → α) (L : Set α) (hL : L.Nonempty) :
    GenLimit.Generic.Stream α :=
  fun n => if enumerate n ∈ L then enumerate n else Classical.choose hL

theorem presentationFromDomainEnumeration_presents
    (enumerate : ℕ → α) (henumerate : Function.Surjective enumerate)
    (L : Set α) (hL : L.Nonempty) :
    GenLimit.Generic.Presents
      (presentationFromDomainEnumeration enumerate L hL) L := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    by_cases hn : enumerate n ∈ L
    · simp [presentationFromDomainEnumeration, hn]
    · simpa [presentationFromDomainEnumeration, hn] using
        Classical.choose_spec hL
  · intro x hx
    obtain ⟨n, hn⟩ := henumerate x
    refine ⟨n, ?_⟩
    simp [presentationFromDomainEnumeration, hn, hx]

/-- Generic form of the locking-existence diagonal.  The shared Angluin file
specializes this lemma to natural-number words; here the already formalized
diagonal is reused with an arbitrary supplied presentation. -/
theorem exists_lockingSequence_of_identifies_with_presentation
    {M : List α → ℕ} {L : Set α}
    {base : GenLimit.Generic.Stream α}
    (hbaseP : GenLimit.Generic.Presents base L)
    (hIdentifies : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream L →
        ∃ j, ListConvergesTo M stream j) :
    ∃ xs : List α, ∃ j, GenLimit.Angluin.IsLockingSequence M L xs j := by
  classical
  by_contra hlocks
  push_neg at hlocks
  have hchange : ∀ xs, GenLimit.Angluin.ListWithin xs L →
      GenLimit.Angluin.HasChangeExtension M L xs := by
    intro xs hxs
    exact GenLimit.Angluin.hasChangeExtension_of_not_locking
      hxs (hlocks xs (M xs))
  let hbase := GenLimit.Generic.streamIn_of_presents hbaseP
  let diagonal :=
    GenLimit.Angluin.adversarialStream M L base hbase hchange
  have hdiagonalP : GenLimit.Generic.Presents diagonal L :=
    GenLimit.Angluin.adversarialStream_presents (M := M) hbaseP
  obtain ⟨j, T, hconverges⟩ := hIdentifies diagonal hdiagonalP
  let n := T
  let history :=
    (GenLimit.Angluin.adversarialHistory M L base hbase hchange n).1
  let seeded := history ++ [base n]
  have hseededPrefix :
      GenLimit.Angluin.streamPrefix diagonal seeded.length = seeded := by
    have hseededHist : seeded <+:
        (GenLimit.Angluin.adversarialHistory M L base hbase hchange
          (n + 1)).1 := by
      rw [GenLimit.Angluin.adversarialHistory,
        GenLimit.Angluin.adversarialStep_eq]
      exact List.prefix_append _ _
    exact GenLimit.Angluin.streamPrefix_adversarialStream_of_prefix
      hseededHist
  have hnextPrefix :=
    GenLimit.Angluin.streamPrefix_adversarialStream
      (M := M) (L := L) (base := base) (hbase := hbase)
      (hchange := hchange) (n + 1)
  have hseededLen : T ≤ seeded.length := by
    have hlen := GenLimit.Angluin.adversarialHistory_length
      (M := M) (L := L) (base := base) (hbase := hbase)
      (hchange := hchange) T
    dsimp [seeded, history, n]
    simp only [List.length_append, List.length_singleton]
    omega
  have hnextLen : T ≤
      (GenLimit.Angluin.adversarialHistory M L base hbase hchange
        (n + 1)).1.length := by
    dsimp [n]
    exact le_trans (Nat.le_add_right T 1)
      (GenLimit.Angluin.adversarialHistory_length
        (M := M) (L := L) (base := base) (hbase := hbase)
        (hchange := hchange) (T + 1))
  have hseededGuess : M seeded = j := by
    rw [← hseededPrefix]
    exact hconverges _ hseededLen
  have hnextGuess :
      M (GenLimit.Angluin.adversarialHistory M L base hbase hchange
        (n + 1)).1 = j := by
    rw [← hnextPrefix]
    exact hconverges _ hnextLen
  exact (GenLimit.Angluin.adversarialHistory_mindChange
    (M := M) (L := L) (base := base) (hbase := hbase)
    (hchange := hchange) n) (hnextGuess.trans hseededGuess.symm)

/-- A generic locking sequence obtained for a correctly identified target
must name that target. -/
theorem lockingSequence_correct_with_presentation
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    {z j : ℕ} {xs : List α}
    {base : GenLimit.Generic.Stream α}
    (hbaseP : GenLimit.Generic.Presents base (C z))
    (hIdentifies : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ ell, C ell = C z ∧
          ListConvergesTo M stream ell)
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j) :
    C j = C z := by
  let combined := GenLimit.Angluin.prependStream xs base
  have hcombinedP : GenLimit.Generic.Presents combined (C z) :=
    GenLimit.Angluin.prependStream_presents hlock.1 hbaseP
  obtain ⟨ell, hell, N, hconverges⟩ :=
    hIdentifies combined hcombinedP
  have hbaseIn : GenLimit.Generic.StreamIn base (C z) :=
    GenLimit.Generic.streamIn_of_presents hbaseP
  have htailIn :
      GenLimit.Angluin.ListWithin
        (GenLimit.Angluin.streamPrefix base N) (C z) :=
    GenLimit.Angluin.streamPrefix_listWithin hbaseIn N
  have hlocked :
      M (xs ++ GenLimit.Angluin.streamPrefix base N) = j :=
    hlock.2 _ htailIn
  have hprefix :
      GenLimit.Angluin.streamPrefix combined (xs.length + N) =
        xs ++ GenLimit.Angluin.streamPrefix base N :=
    GenLimit.Angluin.streamPrefix_prependStream xs base N
  have hlimit :
      M (xs ++ GenLimit.Angluin.streamPrefix base N) = ell := by
    rw [← hprefix]
    exact hconverges _ (Nat.le_add_left N xs.length)
  have hjell : j = ell := hlocked.symm.trans hlimit
  exact (congrArg C hjell).trans hell

/-- Generic form of the locking-sequence-to-tell-tale lemma. -/
theorem lockingSequence_isTellTale_with_presentations
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    (hIdentifies : ∀ z, ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ j, C j = C z ∧ ListConvergesTo M stream j)
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C i))
    {z j : ℕ} {xs : List α}
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j)
    (hcorrect : C j = C z) :
    GenLimit.Angluin.IsTellTale C z xs.toFinset := by
  classical
  constructor
  · intro x hx
    exact hlock.1 x (List.mem_toFinset.mp hx)
  · intro k hcontent hkz
    obtain ⟨base, hbase⟩ := hPresentable k
    have hxsK : GenLimit.Angluin.ListWithin xs (C k) := by
      intro x hx
      exact hcontent (List.mem_toFinset.mpr hx)
    let combined := GenLimit.Angluin.prependStream xs base
    have hcombined : GenLimit.Generic.Presents combined (C k) :=
      GenLimit.Angluin.prependStream_presents hxsK hbase
    obtain ⟨ell, hell, Nell, hconverges⟩ :=
      hIdentifies k combined hcombined
    have hbaseInK : GenLimit.Generic.StreamIn base (C k) :=
      GenLimit.Generic.streamIn_of_presents hbase
    have htailInZ :
        GenLimit.Angluin.ListWithin
          (GenLimit.Angluin.streamPrefix base Nell) (C z) := by
      apply GenLimit.Angluin.streamPrefix_listWithin
      exact fun x hx => hkz (hbaseInK hx)
    have hlocked :
        M (xs ++ GenLimit.Angluin.streamPrefix base Nell) = j :=
      hlock.2 _ htailInZ
    have hprefix :
        GenLimit.Angluin.streamPrefix combined (xs.length + Nell) =
          xs ++ GenLimit.Angluin.streamPrefix base Nell :=
      GenLimit.Angluin.streamPrefix_prependStream xs base Nell
    have hlearned :
        M (xs ++ GenLimit.Angluin.streamPrefix base Nell) = ell := by
      rw [← hprefix]
      exact hconverges (xs.length + Nell)
        (Nat.le_add_left Nell xs.length)
    have hjell : j = ell := hlocked.symm.trans hlearned
    have htargetsEqual : C z = C k :=
      hcorrect.symm.trans ((congrArg C hjell).trans hell)
    exact htargetsEqual.subset

/-- Variant needed when the indexed collection may contain empty languages.
A nonempty locking history cannot be contained in an empty candidate, while
every nonempty candidate has an exact positive presentation. -/
theorem lockingSequence_isTellTale_with_nonempty_presentations
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    (hIdentifies : ∀ z, ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ j, C j = C z ∧ ListConvergesTo M stream j)
    (hPresentable : ∀ i, (C i).Nonempty →
      ∃ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream (C i))
    {z j : ℕ} {xs : List α}
    (hxs : xs ≠ [])
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j)
    (hcorrect : C j = C z) :
    GenLimit.Angluin.IsTellTale C z xs.toFinset := by
  classical
  constructor
  · intro x hx
    exact hlock.1 x (List.mem_toFinset.mp hx)
  · intro k hcontent hkz
    have hkNonempty : (C k).Nonempty := by
      cases hxsEq : xs with
      | nil => exact (hxs hxsEq).elim
      | cons x tail =>
          refine ⟨x, hcontent ?_⟩
          apply List.mem_toFinset.mpr
          rw [hxsEq]
          simp
    obtain ⟨base, hbase⟩ := hPresentable k hkNonempty
    have hxsK : GenLimit.Angluin.ListWithin xs (C k) := by
      intro x hx
      exact hcontent (List.mem_toFinset.mpr hx)
    let combined := GenLimit.Angluin.prependStream xs base
    have hcombined : GenLimit.Generic.Presents combined (C k) :=
      GenLimit.Angluin.prependStream_presents hxsK hbase
    obtain ⟨ell, hell, Nell, hconverges⟩ :=
      hIdentifies k combined hcombined
    have hbaseInK : GenLimit.Generic.StreamIn base (C k) :=
      GenLimit.Generic.streamIn_of_presents hbase
    have htailInZ :
        GenLimit.Angluin.ListWithin
          (GenLimit.Angluin.streamPrefix base Nell) (C z) := by
      apply GenLimit.Angluin.streamPrefix_listWithin
      exact fun x hx => hkz (hbaseInK hx)
    have hlocked :
        M (xs ++ GenLimit.Angluin.streamPrefix base Nell) = j :=
      hlock.2 _ htailInZ
    have hprefix :
        GenLimit.Angluin.streamPrefix combined (xs.length + Nell) =
          xs ++ GenLimit.Angluin.streamPrefix base Nell :=
      GenLimit.Angluin.streamPrefix_prependStream xs base Nell
    have hlearned :
        M (xs ++ GenLimit.Angluin.streamPrefix base Nell) = ell := by
      rw [← hprefix]
      exact hconverges (xs.length + Nell)
        (Nat.le_add_left Nell xs.length)
    have hjell : j = ell := hlocked.symm.trans hlearned
    have htargetsEqual : C z = C k :=
      hcorrect.symm.trans ((congrArg C hjell).trans hell)
    exact htargetsEqual.subset

/-- Extending a locking sequence by one target point preserves locking and
makes its content nonempty. -/
theorem append_mem_isLockingSequence
    {M : List α → ℕ} {L : Set α} {xs : List α} {j : ℕ}
    (hlock : GenLimit.Angluin.IsLockingSequence M L xs j)
    {x : α} (hx : x ∈ L) :
    GenLimit.Angluin.IsLockingSequence M L (xs ++ [x]) j := by
  constructor
  · intro y hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · exact hlock.1 y hy
    · subst y
      exact hx
  · intro tail htail
    have hwithin : GenLimit.Angluin.ListWithin ([x] ++ tail) L := by
      intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | hy
      · subst y
        exact hx
      · exact htail y hy
    simpa only [List.append_assoc] using hlock.2 ([x] ++ tail) hwithin

theorem conditionTwo_of_semanticallyIdentifiable
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (hID : ∃ M : GenLimit.Angluin.SemanticIdentifier α,
      GenLimit.Angluin.SemanticallyIdentifies M C) :
    GenLimit.Angluin.ConditionTwo C := by
  classical
  obtain ⟨M, hM⟩ := hID
  obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat α
  let LM := listIdentifierOf M
  have hListIdentifies : ∀ z, ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ j, C j = C z ∧
          ListConvergesTo LM stream j := by
    intro z stream hP
    obtain ⟨j, hj, T, hT⟩ := hM z stream hP
    refine ⟨j, hj, T, ?_⟩
    intro t ht
    change listIdentifierOf M
      (GenLimit.Angluin.streamPrefix stream t) = j
    rw [listIdentifierOf_streamPrefix]
    exact hT t ht
  have hPresentable : ∀ i, (C i).Nonempty →
      ∃ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream (C i) := by
    intro i hi
    exact ⟨presentationFromDomainEnumeration enumerate (C i) hi,
      presentationFromDomainEnumeration_presents
        enumerate henumerate (C i) hi⟩
  intro z
  by_cases hz : (C z).Nonempty
  · obtain ⟨base, hbaseP⟩ := hPresentable z hz
    have hTarget : ∀ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream (C z) →
          ∃ j, ListConvergesTo LM stream j := by
      intro stream hP
      obtain ⟨j, _hj, hconv⟩ := hListIdentifies z stream hP
      exact ⟨j, hconv⟩
    obtain ⟨xs, j, hlock⟩ :=
      exists_lockingSequence_of_identifies_with_presentation
        hbaseP hTarget
    let x := Classical.choose hz
    have hx : x ∈ C z := Classical.choose_spec hz
    let xs' := xs ++ [x]
    have hlock' : GenLimit.Angluin.IsLockingSequence LM (C z) xs' j :=
      append_mem_isLockingSequence hlock hx
    have hcorrect : C j = C z :=
      lockingSequence_correct_with_presentation
        hbaseP (hListIdentifies z) hlock'
    exact ⟨xs'.toFinset,
      lockingSequence_isTellTale_with_nonempty_presentations
        hListIdentifies hPresentable (by simp [xs'])
        hlock' hcorrect⟩
  · have hzEmpty : C z = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hz
    refine ⟨∅, ?_⟩
    simp [GenLimit.Angluin.IsTellTale, hzEmpty]

end GenLimit.Angluin
