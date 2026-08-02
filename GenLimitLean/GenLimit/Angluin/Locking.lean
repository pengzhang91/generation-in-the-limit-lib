import GenLimit.Angluin.Enumeration
import Mathlib.Data.List.OfFn

/-!
# Locking sequences and tell-tales

Angluin's necessity proof constructs, for each target, a finite positive
history after which the inference machine cannot change its conjecture along
any further target-language data.  This file formalizes the next proof lemma:
a correct locking sequence yields a finite tell-tale.

The remaining effective necessity step is the construction of uniformly
enumerable locking content from a computable successful inference machine.
That step is not asserted here.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

/-- Every entry of a finite history belongs to `L`. -/
def ListWithin (xs : List α) (L : Generic.Language α) : Prop :=
  ∀ x, x ∈ xs → x ∈ L

/-- `xs` locks the list-based identifier to the syntactic index `j` on every
finite continuation drawn from `L`. -/
def IsLockingSequence
    (M : List α → ℕ) (L : Generic.Language α)
    (xs : List α) (j : ℕ) : Prop :=
  ListWithin xs L ∧
    ∀ tail, ListWithin tail L → M (xs ++ tail) = j

/-- Prefix a finite list to an infinite stream. -/
noncomputable def prependStream
    (xs : List α) (stream : Generic.Stream α) : Generic.Stream α :=
  fun n => if h : n < xs.length then xs.get ⟨n, h⟩
    else stream (n - xs.length)

theorem streamPrefix_prependStream
    (xs : List α) (stream : Generic.Stream α) (t : ℕ) :
    streamPrefix (prependStream xs stream) (xs.length + t) =
      xs ++ streamPrefix stream t := by
  rw [streamPrefix, streamPrefix]
  calc
    List.ofFn
        (fun i : Fin (xs.length + t) => prependStream xs stream i) =
        List.ofFn (Fin.append xs.get (fun i : Fin t => stream i)) := by
      congr 1
      funext q
      refine Fin.addCases ?_ ?_ q
      · intro i
        simp [prependStream, Fin.append]
      · intro i
        simp [prependStream, Fin.append]
    _ = List.ofFn xs.get ++ List.ofFn (fun i : Fin t => stream i) :=
      List.ofFn_fin_append _ _
    _ = xs ++ List.ofFn (fun i : Fin t => stream i) := by simp

theorem prependStream_presents
    {xs : List α} {stream : Generic.Stream α}
    {L : Generic.Language α}
    (hxs : ListWithin xs L) (hP : Generic.Presents stream L) :
    Generic.Presents (prependStream xs stream) L := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    by_cases hn : n < xs.length
    · rw [prependStream, dif_pos hn]
      exact hxs _ (List.get_mem xs ⟨n, hn⟩)
    · rw [prependStream, dif_neg hn]
      rw [← hP]
      exact ⟨n - xs.length, rfl⟩
  · intro x hx
    rw [← hP] at hx
    obtain ⟨n, rfl⟩ := hx
    refine ⟨xs.length + n, ?_⟩
    simp [prependStream]

theorem streamPrefix_listWithin
    {stream : Generic.Stream α} {L : Generic.Language α}
    (hstream : Generic.StreamIn stream L) (t : ℕ) :
    ListWithin (streamPrefix stream t) L := by
  intro x hx
  rw [streamPrefix] at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact hstream ⟨i, rfl⟩

/-- A nonempty language over `ℕ` has an exact positive presentation.  This
uses a chosen member as padding while the stream scans all natural numbers. -/
noncomputable def presentationOfNonempty
    (L : Generic.Language ℕ) (hL : L.Nonempty) : Generic.Stream ℕ := by
  classical
  exact fun n => if n ∈ L then n else Classical.choose hL

theorem presentationOfNonempty_presents
    (L : Generic.Language ℕ) (hL : L.Nonempty) :
    Generic.Presents (presentationOfNonempty L hL) L := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    by_cases hn : n ∈ L
    · simp [presentationOfNonempty, hn]
    · simpa [presentationOfNonempty, hn] using Classical.choose_spec hL
  · intro x hx
    exact ⟨x, by simp [presentationOfNonempty, hx]⟩

/-- The proof lemma at the heart of the necessity direction: correct locking
content is a tell-tale.

If the locking content were contained in a proper family sublanguage, prefix
it to a presentation of that sublanguage.  Locking forces the old target
index forever, while identification forces convergence to the sublanguage,
a contradiction. -/
theorem lockingSequence_isTellTale
    {C : Generic.LanguageFamily ℕ} {M : List ℕ → ℕ}
    (hIdentifies : ∀ z, ∀ stream : Generic.Stream ℕ,
      Generic.Presents stream (C z) →
        ∃ j, C j = C z ∧ EffectiveConvergesTo M stream j)
    (hPresentable : ∀ i, ∃ stream : Generic.Stream ℕ,
      Generic.Presents stream (C i))
    {z j : ℕ} {xs : List ℕ}
    (hlock : IsLockingSequence M (C z) xs j)
    (hcorrect : C j = C z) :
    IsTellTale C z xs.toFinset := by
  classical
  constructor
  · intro x hx
    exact hlock.1 x (List.mem_toFinset.mp hx)
  · intro k hcontent hkz
    obtain ⟨base, hbase⟩ := hPresentable k
    have hxsK : ListWithin xs (C k) := by
      intro x hx
      exact hcontent (List.mem_toFinset.mpr hx)
    let combined := prependStream xs base
    have hcombined : Generic.Presents combined (C k) :=
      prependStream_presents hxsK hbase
    obtain ⟨ell, hell, Nell, hconverges⟩ :=
      hIdentifies k combined hcombined
    have hbaseInK : Generic.StreamIn base (C k) :=
      Generic.streamIn_of_presents hbase
    have htailInZ : ListWithin (streamPrefix base Nell) (C z) := by
      apply streamPrefix_listWithin
      exact fun x hx => hkz (hbaseInK hx)
    have hlocked : M (xs ++ streamPrefix base Nell) = j :=
      hlock.2 _ htailInZ
    have hprefix :
        streamPrefix combined (xs.length + Nell) =
          xs ++ streamPrefix base Nell :=
      streamPrefix_prependStream xs base Nell
    have hlearned : M (xs ++ streamPrefix base Nell) = ell := by
      rw [← hprefix]
      exact hconverges (xs.length + Nell) (Nat.le_add_left Nell xs.length)
    have hjell : j = ell := hlocked.symm.trans hlearned
    have htargetsEqual : C z = C k :=
      hcorrect.symm.trans ((congrArg C hjell).trans hell)
    exact htargetsEqual.subset

/-- If correct locking sequences have already been obtained for a successful
identifier, Condition 2 follows.  This packages the preceding source proof
lemma without claiming the still-missing effective locking construction. -/
theorem conditionTwo_of_correctLockingSequences
    {F : EffectiveIndexedFamily} {M : List ℕ → ℕ}
    (hIdentifies : ∀ z, ∀ stream : Generic.Stream ℕ,
      Generic.Presents stream (F.language z) →
        ∃ j, F.language j = F.language z ∧
          EffectiveConvergesTo M stream j)
    (hlocks : ∀ z, ∃ xs : List ℕ, ∃ j,
      IsLockingSequence M (F.language z) xs j ∧
        F.language j = F.language z) :
    ConditionTwo F.language := by
  have hPresentable : ∀ i, ∃ stream : Generic.Stream ℕ,
      Generic.Presents stream (F.language i) := by
    intro i
    exact ⟨presentationOfNonempty (F.language i) (F.nonempty i),
      presentationOfNonempty_presents _ _⟩
  intro z
  obtain ⟨xs, j, hlock, hcorrect⟩ := hlocks z
  exact ⟨xs.toFinset,
    lockingSequence_isTellTale hIdentifies hPresentable hlock hcorrect⟩

end GenLimit.Angluin
