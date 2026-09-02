import GenLimit.Core.GenericGeneration
import GenLimit.Core.Identification
import GenLimit.Core.Text
import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn

/-!
# Generic locking-sequence infrastructure

This module contains the paper-independent diagonal construction behind
locking-sequence arguments for positive-data identification.  It is
parameterized by the example type and by an arbitrary list-based learner.

The construction was originally embedded in the Gold/Angluin developments.
Keeping the generic finite-history API here lets later identification papers
reuse it without importing a paper-specific compatibility namespace.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

/-- Every entry of a finite history belongs to `L`. -/
def ListWithin (xs : List α) (L : Generic.Language α) : Prop :=
  ∀ x, x ∈ xs → x ∈ L

/-- `xs` locks a list-based learner to `j` on every continuation from `L`. -/
def IsLockingSequence
    (M : List α → β) (L : Generic.Language α)
    (xs : List α) (j : β) : Prop :=
  ListWithin xs L ∧
    ∀ tail, ListWithin tail L → M (xs ++ tail) = j

/-- Prefix a finite history to an infinite stream. -/
noncomputable def prependStream
    (xs : List α) (stream : Generic.Stream α) : Generic.Stream α :=
  fun n => if h : n < xs.length then xs.get ⟨n, h⟩
    else stream (n - xs.length)

theorem streamPrefix_prependStream
    (xs : List α) (stream : Generic.Stream α) (t : ℕ) :
    GenLimit.textPrefix (prependStream xs stream) (xs.length + t) =
      xs ++ GenLimit.textPrefix stream t := by
  rw [GenLimit.textPrefix_eq_ofFn, GenLimit.textPrefix_eq_ofFn]
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
    exact ⟨xs.length + n, by simp [prependStream]⟩

theorem streamPrefix_listWithin
    {stream : Generic.Stream α} {L : Generic.Language α}
    (hstream : Generic.StreamIn stream L) (t : ℕ) :
    ListWithin (GenLimit.textPrefix stream t) L := by
  intro x hx
  rw [GenLimit.textPrefix_eq_ofFn] at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact hstream ⟨i, rfl⟩

/-- A nonempty language over `ℕ` has an exact positive presentation. -/
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

/-- A target-language continuation on which the learner changes its guess. -/
def HasChangeExtension
    (M : List α → β) (L : Generic.Language α) (xs : List α) : Prop :=
  ∃ tail, ListWithin tail L ∧ M (xs ++ tail) ≠ M xs

theorem hasChangeExtension_of_not_locking
    {M : List α → β} {L : Generic.Language α} {xs : List α}
    (hxs : ListWithin xs L)
    (hno : ¬IsLockingSequence M L xs (M xs)) :
    HasChangeExtension M L xs := by
  by_contra h
  apply hno
  constructor
  · exact hxs
  · intro tail htail
    by_contra hchange
    exact h ⟨tail, htail, hchange⟩

/-- Histories whose entries all lie in `L`. -/
abbrev HistoryIn (L : Generic.Language α) :=
  {xs : List α // ListWithin xs L}

theorem listWithin_append
    {L : Generic.Language α} {xs ys : List α}
    (hxs : ListWithin xs L) (hys : ListWithin ys L) :
    ListWithin (xs ++ ys) L := by
  intro x hx
  rw [List.mem_append] at hx
  exact hx.elim (hxs x) (hys x)

theorem singletonWithin
    {L : Generic.Language α} {x : α} (hx : x ∈ L) :
    ListWithin [x] L := by
  simpa [ListWithin]

/-- Insert the next base datum, then force one further mind change. -/
noncomputable def adversarialStep
    (M : List α → β) (L : Generic.Language α)
    (base : Generic.Stream α) (hbase : Generic.StreamIn base L)
    (hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs)
    (n : ℕ) (state : HistoryIn L) : HistoryIn L := by
  classical
  let seeded : List α := state.1 ++ [base n]
  have hseeded : ListWithin seeded L :=
    listWithin_append state.2 (singletonWithin (hbase ⟨n, rfl⟩))
  let tail : List α := Classical.choose (hchange seeded hseeded)
  have htail : ListWithin tail L :=
    (Classical.choose_spec (hchange seeded hseeded)).1
  exact ⟨seeded ++ tail, listWithin_append hseeded htail⟩

theorem adversarialStep_eq
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} {hbase : Generic.StreamIn base L}
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs}
    (n : ℕ) (state : HistoryIn L) :
    (adversarialStep M L base hbase hchange n state).1 =
      let seeded := state.1 ++ [base n]
      seeded ++ Classical.choose
        (hchange seeded
          (listWithin_append state.2
            (singletonWithin (hbase ⟨n, rfl⟩)))) := by
  rfl

/-- Nested finite histories generated by the diagonal construction. -/
noncomputable def adversarialHistory
    (M : List α → β) (L : Generic.Language α)
    (base : Generic.Stream α) (hbase : Generic.StreamIn base L)
    (hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs) :
    ℕ → HistoryIn L
  | 0 => ⟨[], by simp [ListWithin]⟩
  | n + 1 => adversarialStep M L base hbase hchange n
      (adversarialHistory M L base hbase hchange n)

theorem adversarialHistory_prefix_succ
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} {hbase : Generic.StreamIn base L}
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs}
    (n : ℕ) :
    (adversarialHistory M L base hbase hchange n).1 <+:
      (adversarialHistory M L base hbase hchange (n + 1)).1 := by
  rw [adversarialHistory, adversarialStep_eq]
  exact List.IsPrefix.trans (List.prefix_append _ [base n])
    (List.prefix_append _ _)

theorem adversarialHistory_prefix
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} {hbase : Generic.StreamIn base L}
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs}
    {n m : ℕ} (hnm : n ≤ m) :
    (adversarialHistory M L base hbase hchange n).1 <+:
      (adversarialHistory M L base hbase hchange m).1 := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m hnm ih =>
      exact ih.trans (adversarialHistory_prefix_succ m)

theorem adversarialHistory_length
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} {hbase : Generic.StreamIn base L}
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs}
    (n : ℕ) :
    n ≤ (adversarialHistory M L base hbase hchange n).1.length := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [adversarialHistory, adversarialStep_eq]
      simp only [List.length_append, List.length_singleton]
      omega

/-- The infinite stream determined by the compatible diagonal histories. -/
noncomputable def adversarialStream
    (M : List α → β) (L : Generic.Language α)
    (base : Generic.Stream α) (hbase : Generic.StreamIn base L)
    (hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs) :
    Generic.Stream α := fun k =>
  let history := (adversarialHistory M L base hbase hchange (k + 1)).1
  history.get ⟨k, by
    have hlen := adversarialHistory_length
      (M := M) (L := L) (base := base) (hbase := hbase)
      (hchange := hchange) (k + 1)
    have : k + 1 ≤ history.length := by
      simpa [history] using hlen
    exact lt_of_lt_of_le (Nat.lt_succ_self k) this⟩

theorem adversarialStream_eq_history_get
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} {hbase : Generic.StreamIn base L}
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs}
    (n k : ℕ)
    (hk : k < (adversarialHistory M L base hbase hchange n).1.length) :
    adversarialStream M L base hbase hchange k =
      (adversarialHistory M L base hbase hchange n).1.get ⟨k, hk⟩ := by
  rw [adversarialStream]
  have hbound : k <
      (adversarialHistory M L base hbase hchange (k + 1)).1.length := by
    have hlen := adversarialHistory_length
      (M := M) (L := L) (base := base) (hbase := hbase)
      (hchange := hchange) (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) n with hkn | hnk
  · have hp := adversarialHistory_prefix
        (M := M) (L := L) (base := base) (hbase := hbase)
        (hchange := hchange) hkn
    exact (List.prefix_iff_getElem.mp hp).2 k hbound
  · have hp := adversarialHistory_prefix
        (M := M) (L := L) (base := base) (hbase := hbase)
        (hchange := hchange) hnk
    exact ((List.prefix_iff_getElem.mp hp).2 k hk).symm

theorem streamPrefix_adversarialStream
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} {hbase : Generic.StreamIn base L}
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs}
    (n : ℕ) :
    GenLimit.textPrefix (adversarialStream M L base hbase hchange)
        (adversarialHistory M L base hbase hchange n).1.length =
      (adversarialHistory M L base hbase hchange n).1 := by
  apply List.ext_get
  · simp [GenLimit.textPrefix]
  · intro k hkPrefix hkHistory
    simp only [GenLimit.textPrefix, List.get_eq_getElem, List.getElem_map,
      List.getElem_range]
    exact adversarialStream_eq_history_get n k hkHistory

theorem streamPrefix_adversarialStream_of_prefix
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} {hbase : Generic.StreamIn base L}
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs}
    {xs : List α} {n : ℕ}
    (hxs : xs <+:
      (adversarialHistory M L base hbase hchange n).1) :
    GenLimit.textPrefix (adversarialStream M L base hbase hchange)
        xs.length = xs := by
  apply List.ext_get
  · simp [GenLimit.textPrefix]
  · intro k hkStream hkxs
    simp only [GenLimit.textPrefix, List.get_eq_getElem, List.getElem_map,
      List.getElem_range]
    have hdiag := adversarialStream_eq_history_get
      (M := M) (L := L) (base := base) (hbase := hbase)
      (hchange := hchange) n k (lt_of_lt_of_le hkxs hxs.length_le)
    have hp := (List.prefix_iff_getElem.mp hxs).2 k hkxs
    rw [List.get_eq_getElem] at hdiag
    exact hdiag.trans hp.symm

theorem adversarialStream_presents
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} (hP : Generic.Presents base L)
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs} :
    Generic.Presents
      (adversarialStream M L base
        (Generic.streamIn_of_presents hP) hchange) L := by
  classical
  let hbase := Generic.streamIn_of_presents hP
  apply Set.Subset.antisymm
  · rintro x ⟨k, rfl⟩
    rw [adversarialStream]
    exact (adversarialHistory M L base hbase hchange (k + 1)).2 _
      (List.get_mem _ _)
  · intro x hx
    rw [← hP] at hx
    obtain ⟨n, rfl⟩ := hx
    let history := (adversarialHistory M L base hbase hchange (n + 1)).1
    have hbaseMem : base n ∈ history := by
      dsimp [history]
      rw [adversarialHistory.eq_def, adversarialStep_eq]
      simp
    have hprefix := streamPrefix_adversarialStream
      (M := M) (L := L) (base := base) (hbase := hbase)
      (hchange := hchange) (n + 1)
    change base n ∈
      (adversarialHistory M L base hbase hchange (n + 1)).1 at hbaseMem
    rw [← hprefix] at hbaseMem
    rw [GenLimit.textPrefix_eq_ofFn] at hbaseMem
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hbaseMem
    exact ⟨i, hi⟩

theorem adversarialHistory_mindChange
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α} {hbase : Generic.StreamIn base L}
    {hchange : ∀ xs, ListWithin xs L → HasChangeExtension M L xs}
    (n : ℕ) :
    let history := (adversarialHistory M L base hbase hchange n).1
    let seeded := history ++ [base n]
    M (adversarialHistory M L base hbase hchange (n + 1)).1 ≠ M seeded := by
  rw [adversarialHistory, adversarialStep_eq]
  exact (Classical.choose_spec
    (hchange _
      (listWithin_append
        (adversarialHistory M L base hbase hchange n).2
        (singletonWithin (hbase ⟨n, rfl⟩))))).2

/-- If a finite-history learner converges on every exact presentation of a
language, then some finite history locks its output on every continuation
from that language.  Supplying the base presentation keeps this statement
independent of any particular enumeration theorem for the example type. -/
theorem exists_lockingSequence_of_converges_with_base
    {M : List α → β} {L : Generic.Language α}
    {base : Generic.Stream α}
    (hbaseP : Generic.Presents base L)
    (hConverges : ∀ stream : Generic.Stream α,
      Generic.Presents stream L →
        ∃ j, GenLimit.StabilizesTo
          (fun t => M (GenLimit.textPrefix stream t)) j) :
    ∃ xs : List α, ∃ j, IsLockingSequence M L xs j := by
  classical
  by_contra hlocks
  push_neg at hlocks
  have hchange :
      ∀ xs, ListWithin xs L → HasChangeExtension M L xs := by
    intro xs hxs
    exact hasChangeExtension_of_not_locking hxs (hlocks xs (M xs))
  let hbase := Generic.streamIn_of_presents hbaseP
  let diagonal := adversarialStream M L base hbase hchange
  have hdiagonalP : Generic.Presents diagonal L :=
    adversarialStream_presents (M := M) hbaseP
  obtain ⟨j, T, hconverges⟩ := hConverges diagonal hdiagonalP
  let n := T
  let history :=
    (adversarialHistory M L base hbase hchange n).1
  let seeded := history ++ [base n]
  have hseededPrefix :
      GenLimit.textPrefix diagonal seeded.length = seeded := by
    have hseededHist : seeded <+:
        (adversarialHistory M L base hbase hchange (n + 1)).1 := by
      rw [adversarialHistory, adversarialStep_eq]
      exact List.prefix_append _ _
    exact streamPrefix_adversarialStream_of_prefix hseededHist
  have hnextPrefix :=
    streamPrefix_adversarialStream
      (M := M) (L := L) (base := base) (hbase := hbase)
      (hchange := hchange) (n + 1)
  have hseededLen : T ≤ seeded.length := by
    have hlen :=
      adversarialHistory_length
        (M := M) (L := L) (base := base) (hbase := hbase)
        (hchange := hchange) T
    dsimp [seeded, history, n]
    simp only [List.length_append, List.length_singleton]
    omega
  have hnextLen : T ≤
      (adversarialHistory M L base hbase hchange (n + 1)).1.length := by
    dsimp [n]
    exact le_trans (Nat.le_add_right T 1)
      (adversarialHistory_length
        (M := M) (L := L) (base := base) (hbase := hbase)
        (hchange := hchange) (T + 1))
  have hseededGuess : M seeded = j := by
    rw [← hseededPrefix]
    exact hconverges _ hseededLen
  have hnextGuess :
      M (adversarialHistory M L base hbase hchange (n + 1)).1 = j := by
    rw [← hnextPrefix]
    exact hconverges _ hnextLen
  exact
    (adversarialHistory_mindChange
      (M := M) (L := L) (base := base) (hbase := hbase)
      (hchange := hchange) n)
      (hnextGuess.trans hseededGuess.symm)

end GenLimit.Angluin
