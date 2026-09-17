import GenLimit.Core.GenericGeneration
import GenLimit.Core.Text
import Mathlib.Data.List.Infix

/-!
# Append-only finite histories and their limit stream

This module separates the generic bookkeeping shared by diagonal
constructions from the paper-specific rules that build each finite history.
`PrefixChain` records only append-only growth.  `HistoryChain` adds the
progress condition needed to read a total infinite stream from those
histories.  The progress condition deliberately does not belong to
`PrefixChain`: append-only ledgers may remain unchanged for a round.
-/

namespace GenLimit.Support

/-- A sequence of finite histories that grows by the list-prefix relation. -/
structure PrefixChain (α : Type*) where
  history : ℕ → List α
  prefix_succ : ∀ n, history n <+: history (n + 1)

namespace PrefixChain

/-- Every earlier history is a prefix of every later history. -/
theorem prefix_of_le
    (chain : PrefixChain α) {n m : ℕ} (hnm : n ≤ m) :
    chain.history n <+: chain.history m := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m hnm ih => exact ih.trans (chain.prefix_succ m)

end PrefixChain

/-- An append-only history whose `n`-th stage already contains at least `n`
entries. -/
structure HistoryChain (α : Type*) extends PrefixChain α where
  le_length : ∀ n, n ≤ (history n).length

namespace HistoryChain

/-- The infinite stream determined by compatible histories with progress. -/
def stream (chain : HistoryChain α) : GenLimit.Generic.Stream α :=
  fun k => (chain.history (k + 1)).get ⟨k, by
    have hlength := chain.le_length (k + 1)
    exact Nat.lt_of_succ_le hlength⟩

/-- Reading the limit stream at a position already present in any finite
history returns that history's entry. -/
theorem stream_eq_get
    (chain : HistoryChain α) (n k : ℕ)
    (hk : k < (chain.history n).length) :
    chain.stream k = (chain.history n).get ⟨k, hk⟩ := by
  rw [stream]
  have hbound : k < (chain.history (k + 1)).length := by
    have hlength := chain.le_length (k + 1)
    exact Nat.lt_of_succ_le hlength
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) n with hkn | hnk
  · have hp := chain.toPrefixChain.prefix_of_le hkn
    exact (List.prefix_iff_getElem.mp hp).2 k hbound
  · have hp := chain.toPrefixChain.prefix_of_le hnk
    exact ((List.prefix_iff_getElem.mp hp).2 k hk).symm

/-- Taking exactly the length of a finite history from the limit stream
recovers that history. -/
theorem textPrefix_stream (chain : HistoryChain α) (n : ℕ) :
    GenLimit.textPrefix chain.stream (chain.history n).length =
      chain.history n := by
  apply List.ext_get
  · simp [GenLimit.textPrefix]
  · intro k _hkPrefix hkHistory
    simp only [GenLimit.textPrefix, List.get_eq_getElem, List.getElem_map,
      List.getElem_range]
    exact chain.stream_eq_get n k hkHistory

/-- Any list known to be a prefix of a finite history is also the
corresponding prefix of the limit stream. -/
theorem textPrefix_stream_of_prefix
    (chain : HistoryChain α) {xs : List α} {n : ℕ}
    (hxs : xs <+: chain.history n) :
    GenLimit.textPrefix chain.stream xs.length = xs := by
  apply List.ext_get
  · simp [GenLimit.textPrefix]
  · intro k _hkStream hkxs
    simp only [GenLimit.textPrefix, List.get_eq_getElem, List.getElem_map,
      List.getElem_range]
    have hstream := chain.stream_eq_get n k
      (lt_of_lt_of_le hkxs hxs.length_le)
    have hp := (List.prefix_iff_getElem.mp hxs).2 k hkxs
    rw [List.get_eq_getElem] at hstream
    exact hstream.trans hp.symm

/-- The distinct sample at a finite-history boundary is exactly the set of
values in that history. -/
theorem sample_stream_at_history
    [DecidableEq α] (chain : HistoryChain α) (n : ℕ) :
    GenLimit.Generic.sample chain.stream (chain.history n).length =
      (chain.history n).toFinset := by
  calc
    _ = GenLimit.Generic.sample
        (GenLimit.Generic.historyThenFallback (chain.history n)
          (chain.stream 0))
        (chain.history n).length := by
      apply GenLimit.Generic.sample_eq_of_eq_on_prefix
      intro k hk
      rw [GenLimit.Generic.historyThenFallback, dif_pos hk]
      exact chain.stream_eq_get n k hk
    _ = _ := GenLimit.Generic.sample_historyThenFallback_length _ _

end HistoryChain

end GenLimit.Support
