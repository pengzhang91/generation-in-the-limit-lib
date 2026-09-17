import GenLimit.Core.Text
import GenLimit.Support.HistoryChain

/-!
# Text-prefix lemmas for append-only histories

This extension keeps the fixed-universe `GenLimit.textPrefix` dependency out
of the universe-polymorphic history-chain core.
-/

namespace GenLimit.Support
namespace HistoryChain

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

end HistoryChain
end GenLimit.Support
