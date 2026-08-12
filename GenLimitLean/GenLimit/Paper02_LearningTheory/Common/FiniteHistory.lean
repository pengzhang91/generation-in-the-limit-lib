import GenLimit.Core.GenericGeneration
import Mathlib.Data.List.OfFn

/-!
# Finite histories as streams for #02 Learning Theory

Several paper proofs inspect samples of prefixes of a finite generator input.
This module performs the conversion once, using the existing Core stream
constructor `GenLimit.Generic.historyThenFallback`.
-/

namespace GenLimit.LiRamanTewari.Common

/-- Extend a finite tuple by an arbitrary fallback.  Only prefixes no longer
than the tuple are relevant to the accompanying lemmas. -/
noncomputable def extendHistory [Nonempty α] {t : ℕ} (xs : Fin t → α) :
    GenLimit.Generic.Stream α :=
  GenLimit.Generic.historyThenFallback (List.ofFn xs)
    (Classical.choice inferInstance)

theorem extendHistory_apply_of_lt [Nonempty α]
    {t : ℕ} (xs : Fin t → α) {k : ℕ} (hk : k < t) :
    extendHistory xs k = xs ⟨k, hk⟩ := by
  simp [extendHistory, GenLimit.Generic.historyThenFallback, hk]

theorem sample_extendHistory_eq [Nonempty α]
    {t r : ℕ} (xs : Fin t → α) (hrt : r ≤ t) :
    GenLimit.Generic.sample (extendHistory xs) r =
      GenLimit.Generic.sequenceSample
        (fun i : Fin r ↦ xs ⟨i, i.isLt.trans_le hrt⟩) := by
  classical
  ext x
  simp only [GenLimit.Generic.mem_sample_iff,
    GenLimit.Generic.mem_sequenceSample_iff]
  constructor
  · rintro ⟨k, hk, hx⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    simpa [extendHistory_apply_of_lt xs (hk.trans_le hrt)] using hx
  · rintro ⟨k, hx⟩
    refine ⟨k, k.isLt, ?_⟩
    simpa [extendHistory_apply_of_lt xs (k.isLt.trans_le hrt)] using hx

theorem sample_extendHistory_full [Nonempty α]
    {t : ℕ} (xs : Fin t → α) :
    GenLimit.Generic.sample (extendHistory xs) t =
      GenLimit.Generic.sequenceSample xs := by
  simpa using sample_extendHistory_eq xs le_rfl

theorem sample_extendHistory_stream_eq [Nonempty α]
    {stream : GenLimit.Generic.Stream α} {t r : ℕ} (hrt : r ≤ t) :
    GenLimit.Generic.sample
        (extendHistory (fun i : Fin t ↦ stream i)) r =
      GenLimit.Generic.sample stream r := by
  classical
  ext x
  simp only [GenLimit.Generic.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, hx⟩
    refine ⟨k, hk, ?_⟩
    simpa [extendHistory_apply_of_lt
      (fun i : Fin t ↦ stream i) (hk.trans_le hrt)] using hx
  · rintro ⟨k, hk, hx⟩
    refine ⟨k, hk, ?_⟩
    simpa [extendHistory_apply_of_lt
      (fun i : Fin t ↦ stream i) (hk.trans_le hrt)] using hx

end GenLimit.LiRamanTewari.Common
