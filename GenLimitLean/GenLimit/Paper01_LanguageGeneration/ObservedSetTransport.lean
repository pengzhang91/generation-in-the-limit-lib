import GenLimit.Paper01_LanguageGeneration.Transport
import GenLimit.Paper01_LanguageGeneration.SetInterface

/-! # Section 4 generation from an observed set over an enumerable universe -/

namespace GenLimit.KM.Transport

/-- Encode the observed set, run the Section 4 set generator and decode its output. -/
noncomputable def observedSetGenerator
    (e : α ≃ ℕ) (O : IndexedOracleFamily α) (S : Finset α) : α :=
  e.symm (SetInterface.generator (encodeFamily e O) (FiniteFamily.encodeSample e S))

theorem encodeSample_prefix (e : α ≃ ℕ) (stream : Generic.Stream α) (t : ℕ) :
    FiniteFamily.encodeSample e (Generic.sample stream t) =
      sample (Support.renameStream e stream) t := by
  ext n
  obtain ⟨x, rfl⟩ := e.surjective n
  rw [FiniteFamily.mem_encodeSample, mem_encoded_sample_iff]

/-- Equations (4.1) and (4.6) with an explicit universe enumeration. Repeated
observations are permitted and the generator receives only the finite set. -/
theorem observedSetGenerator_generates
    (e : α ≃ ℕ) (O : IndexedOracleFamily α) {stream : Generic.Stream α} {z : ℕ}
    (hp : Generic.Presents stream (O.language z)) :
    ∃ T, ∀ t ≥ T, observedSetGenerator e O (Generic.sample stream t) ∈ O.language z ∧
      observedSetGenerator e O (Generic.sample stream t) ∉ Generic.sample stream t := by
  obtain ⟨T, hT⟩ := SetInterface.kleinbergMullainathan_set_interface_with_repetitions
    (encodeFamily e O) (stream := Support.renameStream e stream) (z := z)
    (Support.presents_renameStream e hp)
  refine ⟨T, fun t ht => ?_⟩
  let x := observedSetGenerator e O (Generic.sample stream t)
  have hx : e x = SetInterface.generator (encodeFamily e O)
      (sample (Support.renameStream e stream) t) := by
    simp [x, observedSetGenerator, encodeSample_prefix]
  obtain ⟨hm, hf⟩ := hT t ht
  constructor
  · apply (Support.mem_renameLanguage_iff e (O.language z) x).mp
    rw [hx]
    exact hm
  · intro hs
    exact hf (hx ▸ (mem_encoded_sample_iff e stream t x).mpr hs)

end GenLimit.KM.Transport
