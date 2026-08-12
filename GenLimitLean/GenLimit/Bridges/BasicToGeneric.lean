import GenLimit.Core.Basic
import GenLimit.Core.ClassGeneration

/-!
# The original Nat API and the generic generation API

The original KM development fixes the example universe to `ℕ`; #02 uses the
generic interface.  Their presentation and sample definitions agree exactly
at `α = ℕ`.  The only nontrivial adapter below turns a function of the observed
finite set into the tuple-history generator expected by #02.
-/

namespace GenLimit.Bridge

@[simp] theorem basicPresents_iff_genericPresents
    (stream : ℕ → ℕ) (L : Set ℕ) :
    GenLimit.Presents stream L ↔
      GenLimit.Generic.Presents stream L :=
  Iff.rfl

@[simp] theorem genericSample_eq_basicSample
    (stream : ℕ → ℕ) (t : ℕ) :
    GenLimit.Generic.sample stream t = GenLimit.sample stream t := by
  classical
  ext x
  simp [GenLimit.Generic.sample, GenLimit.sample]

/-- Regard a function of the observed finite set as a generic finite-history
generator. -/
noncomputable def generatorOfObservedSet
    (g : Finset ℕ → ℕ) : GenLimit.Generic.Generator ℕ :=
  fun _ history ↦ g (GenLimit.Generic.sequenceSample history)

@[simp] theorem output_generatorOfObservedSet
    (g : Finset ℕ → ℕ) (stream : ℕ → ℕ) (t : ℕ) :
    GenLimit.Generic.output (generatorOfObservedSet g) stream t =
      g (GenLimit.sample stream t) := by
  simp [GenLimit.Generic.output, generatorOfObservedSet,
    GenLimit.Generic.sequenceSample_prefix]

end GenLimit.Bridge
