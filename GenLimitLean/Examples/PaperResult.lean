import GenLimit.Paper02_LearningTheory.Results.Overview

/-!
# Example: consume a paper's main-results facade

The singleton class containing only the universal language is a concrete
finite UUS class.  Paper #02 Theorem 2.5 can therefore be applied directly
through its stable `Results.Overview` wrapper.
-/

namespace GenLimit.Examples

open Generic

def singletonUniversalClass (α : Type*) : LanguageClass α :=
  {Set.univ}

theorem singleton_universal_class_uniformly_generatable
    [Nonempty α] [Countable α] [Infinite α] :
    UniformlyGeneratable (singletonUniversalClass α) := by
  apply LiRamanTewari.Results.theorem_2_5
  · intro L hL
    have hL' : L = (Set.univ : Language α) := by
      simpa [singletonUniversalClass] using hL
    subst L
    exact Set.infinite_univ
  · change ({Set.univ} : Set (Language α)).Finite
    exact Set.finite_singleton Set.univ

end GenLimit.Examples
