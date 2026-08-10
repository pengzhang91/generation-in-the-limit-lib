import GenLimit.Paper08_HallucinationDetection.Appendix
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization

/-!
# #02 Learning Theory to #08 Hallucination Detection

Theorem A.2 of Karbasi--Montasser--Sous--Velegkas invokes the countable-class
generation result formalized in #02 Learning Theory. Keeping
that proof here makes the native hallucination-detection import path
independent of every later paper development while preserving the source's
public theorem name.
-/

namespace GenLimit.HallucinationDetection

/-- Theorem A.2. Infinite targets use the countable-class generator; finite
targets eventually have empty unseen remainder, exactly as allowed by
Definition 5. -/
theorem theorem_A_2
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    AppendixGeneratableInLimit C := by
  classical
  obtain ⟨G, hG⟩ :=
    GenLimit.LiRamanTewari.countable_classes_are_nonuniformly_generatable
      (infiniteMembers_uus C) (infiniteMembers_countable C)
  refine ⟨G, ?_⟩
  intro z stream hP
  by_cases hInfinite : (C z).Infinite
  · have htarget : C z ∈ infiniteMembers C :=
      ⟨⟨z, rfl⟩, hInfinite⟩
    obtain ⟨d, hd⟩ := hG (C z) htarget
    obtain ⟨T, hcard⟩ :=
      GenLimit.Generic.exists_sample_card_eq_of_presents_infinite
        hP hInfinite d
    refine ⟨T, ?_⟩
    intro t ht
    left
    exact hd stream (GenLimit.Generic.streamIn_of_presents hP)
      T hcard t ht
  · have hFinite : (C z).Finite := Set.not_infinite.mp hInfinite
    have hmemFinite {x : α} :
        x ∈ hFinite.toFinset ↔ x ∈ C z :=
      hFinite.mem_toFinset
    obtain ⟨T, hsubsetT⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample
        hP hFinite.toFinset (by
        intro x hx
        exact hmemFinite.mp hx)
    refine ⟨T, ?_⟩
    intro t ht
    right
    apply Set.diff_eq_empty.mpr
    intro x hx
    have hxT : x ∈ hFinite.toFinset := hmemFinite.mpr hx
    exact GenLimit.Generic.sample_mono ht (hsubsetT hxT)

end GenLimit.HallucinationDetection
