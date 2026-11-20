import GenLimit.NoRegretLanguageGeneration.ForcingEmbedding
import GenLimit.NoRegretLanguageGeneration.MarkedUnion

namespace PredictionToGeneration.MarkedUnion
open Classical

/-- Revealing the marker first prevents its reuse as a constant-positive output. -/
theorem union_forces {I : Type} {X : I → Type} (C : (i : I) → HypothesisClass (X i))
    (i : I) (hu : UUS (C i)) (hne : ∃ h,C i h) (n m : Nat)
    (hf : MFForces (C i) n m) : MFForces (Union C) (n+1) m := by
  intro z _
  refine ⟨marker i,by simp [Fresh,demonstrations],?_⟩
  apply forces_embedding (C i) (Union C) hu hne (embed i) ?_ (lift i)
    (fun h hh => ⟨i,h,hh,rfl⟩) (fun h _ x => lift_embed i h x) n m [] [(z,marker i)]
    ?_ ?_ ?_ ?_ hf
  · intro x y he
    simpa [embed] using he
  · intro x
    simp [DemonstrationLink,demonstrations,embed,marker]
  · intro h _ _
    exact ⟨lift_marker i h,trivial⟩
  · intro h _
    exact Nat.zero_le _
  · intro h _ y hy hn
    by_cases hidx : y.1=i
    · rcases y with ⟨j,y⟩
      dsimp at hidx
      subst j
      cases y with
      | none => exact False.elim (hy (by simp [demonstrations,marker]))
      | some x => exact False.elim (hn x rfl)
    · exact lift_other i h y hidx

end PredictionToGeneration.MarkedUnion
