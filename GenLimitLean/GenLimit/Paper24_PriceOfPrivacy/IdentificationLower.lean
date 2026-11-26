import GenLimit.Paper24_PriceOfPrivacy.CommonAtom
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.WeakLower

/-! The intersecting private pair lower bound, Theorem 5.2. -/

namespace GenLimit.PriceOfPrivacy

open AgnosticLanguage DiscreteIID
open scoped ENNReal Classical
noncomputable section

/-- Definition 5.1. Privacy of a word is relative to the whole collection.
Multiple indices are allowed to name the same language. -/
def IntersectingPrivatePair (C : Generic.LanguageFamily X) : Prop :=
  ∃ i j, C i ≠ C j ∧ ∃ a ∈ C i ∩ C j, ∃ x ∈ C i, ∃ y ∈ C j,
    (∀ k, x ∈ C k → C k = C i) ∧ (∀ k, y ∈ C k → C k = C j)

private def twoAtom (a b : X) := spiked (PMF.pure ()) a (fun _ => b)

private theorem twoAtom_event (a b : X) (F : Set X) :
    probability (twoAtom a b) F =
      (if a ∈ F then 3/4 else 0) + (if b ∈ F then 1/4 else 0) := by
  rw [twoAtom,spiked_event,PMF.pure_map,probability,PMF.toOuterMeasure_pure_apply]
  by_cases hb : b ∈ F <;> simp [hb]

private theorem private_gap (C : Generic.LanguageFamily X) (i : ℕ) (a b : X)
    (ha : a ∈ C i) (hb : b ∈ C i) (priv : ∀ k, b ∈ C k → C k = C i) :
    Optimal C (twoAtom a b) i ∧ ∀ k, C k ≠ C i →
      1/4 ≤ risk (twoAtom a b) (C k) - optimalRisk C (twoAtom a b) := by
  have hi : risk (twoAtom a b) (C i) = 0 := by simp [risk,twoAtom_event,ha,hb]
  have best : optimalRisk C (twoAtom a b) = 0 :=
    le_antisymm ((optimalRisk_le C _ i).trans_eq hi) (optimalRisk_nonneg ..)
  refine ⟨hi.trans best.symm,fun k hk => ?_⟩
  have absent : b ∉ C k := fun h => hk (priv k h)
  rw [best,sub_zero,risk,twoAtom_event]
  by_cases has : a ∈ C k <;> norm_num [absent,has]

/-- Privacy applies to the actual language released by the identifier. -/
def languageOutput (C : Generic.LanguageFamily X) (A : Identifier X) (xs : List X) :=
  (A xs).map C

private theorem language_event (C : Generic.LanguageFamily X) (A : Identifier X)
    (q : PMF (List X)) (F : Set (Set X)) :
    probability (q.bind (languageOutput C A)) F = probability (q.bind A) (C ⁻¹' F) := by
  unfold languageOutput probability
  rw [← PMF.map_bind,PMF.toOuterMeasure_map_apply]

theorem identification_lower (C : Generic.LanguageFamily X) (ipp : IntersectingPrivatePair C) :
    ∃ p₀ p₁ : PMF X, (∃ i, Optimal C p₀ i) ∧ (∃ j, Optimal C p₁ j) ∧
      ∀ (ε : ℝ≥0∞) (A : Identifier X), IsPrivate ε (languageOutput C A) →
      ∀ n : ℕ, commonRate ε ^ n / 8 ≤ max (idErr C A p₀ n) (idErr C A p₁ n) := by
  obtain ⟨i,j,diff,a,ha,x,hx,y,hy,hpx,hpy⟩ := ipp
  obtain ⟨opt₀,gap₀⟩ := private_gap C i a x ha.1 hx hpx
  obtain ⟨opt₁,gap₁⟩ := private_gap C j a y ha.2 hy hpy
  refine ⟨twoAtom a x,twoAtom a y,⟨i,opt₀⟩,⟨j,opt₁⟩,?_⟩
  intro ε A dp n
  let F : Set (Set X) := {C i}
  have test := spiked_testing dp (PMF.pure ()) a (fun _ => x) (fun _ => y) F n
  rw [language_event,language_event] at test
  have h₀ := idErr_ge_gap C (twoAtom a x) A n (C ⁻¹' Fᶜ) (1/4)
    (fun k hk => gap₀ k hk)
  have h₁ := idErr_ge_gap C (twoAtom a y) A n (C ⁻¹' F) (1/4)
    (fun k (hk : C k = C i) => gap₁ k (hk ▸ diff))
  change commonRate ε ^ n ≤ probability ((samples (twoAtom a x) n).bind A) (C ⁻¹' Fᶜ)
    + probability ((samples (twoAtom a y) n).bind A) (C ⁻¹' F) at test
  linarith [le_max_left (idErr C A (twoAtom a x) n) (idErr C A (twoAtom a y) n),
    le_max_right (idErr C A (twoAtom a x) n) (idErr C A (twoAtom a y) n)]

end
end GenLimit.PriceOfPrivacy
