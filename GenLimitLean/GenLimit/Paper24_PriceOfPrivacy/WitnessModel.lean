import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model
import GenLimit.Support.EnumerationProgress

/-! The witness levels in Section 4 are prefixes of a public enumeration
of the word universe. The source's first word has Lean index zero. -/

namespace GenLimit.PriceOfPrivacy

open DiscreteIID Set Filter
open scoped ENNReal Topology Classical
noncomputable section

/-- All languages containing any unsupported word already have one among
the first W words of the public enumeration. -/
def WitnessBy (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (p : PMF X) (W : ℕ) : Prop :=
  ∀ i, ¬ C i ⊆ p.support → ∃ t < W, u t ∈ C i ∧ u t ∉ p.support

/-- Assumption 4.1. One finite witness level suffices for all bad languages,
and some language is wholly supported. -/
def GenerationAssumptions (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (p : PMF X) : Prop :=
  (∃ W, WitnessBy u C p W) ∧ ∃ i, C i ⊆ p.support

theorem finite_witness (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (p : PMF X)
    (finite : (range C).Finite) : ∃ W, WitnessBy u C p W := by
  classical
  let word (L : Set X) := if bad : ¬ L ⊆ p.support then u.symm (Set.not_subset.mp bad).choose else 0
  refine ⟨finite.toFinset.sup word + 1, ?_⟩
  intro i bad
  have w := Set.not_subset.mp bad
  refine ⟨word (C i),Nat.lt_succ_of_le (Finset.le_sup (f := word) (finite.mem_toFinset.mpr (Set.mem_range_self i))),?_⟩
  simpa only [word,dif_pos bad,Equiv.apply_symm_apply] using w.choose_spec

/-- A finite head of a discrete distribution leaves arbitrarily little mass
outside. -/
theorem finite_head (p : PMF X) {η : ℝ} (pos : 0 < η) :
    ∃ T : Finset X, probability p (↑T : Set X)ᶜ < η := by
  have hs := (ENNReal.summable_toReal (p.tsum_coe ▸ ENNReal.one_ne_top)).hasSum
  have total : (∑' x, (p x).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x),p.tsum_coe,ENNReal.toReal_one]
  rw [total] at hs
  obtain ⟨T,hT⟩ := (hs.eventually (Ioi_mem_nhds (by linarith : 1-η < 1))).exists
  refine ⟨T,?_⟩
  rw [probability_compl,probability,PMF.toOuterMeasure_apply_finset,
    ENNReal.toReal_sum (fun x _ => p.apply_ne_top x)]
  change 1-η < ∑ x ∈ T, (p x).toReal at hT
  linarith

/-- Redirect the unobserved tail of L bijectively onto L'. The alternative
distribution induced by this map keeps all head observations unchanged. -/
theorem redirect_tail [Countable X] (L L' : Set X) (hL : L.Infinite)
    (hL' : L'.Infinite) (T : Finset X) :
    ∃ g : X → X, (∀ x ∈ T, g x = x) ∧ g '' L = (L ∩ (T : Set X)) ∪ L' := by
  classical
  have tail := hL.diff T.finite_toSet
  let e := (Support.infiniteSetEquiv _ tail).symm.trans (Support.infiniteSetEquiv _ hL')
  let g (x : X) := if hx : x ∈ L \ (T : Set X) then (e ⟨x,hx⟩).val else x
  have same (x) (hx : x ∈ T) : g x = x := dif_neg (fun h => h.2 hx)
  refine ⟨g,same,Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    by_cases ht : x ∈ T
    · rw [same x ht]
      exact Or.inl ⟨hx,ht⟩
    · have h : x ∈ L \ (T : Set X) := ⟨hx,ht⟩
      exact Or.inr (by simpa only [g,dif_pos h] using (e ⟨x,h⟩).property)
  · rintro x (hx | hx)
    · exact ⟨x,hx.1,same x hx.2⟩
    · let y := e.symm ⟨x,hx⟩
      refine ⟨y.val,y.property.1,?_⟩
      rw [show g y.val = (e y).val from dif_pos y.property]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)

end
end GenLimit.PriceOfPrivacy
