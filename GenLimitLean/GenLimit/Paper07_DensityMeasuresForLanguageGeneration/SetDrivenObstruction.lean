import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.SetDrivenTexts
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.SetIndex
import GenLimit.Support.KleinbergWei.CantorBendixson
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.FiniteHistory

/-! # Counterexamples when only the unordered finite sample is supplied

The fixed family contains the whole universe and the squares with a finite
initial segment adjoined. Every proper layer has upper density zero. On a
suitable exact text of the whole universe a valid set-driven index rule
eventually names only zero-density languages. A valid set-driven element
generator eventually emits only squares. These conclusions hold even if
element validity requires freshness only against the input.
-/
namespace GenLimit.KleinbergWei.DensityMeasures.SetDriven
open Filter SquareTower TowerTopology

/-- Round count equals the number of observations received. A value at zero
observations plays no role in eventual correctness or density. -/
def ValidElementOnInjective (C : LanguageFamily) (A : Finset ℕ → ℕ) : Prop :=
  ∀ z s, Function.Injective s → Presents s (C z) → ∀ᶠ t in atTop, A (sample s t) ∈ C z \ (sample s t : Set ℕ)

def ValidIndexOnInjective (C : LanguageFamily) (A : Finset ℕ → ℕ) : Prop :=
  ∀ z s, Function.Injective s → Presents s (C z) → ∀ᶠ t in atTop, C (A (sample s t)) ⊆ C z

def output (A : Finset ℕ → ℕ) (s : ℕ → ℕ) (t : ℕ) := A (sample s (t+1))

private theorem layer_infinite (n : ℕ) : (layer n).Infinite :=
  squares_infinite.mono Set.subset_union_left

private theorem layer_zero (n : ℕ) : natOrder.upperDensity (layer n) = 0 := by
  apply le_antisymm _ (natOrder.upperDensity_nonneg _)
  have h := natOrder.upperDensity_union_le squares (Finset.range n : Set ℕ)
  simpa only [layer,squares_upperDensity,natOrder.upperDensity_eq_zero_of_finite (Finset.range n).finite_toSet,add_zero] using h

noncomputable def orders : ℕ → OrderedLanguage
  | 0 => natOrder
  | n+1 => OrderedLanguage.increasing (layer n) (layer_infinite n)

theorem orders_carrier (i : ℕ) : (orders i).carrier = sparseFamily i := by cases i <;> rfl

theorem orders_compatible : OrderedFocus.Compatible orders := by
  have inc (i : ℕ) : StrictMono (orders i).enumeration := by
    cases i with
    | zero => exact strictMono_id
    | succ n => exact OrderedLanguage.increasing_strictMono (layer _) (layer_infinite _)
  intro i j a b c d he hf hab
  exact (inc j).lt_iff_lt.mp (he ▸ hf ▸ (inc i hab))

/-- Every layer is isolated by the finite initial segment that it contains.
Only the full universe can survive the first derivative. -/
theorem rank_two : FiniteRankAtMost (Set.range sparseFamily) 2 := by
  have base (p : Point (Set.range sparseFamily)) : squares ⊆ p.val := by
    obtain ⟨i,he⟩ := p.property
    rw [← he]
    cases i with
    | zero => exact Set.subset_univ _
    | succ n => exact Set.subset_union_left
  have onlyFull (p : Point (Set.range sparseFamily))
      (hp : p ∈ cbDerivative (Set.range sparseFamily) 1) : p.val = Set.univ := by
    obtain ⟨i,he⟩ := p.property
    cases i with
    | zero => exact he.symm
    | succ n =>
      have eq : layer n = p.val := he
      have inc : (Finset.range n : Set ℕ) ⊆ p.val := eq ▸ Set.subset_union_right
      obtain ⟨q,_,hne,hsub⟩ := hp.2 (Finset.range n) inc
      apply False.elim (hne (Subtype.ext (Set.Subset.antisymm hsub.2 ?_)))
      rw [← eq]
      exact Set.union_subset (base q) hsub.1
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨q,hq,hne,_⟩ := hp.2 ∅ (by simp)
  exact hne (Subtype.ext ((onlyFull q hq).trans (onlyFull p hp.1).symm))

/-- Under the set-only reading, neither infinitely frequent accuracy nor
limsup-one index density is possible on every text. -/
theorem index_counterexample (A : Finset ℕ → ℕ) (hv : ValidIndexOnInjective sparseFamily A) :
    ∃ s, Function.Injective s ∧ Presents s Set.univ ∧
      (∀ᶠ t in atTop, sparseFamily (output A s t) ≠ Set.univ) ∧
      limsup (fun t ↦ natOrder.upperDensity (sparseFamily (output A s t))) atTop = 0 := by
  obtain ⟨s,hinj,hs,hd⟩ := injective_diagonal (Q := fun S ↦ natOrder.upperDensity (sparseFamily (A S)) = 0) (by
    intro n s inj hs
    filter_upwards [hv (n+1) s inj hs] with t ht
    exact le_antisymm ((natOrder.upperDensity_mono ht).trans_eq (layer_zero n)) (natOrder.upperDensity_nonneg _))
  have zero : ∀ᶠ t in atTop, natOrder.upperDensity (sparseFamily (output A s t)) = 0 :=
    (tendsto_add_atTop_nat 1).eventually hd
  refine ⟨s,hinj,hs,?_,(tendsto_const_nhds.congr' (zero.mono (fun _ h ↦ h.symm))).limsup_eq⟩
  filter_upwards [zero] with t ht
  intro he
  rw [show sparseFamily (output A s t) = natOrder.carrier from he,natOrder.upperDensity_carrier] at ht
  norm_num at ht

private theorem zero_of_eventually_square (g : ℕ → ℕ) (hg : ∀ᶠ t in atTop, g t ∈ squares) :
    natOrder.upperDensity (Set.range g) = 0 := by
  classical
  obtain ⟨T,hT⟩ := eventually_atTop.mp hg
  let F := (Finset.range T).image g
  have sub : Set.range g ⊆ squares ∪ (F : Set ℕ) := by
    rintro _ ⟨t,rfl⟩
    by_cases h : t < T
    · exact Or.inr (Finset.mem_image.mpr ⟨t,Finset.mem_range.mpr h,rfl⟩)
    · exact Or.inl (hT t (Nat.le_of_not_gt h))
  apply le_antisymm ((natOrder.upperDensity_mono sub).trans ?_) (natOrder.upperDensity_nonneg _)
  simpa [squares_upperDensity,natOrder.upperDensity_eq_zero_of_finite F.finite_toSet]
    using natOrder.upperDensity_union_le squares (F : Set ℕ)

/-- All positive upper- and lower-density guarantees fail for a pure
function of the finite set, already on this rank-at-most-two collection. -/
theorem element_counterexample (A : Finset ℕ → ℕ) (hv : ValidElementOnInjective sparseFamily A) :
    ∃ s, Function.Injective s ∧ Presents s Set.univ ∧
      natOrder.upperDensity (Set.range (output A s)) = 0 ∧
      natOrder.lowerDensity (Set.range (output A s)) = 0 := by
  obtain ⟨s,hinj,hs,hd⟩ := injective_diagonal (Q := fun S ↦ A S ∈ squares) (by
    intro n s inj hs
    have hF : ∀ᶠ t in atTop, Finset.range n ⊆ sample s t := eventually_atTop.mpr
      (TowerTopology.finite_eventually_subset_sample hs (Finset.range n) Set.subset_union_right)
    filter_upwards [hv (n+1) s inj hs,hF] with t ht hsub
    exact (show A (sample s t) ∈ squares ∪ (Finset.range n : Set ℕ) from ht.1).resolve_right
      (fun hm ↦ ht.2 (hsub hm)))
  have hu := zero_of_eventually_square (output A s) ((tendsto_add_atTop_nat 1).eventually hd)
  refine ⟨s,hinj,hs,hu,le_antisymm ((?_ : natOrder.lowerDensity _ ≤ natOrder.upperDensity _).trans_eq hu)
    (natOrder.lowerDensity_nonneg _)⟩
  exact liminf_le_limsup (isBoundedUnder_of ⟨1,natOrder.prefixRatio_le_one _⟩)
    (isBoundedUnder_of ⟨0,natOrder.prefixRatio_nonneg _⟩)

end GenLimit.KleinbergWei.DensityMeasures.SetDriven
