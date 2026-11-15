import GenLimit.NoRegretLanguageGeneration.CountableGeneration
import GenLimit.NoRegretLanguageGeneration.PairedPoints

namespace PredictionToGeneration
open Classical

/-- Classical VC shattering of an arbitrary finite set of examples. -/
def VCShatters (H : HypothesisClass X) (s : Finset X) : Prop :=
  ∀ labeling : X → Bool,∃ h,H h ∧ ∀ x∈s,h x=labeling x

/-- Supremum of cardinalities of VC-shattered finite sets. The examples below
prove boundedness explicitly before using this natural-valued supremum. -/
noncomputable def VCDimension (H : HypothesisClass X) : Nat :=
  sSup {n | ∃ s : Finset X,VCShatters H s ∧ s.card=n}

theorem vc_card_le_one_of_no_pair (H : HypothesisClass X)
    (hpair : ∀ x y,x≠y → ¬(∀ a b : Bool,∃ h,H h ∧ h x=a ∧ h y=b))
    (s : Finset X) (hs : VCShatters H s) : s.card≤1 := by
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1<s.card by omega)
  apply hpair x y hxy
  intro a b
  obtain ⟨h,hh,hl⟩ := hs (fun z => if z=x then a else b)
  exact ⟨h,hh,by simpa using hl x hx,by simpa [Ne.symm hxy] using hl y hy⟩

theorem vc_dimension_one (H : HypothesisClass X)
    (hsingle : ∃ x,(∃ h,H h ∧ h x=true) ∧ (∃ h,H h ∧ h x=false))
    (hpair : ∀ x y,x≠y → ¬(∀ a b : Bool,∃ h,H h ∧ h x=a ∧ h y=b)) :
    VCDimension H=1 := by
  obtain ⟨x,htrue,hfalse⟩ := hsingle
  have hs : VCShatters H {x} := by
    intro f
    cases hf : f x with
    | false =>
      obtain ⟨h,hh,hx⟩ := hfalse
      exact ⟨h,hh,by intro y hy; have he : y=x := Finset.mem_singleton.mp hy; subst y; exact hx.trans hf.symm⟩
    | true =>
      obtain ⟨h,hh,hx⟩ := htrue
      exact ⟨h,hh,by intro y hy; have he : y=x := Finset.mem_singleton.mp hy; subst y; exact hx.trans hf.symm⟩
  have hone : (1 : Nat)∈{n | ∃ s : Finset X,VCShatters H s ∧ s.card=n} := ⟨{x},hs,by simp⟩
  have hupper : ∀ n∈{n | ∃ s : Finset X,VCShatters H s ∧ s.card=n},n≤1 := by
    rintro n ⟨s,hs,rfl⟩
    exact vc_card_le_one_of_no_pair H hpair s hs
  have hb : BddAbove {n | ∃ s : Finset X,VCShatters H s ∧ s.card=n} := ⟨1,hupper⟩
  exact Nat.le_antisymm (csSup_le ⟨1,hone⟩ hupper) (le_csSup hb hone)

namespace VCCounterexample

theorem vc_dimension_eq_one : VCDimension H=1 := vc_dimension_one H vc_one.1 vc_one.2

instance countable_hypotheses : Countable {h // H h} := by
  obtain ⟨code,hi⟩ := countable_class
  exact Function.Injective.countable hi

end VCCounterexample

namespace Cofinite

instance countable_hypotheses : Countable {h // H h} := by
  obtain ⟨code,hi⟩ := countable_class
  exact Function.Injective.countable hi

end Cofinite

namespace PairedPoints

instance countable_hypotheses : Countable {h // H h} := by
  obtain ⟨code,hi⟩ := countable_class
  exact Function.Injective.countable hi

end PairedPoints
end PredictionToGeneration

