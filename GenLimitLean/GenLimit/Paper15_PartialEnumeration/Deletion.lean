import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.Finite
import GenLimit.Paper15_PartialEnumeration.FullTextIdentification

/-! # Partial-text identification and finite deletion

Definition 4.3 requires eventual sandwiching of the entire enumerated set
between the hypothesis and the true language. Theorem 4.13 follows directly
in this model by simulating a learner on a text with the deleted symbols
replaced, then restoring exactly the deleted symbols observed so far. -/
namespace GenLimit.KleinbergWei.PartialEnumeration
open Filter

def IdentifiesPartial (A : List ℕ → Language) (X : Set Language) : Prop :=
  ∀ K ∈ X, ∀ (E : Language) (s : ℕ → ℕ), E.Infinite → E ⊆ K → Presents s E →
    ∀ᶠ n : ℕ in atTop, E ⊆ A (textPrefix s n) ∧ A (textPrefix s n) ⊆ K

def PartialIdentifiable (X : Set Language) := ∃ A, IdentifiesPartial A X

def deleteWords (W : Finset ℕ) (X : Set Language) : Set Language :=
  (fun K ↦ K \ (↑W : Set ℕ)) '' X

private noncomputable def anchor (W : Finset ℕ) (xs : List ℕ) : ℕ :=
  if h : ∃ x, x ∈ xs ∧ x ∉ W then Nat.find h else 0

private noncomputable def restoreLearner (A : List ℕ → Language) (W : Finset ℕ)
    (xs : List ℕ) : Language :=
  A (xs.map (fun x ↦ if x ∈ W then anchor W xs else x)) ∪
    {x | x ∈ W ∧ x ∈ xs}

private theorem eventually_seen {s : ℕ → ℕ} {E : Language} (hp : Presents s E)
    {x : ℕ} (hx : x ∈ E) : ∀ᶠ n : ℕ in atTop, x ∈ textPrefix s n := by
  obtain ⟨i,hi⟩ := (show x ∈ Set.range s from hp.symm ▸ hx)
  exact (eventually_ge_atTop (i+1)).mono (fun n hn ↦ mem_textPrefix_iff.mpr ⟨i,by omega,hi⟩)

/-- Theorem 4.13 / 1.11 for the arbitrary language-valued hypotheses of
Definition 4.3. Taking the image of a class automatically eliminates duplicates. -/
theorem theorem_4_13 (X : Set Language) (W : Finset ℕ) :
    PartialIdentifiable X ↔ PartialIdentifiable (deleteWords W X) := by
  classical
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨fun xs ↦ A xs \ (↑W : Set ℕ),?_⟩
    rintro _ ⟨K,hK,rfl⟩ E s hi hs hp
    filter_upwards [hA K hK E s hi (hs.trans Set.diff_subset) hp] with n hn
    exact ⟨fun x hx ↦ ⟨hn.1 hx,(hs hx).2⟩,fun x hx ↦ ⟨hn.2 hx.1,hx.2⟩⟩
  · rintro ⟨A,hA⟩
    refine ⟨restoreLearner A W,?_⟩
    intro K hK E s hi hs hp
    let D := E \ (↑W : Set ℕ)
    have hd : D.Infinite := hi.diff W.finite_toSet
    have ex := hd.nonempty
    let a := Nat.find ex
    have ha : a ∈ D := Nat.find_spec ex
    have smem (n : ℕ) : s n ∈ E := hp ▸ Set.mem_range_self n
    let f (x : ℕ) := if x ∈ W then a else x
    let d := f ∘ s
    have hpd : Presents d D := by
      ext x
      constructor
      · rintro ⟨n,rfl⟩
        by_cases h : s n ∈ W
        · simpa [d,f,h] using ha
        · simpa [d,f,h] using (show s n ∈ D from ⟨smem n,h⟩)
      · intro hx
        obtain ⟨n,he⟩ := (show x ∈ Set.range s from hp.symm ▸ hx.1)
        have hxW : x ∉ W := hx.2
        exact ⟨n,by simp [d,f,he,hxW]⟩
    have hk' : K \ (↑W : Set ℕ) ∈ deleteWords W X := ⟨K,hK,rfl⟩
    have hb := hA _ hk' D d hd (fun x hx ↦ ⟨hs hx.1,hx.2⟩) hpd
    have hab : ∀ᶠ n : ℕ in atTop, anchor W (textPrefix s n) = a := by
      filter_upwards [eventually_seen hp ha.1] with n hn
      have hex : ∃ x, x ∈ textPrefix s n ∧ x ∉ W := ⟨a,hn,ha.2⟩
      rw [anchor,dif_pos hex]
      apply le_antisymm (Nat.find_min' hex ⟨hn,ha.2⟩)
      obtain ⟨j,_,hj⟩ := mem_textPrefix_iff.mp (Nat.find_spec hex).1
      exact Nat.find_min' ex ⟨hj ▸ smem j,(Nat.find_spec hex).2⟩
    let V := W.filter (· ∈ E)
    have seen : ∀ᶠ n : ℕ in atTop, ∀ x ∈ V, x ∈ textPrefix s n :=
      (V.eventually_all).2 (fun x hx ↦ eventually_seen hp (Finset.mem_filter.mp hx).2)
    filter_upwards [hb,hab,seen] with n hn he hseen
    have hm : (textPrefix s n).map (fun x ↦ if x ∈ W then anchor W (textPrefix s n) else x) =
        textPrefix d n := by rw [he]; simp [textPrefix,List.map_map,d,f]
    unfold restoreLearner
    rw [hm]
    constructor
    · intro x hx
      by_cases hw : x ∈ W
      · exact Or.inr ⟨hw,hseen _ (Finset.mem_filter.mpr ⟨hw,hx⟩)⟩
      · exact Or.inl (hn.1 ⟨hx,hw⟩)
    · rintro x (hx | ⟨_,hx⟩)
      · exact (hn.2 hx).1
      · obtain ⟨j,_,rfl⟩ := mem_textPrefix_iff.mp hx
        exact hs (smem j)

end GenLimit.KleinbergWei.PartialEnumeration
