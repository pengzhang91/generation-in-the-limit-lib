import GenLimit.NoRegretLanguageGeneration.SharpnessProduct
import GenLimit.NoRegretLanguageGeneration.FiniteMinimax

namespace PredictionToGeneration.MarkedUnion
open Classical

abbrev Point (I : Type) (X : I → Type) := (i : I) × Option (X i)

def embed {I : Type} {X : I → Type} (i : I) (x : X i) : Point I X := ⟨i, some x⟩
def marker {I : Type} {X : I → Type} (i : I) : Point I X := ⟨i, none⟩

noncomputable def lift {I : Type} {X : I → Type} (i : I) (h : Hypothesis (X i)) :
    Hypothesis (Point I X) := fun y =>
  if he : y.1 = i then match he ▸ y.2 with | none => true | some x => h x else false

@[simp] theorem lift_embed {I : Type} {X : I → Type} (i : I) (h : Hypothesis (X i)) (x : X i) :
    lift i h (embed i x) = h x := by simp [lift, embed]

@[simp] theorem lift_marker {I : Type} {X : I → Type} (i : I) (h : Hypothesis (X i)) :
    lift i h (marker i) = true := by simp [lift, marker]

theorem lift_other {I : Type} {X : I → Type} (i : I) (h : Hypothesis (X i))
    (y : Point I X) (hy : y.1 ≠ i) : lift i h y = false := by simp [lift, hy]

noncomputable def Component {I : Type} {X : I → Type} (i : I) (C : HypothesisClass (X i)) :
    HypothesisClass (Point I X) := fun g => ∃ h, C h ∧ g = lift i h

noncomputable def Union {I : Type} {X : I → Type} (C : (i : I) → HypothesisClass (X i)) :
    HypothesisClass (Point I X) := fun g => ∃ i, Component i (C i) g

theorem restrict_component_embed {I : Type} {X : I → Type} (i : I)
    (C : HypothesisClass (X i)) (x : X i) (b : Bool) :
    restrict (Component i C) (embed i x) b = Component i (restrict C x b) := by
  funext g
  apply propext
  constructor
  · rintro ⟨⟨h, hh, rfl⟩, hb⟩
    exact ⟨h, ⟨hh, by simpa using hb⟩, rfl⟩
  · rintro ⟨h, ⟨hh, hb⟩, rfl⟩
    exact ⟨⟨h, hh, rfl⟩, by simpa using hb⟩

theorem component_shatters {I : Type} {X : I → Type} (i : I)
    (C : HypothesisClass (X i)) (n : Nat) :
    Shatters (Component i C) n ↔ Shatters C n := by
  induction n generalizing C with
  | zero =>
    constructor
    · rintro ⟨g, h, hh, _⟩; exact ⟨h, hh⟩
    · rintro ⟨h, hh⟩; exact ⟨lift i h, h, hh, rfl⟩
  | succ n ih =>
    constructor
    · rintro ⟨y, h0, h1⟩
      obtain ⟨g, hg, hg1⟩ := SharpnessProduct.shatters_le _ (Nat.zero_le n) h1
      obtain ⟨h, hh, rfl⟩ := hg
      have hy : y.1 = i := by
        by_contra hn
        rw [lift_other i h y hn] at hg1
        contradiction
      rcases y with ⟨j, y⟩
      dsimp at hy
      subst j
      cases y with
      | none =>
        obtain ⟨g, hg, hg0⟩ := SharpnessProduct.shatters_le _ (Nat.zero_le n) h0
        obtain ⟨h, hh, rfl⟩ := hg
        have : lift i h (marker i) = false := hg0
        simp at this
      | some x =>
        change Shatters (restrict (Component i C) (embed i x) false) n at h0
        change Shatters (restrict (Component i C) (embed i x) true) n at h1
        rw [restrict_component_embed] at h0 h1
        exact ⟨x, (ih _).mp h0, (ih _).mp h1⟩
    · rintro ⟨x, h0, h1⟩
      refine ⟨embed i x, ?_, ?_⟩
      · rw [restrict_component_embed]; exact (ih _).mpr h0
      · rw [restrict_component_embed]; exact (ih _).mpr h1

theorem union_ldim_upper {I : Type} {X : I → Type}
    (C : (i : I) → HypothesisClass (X i)) (d : Nat) (hC : ∀ i, LdimLE (C i) d) :
    LdimLE (Union C) (d + 1) := by
  rintro ⟨y, _, h1⟩
  have hs : Shatters (Component y.1 (C y.1)) (d + 1) := by
    apply shatters_mono (n := d + 1) (hs := h1)
    rintro g ⟨⟨i, h, hh, rfl⟩, hp⟩
    have hi : y.1 = i := by
      by_contra hn
      rw [lift_other i h y hn] at hp
      contradiction
    subst i
    exact ⟨h, hh, rfl⟩
  exact hC y.1 ((component_shatters y.1 (C y.1) (d + 1)).mp hs)

theorem union_shatters_succ {I : Type} {X : I → Type}
    (C : (i : I) → HypothesisClass (X i)) (i j : I) (hij : i ≠ j)
    (d : Nat) (hi : Shatters (C i) d) (hj : Shatters (C j) d) :
    Shatters (Union C) (d + 1) := by
  refine ⟨marker i, ?_, ?_⟩
  · apply shatters_mono (n := d) (hs := (component_shatters j (C j) d).mpr hj)
    rintro g ⟨h, hh, rfl⟩
    exact ⟨⟨j, h, hh, rfl⟩, lift_other j h (marker i) hij⟩
  · apply shatters_mono (n := d) (hs := (component_shatters i (C i) d).mpr hi)
    rintro g ⟨h, hh, rfl⟩
    exact ⟨⟨i, h, hh, rfl⟩, lift_marker i h⟩

end PredictionToGeneration.MarkedUnion

namespace PredictionToGeneration.MarkedUnion
open Classical

noncomputable def extract {I : Type} {X : I → Type} (i : I) (y : Point I X) : Option (X i) :=
  if he : y.1 = i then he ▸ y.2 else none

@[simp] theorem extract_embed {I : Type} {X : I → Type} (i : I) (x : X i) :
    extract i (embed i x) = some x := by simp [extract, embed]

theorem component_uus {I : Type} {X : I → Type} (i : I)
    (C : HypothesisClass (X i)) (hu : UUS C) : UUS (Component i C) := by
  rintro g ⟨h, hh, rfl⟩ seen
  obtain ⟨x, hx, hp⟩ := hu h hh (seen.filterMap (extract i))
  refine ⟨embed i x, ?_, by simpa using hp⟩
  intro hm
  apply hx
  exact List.mem_filterMap.mpr ⟨embed i x, hm, extract_embed i x⟩

theorem union_uus {I : Type} {X : I → Type}
    (C : (i : I) → HypothesisClass (X i)) (hu : ∀ i, UUS (C i)) : UUS (Union C) := by
  rintro g ⟨i, hi⟩ seen
  exact component_uus i (C i) (hu i) g hi seen

theorem union_countable {I : Type} {X : I → Type} [Countable I]
    (C : (i : I) → HypothesisClass (X i)) (hc : ∀ i, Countable {h // C i h}) :
    Countable {g // Union C g} := by
  letI : (i : I) → Countable {h // C i h} := hc
  let encode : {g // Union C g} → (i : I) × {h // C i h} := fun g =>
    ⟨Classical.choose g.2,
      ⟨Classical.choose (Classical.choose_spec g.2), (Classical.choose_spec (Classical.choose_spec g.2)).1⟩⟩
  let decode : ((i : I) × {h // C i h}) → Hypothesis (Point I X) := fun p => lift p.1 p.2.1
  have he : ∀ g : {g // Union C g}, decode (encode g) = g.1 := by
    intro g
    exact (Classical.choose_spec (Classical.choose_spec g.2)).2.symm
  apply Function.Injective.countable (f := encode)
  intro a b hab
  apply Subtype.ext
  exact (he a).symm.trans ((congrArg decode hab).trans (he b))

end PredictionToGeneration.MarkedUnion
