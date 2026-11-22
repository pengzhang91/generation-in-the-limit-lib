import GenLimit.Paper00_LanguageIdentification.Effective.PrimitiveObstruction
import Mathlib.Logic.Function.Basic

/-! # Admissible targets in Gold's two text obstructions

Gold's proof treats lack of a name as failure of identification. With a
universal quantifier over total exact texts alone, a target without an
admissible presentation imposes no obligation. Both readings are explicit.
-/

namespace GenLimit.Gold.Effective

open Nat.Partrec (Code)

/-- A nonempty range of a partial recursive program admits a primitive
recursive text. Pair the input with the time bound and use a fixed member
when the bounded evaluation has no output. -/
theorem primitive_text_of_generator {c : Code} {L : Language}
    (hc : Generator c L) (he : L.Nonempty) :
    ∃ s, Primrec s ∧ Presents s L := by
  obtain ⟨a,ha⟩ := he
  let f (n : ℕ) := (Code.evaln n.unpair.2 c n.unpair.1).getD a
  refine ⟨f, Primrec.option_getD.comp (Code.primrec_evaln.comp
    (((Primrec.snd.comp Primrec.unpair).pair (Primrec.const c)).pair
      (Primrec.fst.comp Primrec.unpair))) (Primrec.const a), ?_⟩
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    cases hh : Code.evaln n.unpair.2 c n.unpair.1 with
    | none => simpa [f, hh] using ha
    | some y =>
      simpa [f, hh] using (hc y).mpr ⟨_, Code.evaln_sound hh⟩
  · intro hx
    obtain ⟨u,hu⟩ := (hc x).mp hx
    obtain ⟨t,ht⟩ := Code.evaln_complete.mp hu
    change Code.evaln t c u = some x at ht
    exact ⟨Nat.pair u t, by simp [f, ht]⟩

theorem generator_of_tester {L : Language} {e : Code} (he : Tester e L) : ∃ c, Generator c L := by
  obtain ⟨k,_,hk⟩ := tester_to_generator
  exact ⟨_, hk e L he⟩

theorem tester_of_recursive {L : Language} (hl : L ∈ recursiveLanguages) : ∃ e, Tester e L := by
  obtain ⟨e, he⟩ := Code.exists_code.mp (Partrec.nat_iff.mp (show Computable (bit L) from hl))
  exact ⟨e, fun x => ⟨fun hx => by simp [he, bit, hx], fun hx => by simp [he, bit, hx]⟩⟩

def Named (names : NameRelation N) (C : Set Language) : Prop := ∀ L ∈ C, ∃ n, names n L

/-- I.8. Superfinite classes cannot be both generator-named and effectively
identified from recursive text. -/
theorem superfinite_generator_recursive_text {C : Set Language} (hs : Text.IsSuperfinite C) :
    ¬ (Named Generator C ∧ Identifiable Generator recursiveText C) := by
  rintro ⟨names, learns⟩
  obtain ⟨finite,L,hl,hinf⟩ := hs
  obtain ⟨c,hc⟩ := names L hl
  obtain ⟨s, hprim, hp⟩ := primitive_text_of_generator hc hinf.nonempty
  exact no_generator_recursive_text finite hl hinf hprim.to_comp hp learns

/-- I.9. Superfinite classes cannot be both tester-named and effectively
identified from primitive recursive text. -/
theorem superfinite_tester_primitive_text {C : Set Language} (hs : Text.IsSuperfinite C) :
    ¬ (Named Tester C ∧ Identifiable Tester primitiveRecursiveText C) := by
  rintro ⟨names, learns⟩
  obtain ⟨finite,L,hl,hinf⟩ := hs
  obtain ⟨e,he⟩ := names L hl
  obtain ⟨c,hc⟩ := generator_of_tester he
  obtain ⟨s, hprim, hp⟩ := primitive_text_of_generator hc hinf.nonempty
  exact PrimitiveDiagonal.obstruction finite hl hinf hprim hp learns

/-- Under the presentation-only convention an infinite language having no
recursive text may be adjoined to the finite languages. This exhibits the
vacuous-presentations boundary in the unrestricted readings of I.8 and I.9. -/
theorem superfinite_unpresentable_counterexample :
    ∃ C, Text.IsSuperfinite C ∧ Identifiable Generator recursiveText C ∧
      Identifiable Tester primitiveRecursiveText C := by
  classical
  let R : Set Language := Set.range '' {s : ℕ → ℕ | Computable s}
  have hR : R.Countable := computable_streams_countable.image _
  have small := hR.union (Set.Countable.setOf_finite (α := ℕ))
  obtain ⟨L,hl⟩ : ∃ L, L ∉ R ∪ Text.finiteLanguages := by
    by_contra! h
    haveI : Countable Language := Set.countable_univ_iff.mp (small.mono fun L _ => h L)
    obtain ⟨e, he⟩ := exists_surjective_nat Language
    exact Function.cantor_surjective e he
  let C := insert L Text.finiteLanguages
  have hinf : L.Infinite := fun hf => hl (Or.inr hf)
  have noText {s : ℕ → ℕ} (hc : Computable s) (hp : Presents s L) : False :=
    hl (Or.inl ⟨s,hc,hp⟩)
  have restrict {s : ℕ → ℕ} {A : Language} (hA : A ∈ C) (hc : Computable s)
      (hp : Presents s A) : A ∈ Text.finiteLanguages := by
    rcases hA with rfl | h
    · exact (noText hc hp).elim
    · exact h
  obtain ⟨M,hM,hm⟩ := finite_tester_identification
  refine ⟨C, ⟨Set.subset_insert .., L, Set.mem_insert .., hinf⟩, generator_identification_of_tester
    ⟨M,hM,fun A hA s hs => hm A (restrict hA hs.1 hs.2) s hs.2⟩,
    ⟨M,hM,fun A hA s hs => hm A (restrict hA hs.1.to_comp hs.2) s hs.2⟩⟩

end GenLimit.Gold.Effective
