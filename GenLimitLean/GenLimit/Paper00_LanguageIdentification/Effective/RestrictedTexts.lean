import GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration
import GenLimit.Paper00_LanguageIdentification.Effective.Finite

/-! # Ineffective identification from recursive and primitive recursive texts (§8) -/

namespace GenLimit.Gold.Effective

open Nat.Partrec (Code)

def recursiveText : Method ℕ := fun L => {s | Computable s ∧ Presents s L}
def primitiveRecursiveText : Method ℕ := fun L => {s | Primrec s ∧ Presents s L}

/-- A code for a total recursive function determines all of its values. -/
theorem computable_streams_countable : {s : ℕ → ℕ | Computable s}.Countable := by
  classical
  let F := {s : ℕ → ℕ // Computable s}
  have hasCode (s : F) : ∃ c : Code, ∀ x, c.eval x = Part.some (s.val x) := by
    obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp s.property)
    exact ⟨c, fun x => congrFun hc x⟩
  let code (s : F) := (hasCode s).choose
  have inj : Function.Injective code := by
    intro a b h
    apply Subtype.ext
    funext x
    have eq := congrArg (fun c : Code => c.eval x) h
    change (code a).eval x = (code b).eval x at eq
    rw [(hasCode a).choose_spec, (hasCode b).choose_spec] at eq
    simpa using eq
  exact (inj.countable : Countable F)

/-- Every named countable class is semantically identifiable using recursive
texts. The learner may use a noneffective enumeration of the allowable streams. -/
theorem recursive_text_identification {N : Type*} [Nonempty N]
    (names : NameRelation N) (C : Set Language) (hc : C.Countable)
    (hn : ∀ L ∈ C, ∃ n, names n L) :
    ∃ M, Learns M names recursiveText C := by
  classical
  by_cases he : C.Nonempty
  · letI : Countable C := hc.to_subtype
    letI : Nonempty C := he.to_subtype
    let naming : Abstract.Naming C C := ⟨id, id, fun _ => rfl⟩
    let allowed : Abstract.Allowable ℕ C := fun L => recursiveText L.val
    have hcount (L : C) : (allowed L).Countable :=
      computable_streams_countable.mono (fun _ h => h.1)
    have hd : Abstract.Distinguishable allowed := by
      intro A B s ha hb
      exact Subtype.ext (ha.2.symm.trans hb.2)
    obtain ⟨M, hM⟩ := Abstract.distinguishable_implies_identifiable_of_countable naming hcount hd
    let name (L : C) := (hn L.val L.property).choose
    refine ⟨fun h => name (M h), fun L hL s hs => ?_⟩
    obtain ⟨i, hi, T, hT⟩ := hM ⟨L,hL⟩ s hs
    change i = ⟨L, hL⟩ at hi
    subst i
    exact ⟨_, (hn L hL).choose_spec, T, fun t ht => congrArg name (hT t ht)⟩
  · exact ⟨fun _ => Classical.arbitrary N, fun L hL => (he ⟨L, hL⟩).elim⟩

theorem primitive_recursive_text_identification {N : Type*} [Nonempty N]
    (names : NameRelation N) (C : Set Language) (hc : C.Countable)
    (hn : ∀ L ∈ C, ∃ n, names n L) :
    ∃ M, Learns M names primitiveRecursiveText C := by
  obtain ⟨M, hm⟩ := recursive_text_identification names C hc hn
  exact ⟨M, fun L hL s hs => hm L hL s ⟨hs.1.to_comp, hs.2⟩⟩

/-- Both restricted-text conclusions of §8. -/
theorem section_8_restricted_texts {N : Type*} [Nonempty N] (names : NameRelation N)
    (C : Set Language) (hc : C.Countable) (hn : ∀ L ∈ C, ∃ n, names n L) :
    (∃ M, Learns M names recursiveText C) ∧ (∃ M, Learns M names primitiveRecursiveText C) :=
  ⟨recursive_text_identification names C hc hn, primitive_recursive_text_identification names C hc hn⟩

end GenLimit.Gold.Effective
